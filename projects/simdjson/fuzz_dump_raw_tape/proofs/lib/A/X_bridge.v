(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import CatSim ShapeAlg AsanAcct AsanAcctShape.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode RelSpec RzCPS NodesA NodesA_wv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Fixpoint TT {X : Type} (t : itree node (exc X)) (T : X -> TSet) : TSet :=
  match t with
  | Ret Unr => fun _ => False
  | Ret (Ok x) => T x
  | Vis n k =>
      match n with
      | NWritev fd bufs =>
          match concat bufs with
          | [] => TT (k (eff0 (Z_to_bv 64 0))) T
          | b :: bs => t_alt (fun i : wr_index (b :: bs) =>
                         t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (b :: bs)))
                                (TT (k (eff0 (Z_to_bv 64 (Z.of_nat (proj1_sig i))))) T))
          end
      | NIoctl fd req => TT (k (efferr ENOTTY)) T
      | _ => fun _ => False
      end
  | Cho _ => fun _ => False
  end.

Fixpoint tok {X : Type} (chans : list Z) (t : itree node (exc X)) : Prop :=
  match t with
  | Ret Unr => False
  | Ret (Ok _) => True
  | Vis n k =>
      match n with
      | NWritev fd bufs => In fd chans
          /\ (concat bufs = [] -> tok chans (k (eff0 (Z_to_bv 64 0))))
          /\ (forall i, (1 <= i <= length (concat bufs))%nat -> tok chans (k (eff0 (Z_to_bv 64 (Z.of_nat i)))))
      | NIoctl fd req => In fd chans /\ tok chans (k (efferr ENOTTY))
      | _ => False
      end
  | Cho _ => False
  end.

Lemma TT_conseq : forall {X} (t : itree node (exc X)) (T T' : X -> TSet), (forall x, t_eq (T x) (T' x)) ->
  t_eq (TT t T) (TT t T').
Proof.
  intros X t T T' HT. induction t as [[|x]|n k IH|kc IHc]; cbn [TT].
  - apply t_eq_refl.
  - apply HT.
  - destruct n; try (intros tr; tauto).
    + destruct (concat bufs) as [|b bs]; [apply IH|].
      intros tr. split; intros [i Hi]; exists i.
      * destruct Hi as [Hp|(tr' & -> & Ht)]; [left; exact Hp| right; exists tr'; split; [reflexivity| apply IH; exact Ht]].
      * destruct Hi as [Hp|(tr' & -> & Ht)]; [left; exact Hp| right; exists tr'; split; [reflexivity| apply IH; exact Ht]].
    + apply IH.
  - apply t_eq_refl.
Qed.

Lemma TT_ebind : forall {X Y} (t : itree node (exc X)) (f : X -> itree node (exc Y)) (T : Y -> TSet),
  TT (ebind t f) T = TT t (fun x => TT (f x) T).
Proof.
  intros X Y t f T. induction t as [[|x]|n k IH|kc IHc]; cbn [ebind bind TT]; [reflexivity| reflexivity| |reflexivity].
  destruct n; try reflexivity.
  - destruct (concat bufs) as [|b bs].
    + unfold ebind in IH. exact (IH _).
    + f_equal. apply FunctionalExtensionality.functional_extensionality. intros i. f_equal. unfold ebind in IH. apply IH.
  - unfold ebind in IH. apply IH.
Qed.

Lemma tok_ebind : forall {X Y} chans (t : itree node (exc X)) (f : X -> itree node (exc Y)),
  tok chans t -> (forall x, tok chans (f x)) -> tok chans (ebind t f).
Proof.
  intros X Y chans t f Ht Hf. induction t as [[|x]|n k IH|kc IHc]; cbn [ebind bind tok] in *; [contradiction| apply Hf| |contradiction].
  destruct n; try contradiction.
  - destruct Ht as (Hfd & H0 & H1). split; [exact Hfd|]. split.
    + intros E. apply IH. exact (H0 E).
    + intros i Hi. apply IH. exact (H1 i Hi).
  - destruct Ht as (Hfd & H). split; [exact Hfd|]. apply IH. exact H.
Qed.

Section Rules.
Variable segs : list Segment.
Variable segtop : Z.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_below_b segs segtop = true.

Lemma AST_unpack : forall A Pm PM c, AST segtop A Pm PM c -> exists ms, Pm ms /\ AST segtop A (eq ms) PM c.
Proof.
  intros A Pm PM [ms mo] (H1 & H2 & H3 & H4). exists (restrict (HID A mo) ms). split; [exact H2|].
  split; [exact H1|]. split; [reflexivity|]. split; [exact H3| exact H4].
Qed.

Theorem ast_writev0 : forall A Pm PM K KM fd bufs,
  concat bufs = [] -> mat_stable KM ->
  (forall ms, Pm ms -> at_node segs (NWritev fd bufs) ms /\ K (nretA ms (eff0 (Z_to_bv 64 0)))) ->
  (forall mo, PM mo -> fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) /\ KM mo) ->
  cps segs (AST segtop A Pm PM) (AST segtop A K KM).
Proof using Hwx Hsegs.
  intros A Pm PM K KM fd bufs Hnb HKM Hm HM. apply (ast_node1 segs segtop Hwx Hsegs); [exact HKM|].
  intros ms mo Hc. pose proof (AST_off segs segtop Hsegs A Pm PM _ Hc) as HH. pose proof Hc as (Hmc & HPm & HPM & _).
  cbn [cfg_ms cfg_model] in *.
  destruct (Hm _ HPm) as (Hat & HK). destruct (HM _ HPM) as (Hfdl & HKMm).
  destruct (writev_at_transfer segs _ ms fd bufs HH Hat) as [Hat' (iovs & Hiov & Hvisa & HF)].
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
  assert (Htotal : iovs_total iovs = 0).
  { rewrite (iovs_total_ok _ _ _ Hok), Hnb. reflexivity. }
  set (CA := import_iovecs_accesses (in_mem i) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))))).
  exists (Z_to_bv 64 66), (with_copyins CA (mkEffect (Z_to_bv 64 0) [] [])), mo.
  split; [exact Hsvc|]. split.
  { intros o. change (sys_input segs ms (Z_to_bv 64 66)) with i. rewrite Hsp. exact (writev_chan_zero_outcome _ _ _ i mo o (Z_to_bv 64 fd) iovs Hfdl Hw Himp Htotal). }
  split; [apply vm_same_refl|]. split; [apply io_eff_copyins, io_eff_mkEffect|].
  split.
  { unfold syscall_effect_accesses. cbn [eff_copyins eff_writes write_accesses with_copyins]. rewrite app_nil_r.
    subst CA. rewrite Hcnt32. rewrite <- (wa_unsigned_id (areg ms 11)). pose proof Hiov as (Hb0 & Hb1 & _).
    rewrite length_iovec_bytes in Hb1, Hvisa.
    apply import_iovecs_accesses_avoid; [lia| lia| lia|]. intros k Hk. apply Hvisa. lia. }
  split; [| exact HKMm]. rewrite nretA_copyins. exact HK.
Qed.

Theorem impl_realizes : forall {X : Type} (chans : list Z) (t : itree node (exc X)) A PM (Q : X -> machine_state -> Prop)
    (T : X -> TSet) ms c,
  mat_stable PM ->
  (forall mo fd, PM mo -> In fd chans -> fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd))) ->
  tok chans t -> AST segtop A (eq ms) PM c -> impl segs (at_node segs) t (epost Q) ms ->
  (forall x ms' c', Q x ms' -> AST segtop A (eq ms') PM c' -> realizes segs c' (T x)) ->
  realizes segs c (TT t T).
Proof using Hwx Hsegs.
  intros X chans t A PM Q T. induction t as [[|x]|n k IH|kc IHc]; intros ms c HPM HFD Htok Hc Him HK; cbn [tok] in Htok; [| | |contradiction].
  - contradiction.
  - cbn [impl epost] in Him. cbn [TT].
    apply (ast_evt segs segtop Hwx Hsegs A (eq ms) PM (Q x) HPM (fun ms0 E => eq_ind ms (fun z => evt segs (Q x) z) Him ms0 E) (T x) c Hc).
    intros c' Hc'. destruct (AST_unpack _ _ _ c' Hc') as (ms' & HQ & Hc''). exact (HK x ms' c' HQ Hc'').
  - cbn [impl] in Him.
    apply (ast_evt segs segtop Hwx Hsegs A (eq ms) PM _ HPM (fun ms0 E => eq_ind ms (fun z => evt segs _ z) Him ms0 E) _ c Hc).
    intros c1 Hc1. destruct (AST_unpack _ _ _ c1 Hc1) as (ms1 & (Hat & Hk) & Hc1').
    destruct n; try contradiction.
    +
      destruct Htok as (Hfd & Htok0 & Htok1). cbn [TT].
      destruct (concat bufs) as [|b bs] eqn:Eb.
      * apply (ast_writev0 A (eq ms1) PM (eq (nretA ms1 (eff0 (Z_to_bv 64 0)))) PM fd bufs Eb HPM); [| | exact Hc1'|].
        -- intros ms0 <-. split; [exact Hat| reflexivity].
        -- intros mo HPMmo. split; [| exact HPMmo]. exact (HFD mo fd HPMmo Hfd).
        -- intros c2 Hc2. apply (IH _ _ c2 HPM HFD (Htok0 eq_refl) Hc2 (Hk _) HK).
      * assert (W : wnode segs (AST segtop A (eq ms1) PM) (Z_to_bv 64 fd) (b :: bs)
                      (fun j => AST segtop A (eq (nretA ms1 (eff0 (Z_to_bv 64 (Z.of_nat j))))) PM)).
        { assert (Hnb : (1 <= length (concat bufs))%nat).
          { lazymatch type of Eb with ?cb = _ => change (1 <= length cb)%nat end. rewrite Eb. cbn. lia. }
          pose proof (ast_writev segs segtop Hwx Hsegs A (eq ms1) PM (fun j => eq (nretA ms1 (eff0 (Z_to_bv 64 (Z.of_nat j))))) PM
                        fd bufs Hnb HPM) as W0.
          rewrite <- Eb. apply W0.
          - intros ms0 <-. split; [exact Hat|]. intros j Hj. reflexivity.
          - intros mo HPMmo. split; [| exact HPMmo]. exact (HFD mo fd HPMmo Hfd). }
        apply (W (fun j => TT (k (eff0 (Z_to_bv 64 (Z.of_nat j)))) T) c1 Hc1').
        intros j c2 Hj Hc2. apply (IH _ _ c2 HPM HFD (Htok1 j ltac:(first [exact Hj| rewrite Eb; exact Hj])) Hc2 (Hk _) HK).
    +
      destruct Htok as (Hfd & Htok'). cbn [TT].
      pose proof Hat as (Hsvc & Hfd2 & Hreq & Ha0 & Ha1).
      apply (ast_ioctl segs segtop Hwx Hsegs A (eq ms1) PM (eq (nretA ms1 (efferr ENOTTY))) PM fd Hfd2 HPM); [| | exact Hc1'|].
      * intros ms0 <-. split; [exact Hsvc|]. split; [exact Ha0|]. split; [rewrite Ha1, Hreq; reflexivity| reflexivity].
      * intros mo HPMmo. split; [| exact HPMmo]. exists (Z_to_bv 64 fd). exact (HFD mo fd HPMmo Hfd).
      * intros c2 Hc2. apply (IH _ _ c2 HPM HFD Htok' Hc2 (Hk _) HK).
Qed.

End Rules.

