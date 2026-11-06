(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec ITree Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AcctCore ExecF ModelX MmXfer.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ITreeA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lf (mo : Model) : Model := with_vm_backing [] [] mo.

Lemma lf_MX : forall m mat, lf (MX m mat) = lf m. Proof. reflexivity. Qed.
Lemma m_fds_lf : forall m, m_fds (lf m) = m_fds m. Proof. reflexivity. Qed.
Lemma m_fs_lf : forall m, m_fs (lf m) = m_fs m. Proof. reflexivity. Qed.
Lemma m_halted_lf : forall m, m_halted (lf m) = m_halted m. Proof. reflexivity. Qed.
Lemma m_vmmaps_lf : forall m, m_vmmaps (lf m) = m_vmmaps m. Proof. reflexivity. Qed.
Lemma lf_with_fds : forall x m, lf (with_fds x m) = with_fds x (lf m). Proof. reflexivity. Qed.
Lemma lf_with_halted : forall x m, lf (with_halted x m) = with_halted x (lf m). Proof. reflexivity. Qed.
Lemma lf_with_vmmaps : forall h m, lf (with_vmmaps h m) = with_vmmaps h (lf m). Proof. reflexivity. Qed.

Section Defs.
Variable NMAX : nat.
(* [comment removed for export] *)
Variable SHM : list (Z * Z).

Definition sh_entry_ok (h : VmMaps) (e : Z * Z) : Prop :=
  0 <= fst e /\ 0 < snd e /\ fst e + snd e < 2^64 /\
  In (Z_to_bv 64 (fst e), Z_to_bv 64 (snd e)) (vm_maps h) /\
  region_free (vm_noaccess h) (Z_to_bv 64 (fst e)) (Z_to_bv 64 (snd e)) = true /\
  region_free (vm_reserved h) (Z_to_bv 64 (fst e)) (Z_to_bv 64 (snd e)) = true.

Definition shinv (mo : Model) : Prop := Forall (sh_entry_ok (m_vmmaps mo)) SHM.

Definition minvA (mo : Model) : Prop := minv (lf mo) /\ m_vm_materialized mo = [] /\ shinv mo.

#[using="Type"] Lemma minvA_minv : forall mo, minvA mo -> minv (lf mo).
Proof. intros mo [H _]; exact H. Qed.
#[using="Type"] Lemma minvA_canon : forall mo, minvA mo -> m_vm_materialized mo = [].
Proof. intros mo (_ & H & _); exact H. Qed.
#[using="Type"] Lemma minvA_shinv : forall mo, minvA mo -> shinv mo.
Proof. intros mo (_ & _ & H); exact H. Qed.

(* [comment removed for export] *)
Definition mmap_fixed_repl (flags addr n : word) (mo : Model) : Model :=
  with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) addr n) mo).
Definition mmap_fixed_span_repl (flags addr n : word) (mo : Model) : Model :=
  with_mmap_replacement flags addr n (with_vmmaps (mmap_fixed_rw_span_next (m_vmmaps mo) addr n) mo).

Definition nslack (n : node) (mo : Model) : Prop :=
  match n with
  | NBrk req =>
      robust NMAX (nonlazy_bytes mo + bv_unsigned (bv_sub (Z_to_bv 64 req) (vm_brk (m_vmmaps mo)))) (vm_limit (m_vmmaps mo))
  | NMmap addr len prot flags =>
      let nZ := page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) in
      (mmap_noreserve_b (Z_to_bv 64 flags) = true \/ robust NMAX (nonlazy_bytes mo + nZ) (vm_limit (m_vmmaps mo)))
      /\ robust NMAX (nonlazy_bytes (mmap_fixed_repl (Z_to_bv 64 flags) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) mo))
                (vm_limit (m_vmmaps mo))
      /\ robust NMAX (nonlazy_bytes (mmap_fixed_span_repl (Z_to_bv 64 flags) (Z_to_bv 64 addr) (Z_to_bv 64 nZ) mo))
                (vm_limit (m_vmmaps mo))
  | NMprotect addr len prot =>
      robust NMAX (nonlazy_bytes (mprotect_model_next mo (Z_to_bv 64 addr) (Z_to_bv 64 (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))))))
             (vm_limit (m_vmmaps mo))
  | _ => True
  end.

(* [comment removed for export] *)
Definition apart_sh (a l : Z) : Prop := Forall (fun e => a + l <= fst e \/ fst e + snd e <= a) SHM.

(* [comment removed for export] *)
Definition nshapart (n : node) : Prop :=
  match n with
  | NMunmap addr len => apart_sh (bv_unsigned (Z_to_bv 64 addr)) (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))
  | NMmap addr len _ _ =>
      bv_unsigned (Z_to_bv 64 addr) = 0 \/
      apart_sh (bv_unsigned (Z_to_bv 64 addr)) (page_round_up_Z (bv_unsigned (Z_to_bv 64 len)))
  | _ => True
  end.

Definition nsafeA (n : node) (mo : Model) : Prop := nsafe n mo /\ nslack n mo /\ nshapart n.

End Defs.

(* [comment removed for export] *)
Definition nstepA : node -> Model -> resp -> Model -> list event -> Prop := nstep.
Definition nexitA : node -> Model -> word -> Model -> Prop := nexit.

(* [comment removed for export] *)
Definition fstepA (n : node) (rsp : resp) (R R' : footprint) : Prop :=
  match n with
  | NMmap addr len prot flags =>
      fp_le R R' /\
      (prot = PROT_READ + PROT_WRITE ->
       bv_unsigned (eff_ret rsp) mod page_size = 0 ->
       rng R' (bv_unsigned (eff_ret rsp)) (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))))
  | NMunmap addr len =>
      forall b (j : nat), R b j ->
        (b + Z.of_nat j <= bv_unsigned (Z_to_bv 64 addr) \/
         bv_unsigned (Z_to_bv 64 addr) + page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) <= b) -> R' b j
  | NBrk _ | NMprotect _ _ _ => fp_le R R'
  | _ => R' = R
  end.

Lemma fstepA_id : forall n rsp R,
  match n with NMmap _ _ _ _ | NMunmap _ _ | NBrk _ | NMprotect _ _ _ => False | _ => True end ->
  fstepA n rsp R R.
Proof. intros n rsp R H; destruct n; try destruct H; reflexivity. Qed.

Lemma fstepA_rng : forall n rsp R R' lo len,
  match n with NMunmap _ _ => False | _ => True end ->
  fstepA n rsp R R' -> rng R lo len -> rng R' lo len.
Proof.
  intros n rsp R R' lo len Hn HF HR. destruct n; try destruct Hn; cbn in HF;
    try (subst R'; exact HR); try (eapply rng_fp_le; [| exact HR]); try exact HF. exact (proj1 HF).
Qed.

Lemma fstepA_munmap_rng : forall addr len rsp R R' lo l,
  fstepA (NMunmap addr len) rsp R R' -> rng R lo l ->
  (lo + l <= bv_unsigned (Z_to_bv 64 addr) \/
   bv_unsigned (Z_to_bv 64 addr) + page_round_up_Z (bv_unsigned (Z_to_bv 64 len)) <= lo) ->
  rng R' lo l.
Proof.
  intros addr len rsp R R' lo l HF (A & B & HR) HD. split; [exact A|]. split; [exact B|].
  intros b j Hb Hj. apply HF; [apply HR; assumption| lia].
Qed.

Lemma fstepA_mmap_grant : forall addr len flags rsp R R',
  fstepA (NMmap addr len (PROT_READ + PROT_WRITE) flags) rsp R R' ->
  bv_unsigned (eff_ret rsp) mod page_size = 0 ->
  rng R' (bv_unsigned (eff_ret rsp)) (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))).
Proof. intros addr len flags rsp R R' [_ H] Hal. apply H; [reflexivity| exact Hal]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AtNodeA.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition ncov (n : node) (RNG : footprint) (ms : machine_state) : Prop :=
  match n with
  | NWrite fd bs => rng RNG (bv_unsigned (areg ms 11)) (Z.of_nat (length bs))
  | NOpen path | NOpenW path _ | NUnlink path _ => rng RNG (bv_unsigned (areg ms 11)) (Z.of_nat (length path) + 1)
  | NRead fd buf count => rng RNG buf count
  | NReadv fd dsts =>
      rng RNG (bv_unsigned (areg ms 11)) (16 * Z.of_nat (length dsts)) /\ Forall (fun d => rng RNG (fst d) (snd d)) dsts
  | _ => True
  end.

(* [comment removed for export] *)
Definition at_gatherA (sysno : Z) (fdok : Z -> Prop) (lenok : Z -> Prop) (fd : Z) (bufs : list (list byte))
    (RNG : footprint) (ms : machine_state) : Prop :=
  ms_svc_pending ms = Some (Z_to_bv 64 sysno) /\
  fdok fd /\
  areg ms 10 = Z_to_bv 64 fd /\
  areg ms 12 = Z_to_bv 64 (Z.of_nat (length bufs)) /\
  (1 <= length bufs <= 1024)%nat /\
  bv_unsigned (areg ms 11) + 16 * Z.of_nat (length bufs) <= 2^47 /\
  lenok (Z.of_nat (length (concat bufs))) /\
  ms_rom ms = seg_rom segs /\
  rng RNG (bv_unsigned (areg ms 11)) (16 * Z.of_nat (length bufs)) /\
  exists iovs : list (word * word),
    bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) /\
    Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                           bv_unsigned (fst iov) + Z.of_nat (length bs) <= 2^47 /\
                           bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs /\
                           rng RNG (bv_unsigned (fst iov)) (Z.of_nat (length bs))) iovs bufs.

Definition at_nodeA (n : node) (RNG : footprint) (ms : machine_state) : Prop :=
  match n with
  | NBrk _ | NMprotect _ _ _ | NMremap _ _ _ | NMmapNR _ _ | NSetTid | NPeek _ => False   (* [comment removed for export] *)
  | NWritev fd bufs => at_gatherA 66 (fun fd => fd = 1 \/ fd = 2) (fun t => t <= max_write) fd bufs RNG ms
  | NWritevF fd bufs => at_gatherA 66 (fun fd => 3 <= fd < 2^32) (fun t => 1 <= t <= max_write) fd bufs RNG ms
  | _ => at_node segs n ms /\ ncov n RNG ms
  end.

#[using="Type"] Lemma at_gatherA_inv : forall sysno fdok lenok fd bufs RNG ms,
  at_gatherA sysno fdok lenok fd bufs RNG ms ->
  ms_svc_pending ms = Some (Z_to_bv 64 sysno) /\ fdok fd /\ areg ms 10 = Z_to_bv 64 fd /\
  areg ms 12 = Z_to_bv 64 (Z.of_nat (length bufs)) /\ (1 <= length bufs <= 1024)%nat /\
  bv_unsigned (areg ms 11) + 16 * Z.of_nat (length bufs) <= 2^47 /\ lenok (Z.of_nat (length (concat bufs))) /\
  ms_rom ms = seg_rom segs /\
  exists iovs : list (word * word),
    bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) /\
    Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                           bv_unsigned (fst iov) + Z.of_nat (length bs) <= 2^47 /\
                           bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs.
Proof.
  intros sysno fdok lenok fd bufs RNG ms (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _ & iovs & Hi & HF).
  repeat (split; [assumption|]). exists iovs. split; [exact Hi|].
  eapply Forall2_impl; [| exact HF]. cbn. intros a b (X & X2 & Y & _). auto.
Qed.

#[using="Type"] Lemma at_nodeA_at_node : forall n RNG ms, at_nodeA n RNG ms -> at_node segs n ms.
Proof.
  intros n RNG ms H. destruct n; cbn [at_nodeA] in H; try contradiction; try exact (proj1 H).
  - apply at_gatherA_inv in H. cbn [at_node]. exact H.
  - apply at_gatherA_inv in H. cbn [at_node]. exact H.
Qed.

#[using="Type"] Lemma at_nodeA_pending : forall n RNG ms, at_nodeA n RNG ms -> ms_svc_pending ms <> None.
Proof.
  intros n RNG ms H. apply at_nodeA_at_node in H.
  assert (Hx : exists x8, ms_svc_pending ms = Some x8).
  { destruct n; cbn [at_node] in H; try contradiction;
      first [ destruct H as [[X|X] _]; eexists; exact X
            | destruct H as [X _]; eexists; exact X
            | eexists; exact H ]. }
  destruct Hx as [x8 ->]. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition peek_reg_code (r j : Z) : Z := - (1 + 8 * r + j).
Definition reg_byte (ms : machine_state) (c : Z) : Z :=
  (bv_unsigned (areg ms (Z_to_bv 5 (c / 8))) / 2 ^ (8 * (c mod 8))) mod 256.
Definition peekA_val (ms : machine_state) (a : Z) : Z :=
  if a <? 0 then reg_byte ms (- a - 1) else peek_byte segs ms a.

Definition npeekA (n : node) : option (machine_state -> resp) :=
  match n with
  | NPeek a => Some (fun ms => peek_rsp (peekA_val ms a))
  | _ => None
  end.

#[using="Type"] Lemma peekA_val_range : forall ms a, 0 <= peekA_val ms a < 256.
Proof.
  intros ms a. unfold peekA_val. destruct (a <? 0); [| apply peek_byte_range].
  unfold reg_byte. apply Z.mod_pos_bound. lia.
Qed.

#[using="Type"] Lemma peekA_val_reg : forall ms r j, 0 <= r < 32 -> 0 <= j < 8 ->
  peekA_val ms (peek_reg_code r j) = (bv_unsigned (areg ms (Z_to_bv 5 r)) / 2 ^ (8 * j)) mod 256.
Proof.
  intros ms r j Hr Hj. unfold peekA_val, peek_reg_code.
  replace (- (1 + 8 * r + j) <? 0) with true by (symmetry; apply Z.ltb_lt; lia).
  unfold reg_byte. replace (- - (1 + 8 * r + j) - 1) with (j + r * 8) by lia.
  rewrite Z.div_add by lia. rewrite Z.mod_add by lia.
  rewrite (Z.div_small j 8) by lia. rewrite (Z.mod_small j 8) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma reg_bytes_sum : forall x, 0 <= x < 2^64 ->
  (x / 2^(8*0)) mod 256 + 2^8 * ((x / 2^(8*1)) mod 256) + 2^16 * ((x / 2^(8*2)) mod 256) + 2^24 * ((x / 2^(8*3)) mod 256)
  + 2^32 * ((x / 2^(8*4)) mod 256) + 2^40 * ((x / 2^(8*5)) mod 256) + 2^48 * ((x / 2^(8*6)) mod 256)
  + 2^56 * ((x / 2^(8*7)) mod 256) = x.
Proof.
  intros x Hx.
  change (2 ^ (8 * 0)) with 1. change (2 ^ (8 * 1)) with 256. change (2 ^ (8 * 2)) with (256*256).
  change (2 ^ (8 * 3)) with (256*256*256). change (2 ^ (8 * 4)) with (256*256*256*256).
  change (2 ^ (8 * 5)) with (256*256*256*256*256). change (2 ^ (8 * 6)) with (256*256*256*256*256*256).
  change (2 ^ (8 * 7)) with (256*256*256*256*256*256*256).
  rewrite <- !Z.div_div by lia. rewrite Z.div_1_r.
  pose proof (Z.div_mod x 256 ltac:(lia)) as E0.
  pose proof (Z.div_mod (x / 256) 256 ltac:(lia)) as E1.
  pose proof (Z.div_mod (x / 256 / 256) 256 ltac:(lia)) as E2.
  pose proof (Z.div_mod (x / 256 / 256 / 256) 256 ltac:(lia)) as E3.
  pose proof (Z.div_mod (x / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E4.
  pose proof (Z.div_mod (x / 256 / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E5.
  pose proof (Z.div_mod (x / 256 / 256 / 256 / 256 / 256 / 256) 256 ltac:(lia)) as E6.
  assert (E7 : x / 256 / 256 / 256 / 256 / 256 / 256 / 256 < 256).
  { repeat (apply Z.div_lt_upper_bound; [lia|]). lia. }
  assert (P7 : 0 <= x / 256 / 256 / 256 / 256 / 256 / 256 / 256) by (repeat apply Z.div_pos; lia).
  rewrite (Z.mod_small (x / 256 / 256 / 256 / 256 / 256 / 256 / 256) 256) by lia.
  change (2^8) with 256. change (2^16) with (256*256). change (2^24) with (256*256*256). change (2^32) with (256*256*256*256).
  change (2^40) with (256*256*256*256*256). change (2^48) with (256*256*256*256*256*256). change (2^56) with (256*256*256*256*256*256*256).
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Variable SHM : list (Z * Z).

(* [comment removed for export] *)
Definition madv_rsp (addr len : Z) : resp :=
  mkEffect (Z_to_bv 64 0) [] [(Z_to_bv 64 addr, Z_to_bv 64 (page_round_up_Z len))].

Definition silA (RNG : footprint) (ms ms' : machine_state) : Prop :=
  exists addr len,
    ms_svc_pending ms = Some (Z_to_bv 64 233) /\
    areg ms 10 = Z_to_bv 64 addr /\ areg ms 11 = Z_to_bv 64 len /\
    bv_unsigned (int32 (areg ms 12)) = MADV_DONTNEED /\   (* [comment removed for export] *)
    0 <= addr /\ addr mod page_size = 0 /\ 0 < len < 2^64 /\ addr + page_round_up_Z len < 2^64 /\
    Exists (fun e => fst e <= addr /\ addr + page_round_up_Z len <= fst e + snd e) SHM /\
    ms' = nret ms (madv_rsp addr len).

End AtNodeA.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wins_npeek_ext : forall {nd : Type} (np1 np2 : nd -> option (machine_state -> resp)) nst nex,
  (forall n, np1 n = None <-> np2 n = None) ->
  forall {R} (t : itree nd R) mo W, wins np1 nst nex t mo W -> wins np2 nst nex t mo W.
Proof.
  intros nd np1 np2 nst nex HE R t mo W H.
  induction H as [t mo T HT|n k mo T code mo' Hn Hex HT|n k mo T rsp mo' evs Hn Hst Hw IH|n k mo T f Hn Hall IH].
  - apply wins_nil. exact HT.
  - eapply wins_exit; [apply HE; exact Hn| exact Hex| exact HT].
  - eapply wins_vis; [apply HE; exact Hn| exact Hst| exact IH].
  - destruct (np2 n) as [f2|] eqn:E2.
    + eapply wins_peek; [exact E2|]. exact IH.
    + apply HE in E2. congruence.
Qed.

(* [comment removed for export] *)
Lemma wins_npeekA : forall segs segs' {R} (t : itree node R) mo W,
  wins (Nodes.npeek segs') nstep nexit t mo W <-> wins (npeekA segs) nstepA nexitA t mo W.
Proof.
  intros segs segs' R t mo W. unfold nstepA, nexitA.
  split; apply wins_npeek_ext; intros n; destruct n; cbn; split; intros H; try reflexivity; try discriminate H.
Qed.
