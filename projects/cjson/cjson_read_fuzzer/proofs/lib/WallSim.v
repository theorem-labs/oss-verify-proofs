(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: launch over the whole ProcInput, mmap base and vDSO state; access_ok and channel-reader premises on writes, plus a no-reader case where both runs die of SIGPIPE at the first write; stack/argv lemmas restated for the AT_EXECFN block; comments filled in. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.EquivalenceDefinition Require MustExit.
From LinuxProcessSemantics.EquivalenceDefinition Require OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Vdso.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.LinuxProcessSem Require OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Fs.ReadWrite.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ExitSim.
Module CatSim.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.MustExit LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite.
Import LinuxProcessSemantics.LinuxProcessSem.Vdso.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ExitSim.SimInv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ExitSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma read_aux_read_byte : forall ms k a,
  read_bytes_aux (ms_read_byte ms) a k = ms_read_bytes_aux ms a k.
Proof.
  intros ms. induction k as [|k IH]; intro a; [reflexivity|].
  cbn [read_bytes_aux ms_read_bytes_aux].
  destruct (ms_read_byte ms a) as [b|]; [rewrite IH|]; reflexivity.
Qed.

Lemma read_bytes_map_read_byte : forall ms a len,
  read_bytes_map (ms_read_byte ms) a len = ms_read_bytes ms a len.
Proof. intros. rewrite read_bytes_map_eq. unfold ms_read_bytes.
  apply read_aux_read_byte. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma apply_effect_no_write : forall ms r,
  apply_effect ms (mkEffect r [] []) = set_gpr0 ms r.
Proof.
  intros ms r. unfold apply_effect, set_gpr0.
  cbn [eff_ret eff_writes eff_zeros apply_zeros apply_writes].
  reflexivity.
Qed.

Lemma apply_effect_copyins_no_write : forall ms r copyins,
  apply_effect ms (with_copyins copyins (mkEffect r [] [])) = set_gpr0 ms r.
Proof.
  intros ms r copyins. unfold with_copyins, apply_effect, set_gpr0.
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies
       apply_unmaps apply_zeros apply_copies apply_writes].
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_sysno_sys_input64 : forall segs ms x8,
  in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.
Lemma in_arg0_sys_input64 : forall segs ms x8,
  in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.
Lemma in_arg1_sys_input64 : forall segs ms x8,
  in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof. reflexivity. Qed.
Lemma in_arg2_sys_input64 : forall segs ms x8,
  in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof. reflexivity. Qed.
Lemma in_mem_sys_input : forall segs ms x8,
  in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma syscall_spec_write : forall segs ms x8 model o,
  bv_unsigned x8 = 64%Z ->
  (syscall_spec (sys_input segs ms x8) model o
   <-> write_spec (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
         (sys_input segs ms x8) model o).
Proof.
  intros segs ms x8 model o Hno.
  unfold syscall_spec, dispatch.
  change (in_sysno (sys_input segs ms x8)) with x8.
  rewrite Hno. reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fd1chan (model : Model) : Prop :=
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))
  /\ m_channel_reader model = true.

(* [comment removed for export] *)
Definition buf_modeled (b : list byte) : Prop :=
  (Z.of_nat (length b) <= rw_bytes_max)%Z.

Definition bufs_modeled (bufs : list (list byte)) : Prop :=
  Forall buf_modeled bufs.

(* [comment removed for export] *)
Lemma bufs_modeled_single : forall b, buf_modeled b -> bufs_modeled [b].
Proof. intros b H. apply Forall_cons; [exact H | apply Forall_nil]. Qed.

(* [comment removed for export] *)
Lemma buf_modeled_nil : buf_modeled [].
Proof. unfold buf_modeled. cbn. unfold rw_bytes_max. lia. Qed.

Lemma buf_modeled_skipn : forall n (b : list byte),
  buf_modeled b -> buf_modeled (skipn n b).
Proof.
  intros n b H. unfold buf_modeled in *. rewrite length_skipn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma write1_check_n : forall segs ms x8 model buf n,
  fd1chan model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* THE RANGE [vfs_write]'s [access_ok] ACCEPTS.  The channel arm asks it
     on the named count before it reads the source, so a delivery is
     admissible only there: without this premise the lemma was true of a
     walk that wrapped at 2^64 and is false of one that does not, exactly
     where the buffer leaves the user address space ([buf + count] past
     [State.TASK_SIZE]; [Uaccess.access_okb_intro] gives it from that
     inequality).  A repair of a statement that had become false, not a
     weakening *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  check_write (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (with_copyins [(ms_gpr ms 1, n)]
      (mkEffect (len_word (firstn n buf)) [] [])) model
    = CheckOk model (map (WriteEv (Z_to_bv 64 1)) (firstn n buf)).
Proof.
  intros segs ms x8 model buf n Hfd Hno Hg Hr Hok Hcnt Hn1 Hn2.
  unfold fd1chan in Hfd. destruct Hfd as [Hfd Hrdr].
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  pose proof (word_unsigned_range (ms_gpr ms 2)) as Hcr.
  assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
    by (unfold buf_modeled in Hcnt; lia).
  assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
    by (apply rw_range_in_range; exact Hcw).
  unfold check_write.
  rewrite Hg; norm_fd32; rewrite Hfd.
  change (w_is0 (Z_to_bv 64 1)) with false. cbv beta iota.
  rewrite Hmc. cbv beta iota.
  assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
  rewrite Hc. cbv beta iota. cbv zeta.
  rewrite Hok. cbn [negb]. cbv beta iota.
  rewrite Hrdr. change (negb true) with false. cbv beta iota.
  rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb).
  assert (Hg0 : Nat.eqb (length buf) 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Hg0. cbv beta iota. unfold with_copyins; cbn.
  assert (Hlenf : Z.of_nat (length (firstn n buf)) = Z.of_nat n)
    by (rewrite length_firstn; lia).
  assert (Hru : bv_unsigned (len_word (firstn n buf)) = Z.of_nat n).
  { rewrite (len_word_unsigned (firstn n buf));
      [exact Hlenf | rewrite Hlenf; lia]. }
  rewrite ?Hru.
  assert (Hg1 : (1 <=? Z.of_nat n)%Z = true) by (apply Z.leb_le; lia).
  assert (Hg2 : (Z.of_nat n <=? Z.of_nat (length buf))%Z = true)
    by (apply Z.leb_le; lia).
  rewrite ?Hg1, ?Hg2. cbn [andb].
  rewrite ?Nat2Z.id, bv_eqb_refl, Nat.eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma write1_ok_n : forall segs ms x8 model buf n,
  fd1chan model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* see [write1_check_n] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (with_copyins [(ms_gpr ms 1, n)]
          (mkEffect (len_word (firstn n buf)) [] [])) model
        (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
Proof.
  intros segs ms x8 model buf n Hfd Hno Hg Hr Hok Hcnt Hn1 Hn2.
  apply (proj2 (syscall_spec_write _ _ _ _ _ Hno)).
  apply check_write_sound_ok. apply write1_check_n; assumption.
Qed.

(* [comment removed for export] *)
Lemma write1_ok_inv : forall segs ms x8 model eff model' evs buf,
  fd1chan model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  (1 <= length buf)%nat ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    eff = with_copyins [(ms_gpr ms 1, n)]
            (mkEffect (len_word (firstn n buf)) [] []) /\ model' = model /\
    evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf).
Proof.
  intros segs ms x8 model eff model' evs buf Hfd Hno Hg Hr Hok Hnb Hspec.
  unfold fd1chan in Hfd. destruct Hfd as [Hfd Hrdr].
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply check_write_complete_ok in Hspec.
  unfold check_write in Hspec.
  rewrite Hg in Hspec; norm_fd32; rewrite Hfd in Hspec.
  change (w_is0 (Z_to_bv 64 1)) with false in Hspec. cbv beta iota in Hspec.
  (* being handed [Ok] already rules the transfer-size guard out: had it
     fired, the checker would have answered [CheckUnmodeled] *)
  destruct (negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)));
    cbv beta iota in Hspec; [discriminate|].
  assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
  rewrite Hc in Hspec. cbv beta iota zeta in Hspec.
  rewrite Hok in Hspec. cbn [negb] in Hspec. cbv beta iota in Hspec.
  rewrite Hrdr in Hspec. change (negb true) with false in Hspec.
  cbv beta iota in Hspec.
  (* the source the transfer sees is the CLAMPED prefix of the range the
     call named -- [buf] itself for every count under [MAX_RW_COUNT], and
     a prefix of it above, which the gate above admits at an in-range
     buffer *)
  rewrite (write_source_prefix _ _ _ _ Hrb) in Hspec.
  pose proof (rw_count_clamp_range (ms_gpr ms 2)) as Hcl.
  set (c := Z.to_nat (rw_count_clamp (ms_gpr ms 2))) in *.
  assert (Hcpos : (1 <= c)%nat)
    by (unfold c, rw_count_clamp, MAX_RW_COUNT in *; lia).
  assert (Hfl : length (firstn c buf) = Nat.min c (length buf))
    by apply length_firstn.
  assert (Hg0 : Nat.eqb (length (firstn c buf)) 0 = false)
    by (rewrite Hfl; apply Nat.eqb_neq; lia).
  rewrite Hg0 in Hspec. cbv beta iota in Hspec.
  destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
    destruct zs as [|? ?]; destruct us as [|? ?];
      destruct cs as [|? ?]; try discriminate.
  destruct ((1 <=? bv_unsigned ret)%Z
            && (bv_unsigned ret <=? Z.of_nat (length (firstn c buf)))%Z) eqn:Hgr;
    [|discriminate].
  destruct (access_ranges_eqb copyins [(ms_gpr ms 1, Z.to_nat (bv_unsigned ret))])
    eqn:Hreads; [|discriminate].
  inversion Hspec; clear Hspec; subst.
  apply andb_true_iff in Hgr as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  rewrite Hfl in H2.
  apply access_ranges_eqb_eq in Hreads. subst copyins.
  exists (Z.to_nat (bv_unsigned ret)).
  assert (Hff : firstn (Z.to_nat (bv_unsigned ret)) (firstn c buf)
                = firstn (Z.to_nat (bv_unsigned ret)) buf)
    by (rewrite firstn_firstn; f_equal; lia).
  rewrite Hff.
  assert (Hlw : len_word (firstn (Z.to_nat (bv_unsigned ret)) buf) = ret)
    by (apply len_word_firstn_ret; lia).
  rewrite Hlw. repeat split; try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Lemma write1_no_unmodeled : forall segs ms x8 model buf,
  fd1chan model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (* a zero [count] is genuinely unmodeled when the range verdict is
     unclear (see [access_ok_zero] in the write spec), so the nonempty
     buffer is load-bearing here, not just convenient *)
  (1 <= length buf)%nat ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model buf Hfd Hno Hg Hr Hcnt Hnb Hspec.
  unfold fd1chan in Hfd. destruct Hfd as [Hfd Hrdr].
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
    by (unfold buf_modeled in Hcnt; lia).
  assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
    by (apply rw_range_in_range; exact Hcw).
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply (check_write_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  unfold check_write in Hspec.
  rewrite Hg in Hspec; norm_fd32; rewrite Hfd in Hspec.
  change (w_is0 (Z_to_bv 64 1)) with false in Hspec. cbv beta iota in Hspec.
  rewrite Hmc in Hspec. cbv beta iota in Hspec.
  destruct (w_is0 (ms_gpr ms 2)) eqn:Hc; try rewrite Hc in Hspec.
  { exfalso.
    assert (Hc0 : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
    congruence. }
  (* [vfs_write]'s [access_ok]: a refused range is -EFAULT, an answer *)
  destruct (negb (access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)))).
  { now apply check_ret_only_no_unmodeled in Hspec. }
  rewrite Hrdr in Hspec. change (negb true) with false in Hspec.
  cbv beta iota in Hspec.
  rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb)
    in Hspec.
  destruct (length buf =? 0)%nat eqn:Hz; try rewrite Hz in Hspec.
  { now apply check_ret_only_no_unmodeled in Hspec. }
  discriminate Hspec.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fd1dead (model : Model) : Prop :=
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))
  /\ m_channel_reader model = false
  /\ m_sigpipe_default model = true
  /\ m_sigpipe_terminal model = true
  /\ sigpipe_blocked (m_sigmask model) = false.

Lemma write1_dead_check : forall segs ms x8 model eff,
  fd1dead model ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  w_is0 (ms_gpr ms 2) = false ->
  check_write (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2) eff model
  = check_ret_only eff (errno_ret EPIPE)
      (with_killed (Z_to_bv 64 SIGPIPE) model) [].
Proof.
  intros segs ms x8 model eff (Hfd & Hrdr & Hdef & Hterm & Hmask) Hg Hok Hc.
  unfold check_write.
  rewrite Hg; norm_fd32; rewrite Hfd.
  change (w_is0 (Z_to_bv 64 1)) with false. cbv beta iota.
  rewrite (rw_range_of_access_ok _ _ Hok). cbv beta iota.
  rewrite Hc. cbv beta iota.
  rewrite Hrdr. change (negb false) with true. cbv beta iota.
  rewrite Hok. change (negb true) with false. cbv beta iota.
  unfold check_sigpipe_write, sigpipe_declines, raise_sigpipe.
  rewrite Hdef, Hterm, Hmask. reflexivity.
Qed.

Lemma write1_dead_ok : forall segs ms x8 model,
  fd1dead model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  w_is0 (ms_gpr ms 2) = false ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (mkEffect (errno_ret EPIPE) [] [])
        (with_killed (Z_to_bv 64 SIGPIPE) model) []).
Proof.
  intros segs ms x8 model Hd Hno Hg Hok Hc.
  apply (proj2 (syscall_spec_write _ _ _ _ _ Hno)).
  apply check_write_sound_ok.
  rewrite (write1_dead_check segs ms x8 model _ Hd Hg Hok Hc).
  apply check_ret_only_ok_iff. split; [reflexivity | split; reflexivity].
Qed.

Lemma write1_dead_ok_inv : forall segs ms x8 model eff model' evs,
  fd1dead model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  w_is0 (ms_gpr ms 2) = false ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  eff = mkEffect (errno_ret EPIPE) [] []
  /\ model' = with_killed (Z_to_bv 64 SIGPIPE) model /\ evs = [].
Proof.
  intros segs ms x8 model eff model' evs Hd Hno Hg Hok Hc Hspec.
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply check_write_complete_ok in Hspec.
  rewrite (write1_dead_check segs ms x8 model eff Hd Hg Hok Hc) in Hspec.
  apply check_ret_only_ok_iff in Hspec. exact Hspec.
Qed.

Lemma write1_dead_no_unmodeled : forall segs ms x8 model,
  fd1dead model ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  w_is0 (ms_gpr ms 2) = false ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model Hd Hno Hg Hok Hc Hspec.
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply (check_write_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  rewrite (write1_dead_check segs ms x8 model _ Hd Hg Hok Hc) in Hspec.
  exact (check_ret_only_no_unmodeled _ _ _ _ Hspec).
Qed.

Lemma is_prefix_app_mono {A} : forall (l a b : list A),
  is_prefix a b -> is_prefix (l ++ a) (l ++ b).
Proof.
  induction l as [|x l IH]; intros a b H; cbn; [exact H | split; [reflexivity | apply IH; exact H]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint wevents_ch (ch : word) (bufs : list (list byte)) : list event :=
  match bufs with
  | [] => []
  | buf :: rest => map (WriteEv ch) buf ++ wevents_ch ch rest
  end.

Inductive wpick (ch : word) : list (list byte) -> list event -> Prop :=
| wp_nil : wpick ch [] []
| wp_cons : forall buf bufs n tr,
    (1 <= n)%nat -> (n <= length buf)%nat ->
    wpick ch bufs tr ->
    wpick ch (buf :: bufs) (map (WriteEv ch) (firstn n buf) ++ tr).

(* [comment removed for export] *)
Lemma wpick_wevents : forall ch bufs,
  Forall (fun b => (1 <= length b)%nat) bufs ->
  wpick ch bufs (wevents_ch ch bufs).
Proof.
  intros ch bufs H; induction H as [|b bs Hb Hbs IH].
  - apply wp_nil.
  - cbn [wevents_ch].
    pose proof (wp_cons ch b bs (length b) _ Hb (Nat.le_refl _) IH) as Hc.
    rewrite firstn_all in Hc. exact Hc.
Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive to_wexit : machine_state -> list (list byte) -> word -> Prop :=
| tw_exit : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    to_wexit ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| tw_write : forall ms x8 buf bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = Z_to_bv 64 1 ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
    (* the range [vfs_write]'s [access_ok] accepts; see [write1_check_n] *)
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
    (1 <= length buf)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
       to_wexit (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
    to_wexit ms (buf :: bufs) code
| tw_step : forall ms ms' bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wexit ms' bufs code ->
    to_wexit ms bufs code.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive msteps : machine_state -> machine_state -> Prop :=
| mst_refl : forall ms, msteps ms ms
| mst_step : forall ms ms' ms'',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    msteps ms' ms'' ->
    msteps ms ms''.

Lemma msteps_one : forall ms ms',
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  msteps ms ms'.
Proof. intros ms ms' Hsvc Hstep. eapply mst_step; [exact Hsvc | exact Hstep | apply mst_refl]. Qed.

Lemma msteps_trans : forall ms ms' ms'',
  msteps ms ms' -> msteps ms' ms'' -> msteps ms ms''.
Proof.
  intros ms ms' ms'' H; induction H; [auto|].
  intro H2. eapply mst_step; eauto.
Qed.

Lemma msteps_to_wexit : forall ms ms' bufs code,
  msteps ms ms' -> to_wexit ms' bufs code -> to_wexit ms bufs code.
Proof.
  intros ms ms' bufs code H; induction H; [auto|].
  intro Hw. eapply tw_step; eauto.
Qed.

(* [comment removed for export] *)
Lemma to_wexit_bufs_nonempty : forall ms bufs code,
  to_wexit ms bufs code ->
  Forall (fun b => (1 <= length b)%nat) bufs.
Proof.
  intros ms bufs code H;
    induction H as
      [ms x8 Hsvc Hx8
      | ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
      | ms ms' bufs code Hsvc Hstep Hte IH].
  - constructor.
  - constructor; [exact Hnb | apply (IH (length buf)); lia].
  - exact IH.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sstep_write_next_inv : forall ms model x8 buf evs c',
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* see [write1_check_n]: on a refused range the step is the -EFAULT *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  (1 <= length buf)%nat ->
  sstep segs (mkCfg ms model) evs (SNext c') ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf) /\
    c' = mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model.
Proof.
  intros ms model x8 buf evs c' Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hnb Hss.
  inversion Hss; subst; try congruence.
  - (* sstep_syscall *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hok Hnb H3)
        as (n & Hn1 & Hn2 & Heff & Hm & Hevs);
      subst eff model' evs0; exists n
    end.
    match goal with
    | Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
        rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
        inversion Hmat; subst model''
    end.
    rewrite apply_effect_copyins_no_write. repeat split; auto.
  - (* sstep_exit : model' halted, but write leaves model unchanged *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hok Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite Hh in H6; discriminate
    end.
  - (* sstep_killed : the same, through [State.m_killed_of_m_halted_none] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf Hfd Hno Hg Hr Hok Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite (m_killed_of_m_halted_none model Hh) in H6;
      discriminate
    end.
Qed.

Lemma sstep_write_inv : forall ms model x8 buf evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1chan model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  sstep segs (mkCfg ms model) evs st ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    evs = map (WriteEv (Z_to_bv 64 1)) (firstn n buf) /\
    st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model).
Proof.
  intros ms model x8 buf evs st Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hcnt Hnb Hss.
  destruct st as [c'|].
  - destruct (sstep_write_next_inv ms model x8 buf evs c'
                Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc').
    exists n. repeat split; [exact Hn1 | exact Hn2 | exact Hevs | now rewrite Hc'].
  - (* SError: only [sstep_syscall_unmodeled] reaches it, and the write
       is modeled *)
    exfalso. inversion Hss; subst; try congruence.
    + match goal with
      | H2 : ms_svc_pending ms = Some ?x,
        H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
        Hmat : materialize_model_accesses ?model' _ = None |- _ =>
        assert (Hx : x = x8) by congruence; subst x;
        destruct (write1_ok_inv segs ms x8 model eff model' evs0 buf
                    Hfd Hno Hg Hr Hok Hnb H3)
          as (n & _ & _ & _ & Hm & _);
        subst model'; rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
        discriminate
      end.
    + match goal with
      | H2 : ms_svc_pending ms = Some ?x,
        H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
        assert (Hx : x = x8) by congruence; subst x;
        apply (write1_no_unmodeled segs ms x8 model buf Hfd Hno Hg Hr Hcnt Hnb H3)
      end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint wevents (bufs : list (list byte)) : list event :=
  match bufs with
  | [] => []
  | buf :: rest => map (WriteEv (Z_to_bv 64 1)) buf ++ wevents rest
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition wexit_post (bufs : list (list byte)) (code : word) (fs : Fs.Fs) : post :=
  fun tr o =>
    (exists full, wpick (Z_to_bv 64 1) bufs full /\ tr = full ++ [ExitEv code fs])
    /\ exits_with code tr o.

Definition wexit_ready (bufs : list (list byte)) (model : Model) : Prop :=
  bufs = [] \/ fd1chan model.

Lemma to_wexit_exec : forall ms bufs code,
  to_wexit ms bufs code ->
  forall model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  wexit_ready bufs model ->
  bufs_modeled bufs ->
  OmniRun.exec segs (mkCfg ms model) (wexit_post bufs code (m_fs model)).
Proof.
  intros ms bufs code Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros model Hh Hlazy Hfd Hbm.
  - (* tw_exit: the one transition is the exit *)
    apply (exec_step_only segs _ _
             [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
             (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
    + replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
        with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                       (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
        by (cbn; reflexivity).
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
               (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
      * exact Hh.
      * exact Hsvc.
      * apply (exit_dispatch_ok (sys_input segs ms x8) model).
        rewrite in_sysno_sys_input. exact Hx8.
      * cbn. reflexivity.
      * apply m_killed_with_halted.
    + intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * unfold wexit_post. cbn beta. rewrite app_nil_r. split.
        -- exists []. split; [apply wp_nil | reflexivity].
        -- cbn [exits_with cfg_model]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - (* tw_write: every delivered length is a successor, each covered by the IH *)
    destruct Hfd as [Hnil | Hfd]; [discriminate Hnil |].
    apply Forall_cons_iff in Hbm as [Hb Hbs].
    apply exec_step; [exact Hh | | |].
    + (* progress: full delivery *)
      eexists; eexists.
      apply (sstep_syscall segs ms model x8
               (with_copyins [(ms_gpr ms 1, length buf)]
                  (mkEffect (len_word (firstn (length buf) buf)) [] [])) model model
               (map (WriteEv (Z_to_bv 64 1)) (firstn (length buf) buf))).
      * exact Hh.
      * exact Hsvc.
      * apply write1_ok_n; try assumption. apply Nat.le_refl.
      * exact Hh.
      * rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
    + intros evs Hss.
      destruct (sstep_write_inv ms model x8 buf evs SError
                  Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hb Hnb Hss) as (n & _ & _ & _ & Habs).
      discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_write_inv ms model x8 buf evs (SNext c')
                  Hh Hlazy Hfd Hsvc Hno Hg Hr Hok Hb Hnb Hss) as (n & Hn1 & Hn2 & -> & Hc').
      injection Hc' as ->.
      eapply exec_conseq; [exact (IH n Hn1 Hn2 model Hh Hlazy (or_intror Hfd) Hbs) |].
      intros tr o ((full & Hpick & ->) & Hx). split.
      * exists (map (WriteEv (Z_to_bv 64 1)) (firstn n buf) ++ full).
        split; [apply wp_cons; assumption | apply app_assoc].
      * exact Hx.
  - (* tw_step: one silent instruction *)
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH model Hh Hlazy Hfd Hbm) |].
      intros tr o H. cbn [app]. exact H.
Qed.

Lemma to_wexit_star_admits : forall ms bufs code,
  to_wexit ms bufs code ->
  forall model full,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  wexit_ready bufs model ->
  bufs_modeled bufs ->
  wpick (Z_to_bv 64 1) bufs full ->
  exists c, star segs (mkCfg ms model) (full ++ [ExitEv code (m_fs model)]) c.
Proof.
  intros ms bufs code Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros model full Hh Hlazy Hfd Hbm Hpick.
  - (* tw_exit *)
    inversion Hpick; subst. cbn [app].
    exists (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
    apply star_one.
    replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
      with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                     (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
      by (cbn; reflexivity).
    apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
             (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
             (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
    + exact Hh.
    + exact Hsvc.
    + apply (exit_dispatch_ok (sys_input segs ms x8) model).
      rewrite in_sysno_sys_input. exact Hx8.
    + cbn. reflexivity.
    + apply m_killed_with_halted.
  - (* tw_write *)
    destruct Hfd as [Hnil | Hfd]; [discriminate Hnil |].
    apply Forall_cons_iff in Hbm as [Hb Hbs].
    inversion Hpick as [|buf' bufs' n tr Hn1 Hn2 Hpick']; subst.
    destruct (IH n Hn1 Hn2 model tr Hh Hlazy (or_intror Hfd) Hbs Hpick') as [c Hstar].
    exists c. rewrite <- app_assoc.
    eapply star_step; [| exact Hstar].
    rewrite <- (apply_effect_copyins_no_write ms
                  (len_word (firstn n buf)) [(ms_gpr ms 1, n)]).
    apply (sstep_syscall segs ms model x8
             (with_copyins [(ms_gpr ms 1, n)]
                (mkEffect (len_word (firstn n buf)) [] [])) model model
             (map (WriteEv (Z_to_bv 64 1)) (firstn n buf))).
    + exact Hh.
    + exact Hsvc.
    + apply write1_ok_n; assumption.
    + exact Hh.
    + rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
  - (* tw_step *)
    destruct (IH model full Hh Hlazy Hfd Hbm Hpick) as [c Hstar].
    exists c.
    replace (full ++ [ExitEv code (m_fs model)])
      with ([] ++ (full ++ [ExitEv code (m_fs model)])) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

Lemma to_wexit_star_only : forall ms bufs code,
  to_wexit ms bufs code ->
  forall model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  wexit_ready bufs model ->
  bufs_modeled bufs ->
  forall tr c, star segs (mkCfg ms model) tr c ->
    exists full, wpick (Z_to_bv 64 1) bufs full /\
      is_prefix tr (full ++ [ExitEv code (m_fs model)]).
Proof.
  intros ms bufs code Hte model Hh Hlazy Hfd Hbm tr c Hstar.
  destruct (exec_realizes _ _ _
              (exec_star _ _ _ _ _ (to_wexit_exec ms bufs code Hte model Hh Hlazy Hfd Hbm) Hstar))
    as (tr' & o & _ & HQ).
  unfold wexit_post in HQ. cbn beta in HQ. destruct HQ as ((full & Hpick & Heq) & _).
  exists full. split; [exact Hpick |]. rewrite <- Heq. apply is_prefix_app.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_wexit_no_error : forall ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  wexit_ready bufs model ->
  to_wexit ms bufs code ->
  bufs_modeled bufs ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model bufs code Hh Hlazy Hfd Hte Hbm. apply exec_no_error.
  eapply exec_conseq; [exact (to_wexit_exec ms bufs code Hte model Hh Hlazy Hfd Hbm) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(** The first write the run reaches names a range [access_ok] passes.
    With no reader the channel arm tests the NAMED range before it raises
    the signal ([vfs_write]'s order), and a range past [State.TASK_SIZE]
    answers -EFAULT and lets the run go on, on a return no [to_wexit]
    write node continues from.  The prefix it walks is [to_wexit]'s own
    silent prefix, so a per-binary proof builds it from the same
    [msteps] ([msteps_wfirst_ok]). *)
Inductive wfirst_ok : machine_state -> Prop :=
| wfo_write : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
    wfirst_ok ms
| wfo_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    wfirst_ok ms' ->
    wfirst_ok ms.

Lemma msteps_wfirst_ok : forall ms ms',
  msteps ms ms' -> wfirst_ok ms' -> wfirst_ok ms.
Proof.
  intros ms ms' H; induction H; [auto|].
  intro Hw. eapply wfo_step; eauto.
Qed.

Definition wkill_post (fs : Fs.Fs) : post :=
  fun tr o =>
    tr = [KillEv (Z_to_bv 64 SIGPIPE) fs]
    /\ match o with
       | OHalt c => m_killed (cfg_model c) = Some (Z_to_bv 64 SIGPIPE)
       | OError _ => False
       end.

Lemma sstep_write_dead_inv : forall ms model x8 evs st,
  m_halted model = None ->
  fd1dead model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = Z_to_bv 64 1 ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  w_is0 (ms_gpr ms 2) = false ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [KillEv (Z_to_bv 64 SIGPIPE) (m_fs model)]
  /\ st = SNext (mkCfg ms (with_killed (Z_to_bv 64 SIGPIPE) model)).
Proof.
  intros ms model x8 evs st Hh Hd Hsvc Hno Hg Hok Hc Hss.
  inversion Hss; subst; try congruence.
  all: match goal with
       | H2 : ms_svc_pending ?m = Some ?x,
         H3 : syscall_spec (sys_input segs ?m ?x) _ _ |- _ =>
           try (assert (Hx : x = x8) by congruence; subst x)
       end.
  all: match goal with
       | H3 : syscall_spec (sys_input segs ?m ?x) ?mo Unmodeled |- _ =>
           exfalso; exact (write1_dead_no_unmodeled segs m x mo Hd Hno Hg Hok Hc H3)
       | H3 : syscall_spec (sys_input segs ?m ?x) ?mo (Ok ?eff ?model' ?evs0) |- _ =>
           destruct (write1_dead_ok_inv segs m x mo eff model' evs0
                       Hd Hno Hg Hok Hc H3) as (-> & -> & ->)
       end.
  all: rewrite ?m_halted_with_killed, ?m_killed_with_killed in *;
       try discriminate.
  match goal with
  | H : Some _ = Some ?sig |- _ => injection H as Hsig; subst sig
  end.
  split; reflexivity.
Qed.

Lemma to_wexit_kill_exec : forall ms bufs code,
  to_wexit ms bufs code ->
  bufs <> [] ->
  wfirst_ok ms ->
  forall model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fd1dead model ->
  OmniRun.exec segs (mkCfg ms model) (wkill_post (m_fs model)).
Proof.
  intros ms bufs code Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr _ Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH];
    intros Hne Hfo model Hh Hlazy Hd.
  - exfalso. exact (Hne eq_refl).
  - (* the first write: signal 13 kills the process *)
    assert (Hok : access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true).
    { inversion Hfo; subst; [assumption | congruence]. }
    assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                    (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
    { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
    pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
    assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
    apply (exec_step_only segs _ _ [KillEv (Z_to_bv 64 SIGPIPE) (m_fs model)]
             (mkCfg ms (with_killed (Z_to_bv 64 SIGPIPE) model))).
    + replace [KillEv (Z_to_bv 64 SIGPIPE) (m_fs model)]
        with ([] ++ [KillEv (Z_to_bv 64 SIGPIPE)
                       (m_fs (with_killed (Z_to_bv 64 SIGPIPE) model))])
        by reflexivity.
      apply (sstep_killed segs ms model x8 (mkEffect (errno_ret EPIPE) [] [])
               (with_killed (Z_to_bv 64 SIGPIPE) model) [] (Z_to_bv 64 SIGPIPE)).
      * exact Hh.
      * exact Hsvc.
      * exact (write1_dead_ok segs ms x8 model Hd Hno Hg Hok Hc).
      * apply m_killed_with_killed.
    + intros evs st Hss.
      exact (sstep_write_dead_inv ms model x8 evs st Hh Hd Hsvc Hno Hg Hok Hc Hss).
    + apply exec_halt.
      * cbn [cfg_model]. rewrite m_halted_with_killed. discriminate.
      * cbv beta. unfold wkill_post.
        split; [rewrite app_nil_r; reflexivity |].
        cbn [cfg_model]. apply m_killed_with_killed.
  - (* a silent instruction: the first write is still ahead *)
    assert (Hfo' : wfirst_ok ms').
    { inversion Hfo; subst; [congruence |].
      match goal with
      | Hs : RiscvSemantics.step segs ms = MachineOk ?m2, Hw : wfirst_ok ?m2 |- _ =>
          rewrite Hstep in Hs; injection Hs as Hm2; subst m2; exact Hw
      end. }
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hne Hfo' model Hh Hlazy Hd) |].
      intros tr o H. cbn [app]. exact H.
Qed.

Lemma to_wexit_kill_obs_iff : forall ms bufs code model,
  to_wexit ms bufs code -> bufs <> [] -> wfirst_ok ms ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1dead model ->
  forall tr, obs_trace segs (mkCfg ms model) tr
             <-> is_prefix tr [KillEv (Z_to_bv 64 SIGPIPE) (m_fs model)].
Proof.
  intros ms bufs code model Hte Hne Hfo Hh Hlazy Hd.
  apply exec_obs_iff.
  eapply exec_conseq;
    [exact (to_wexit_kill_exec ms bufs code Hte Hne Hfo model Hh Hlazy Hd) |].
  intros tr o (Htr & Ho). split; [exact Htr |].
  destruct o; [exact (fun h => h) | destruct Ho].
Qed.

Lemma to_wexit_kill_no_error : forall ms bufs code model,
  to_wexit ms bufs code -> bufs <> [] -> wfirst_ok ms ->
  m_halted model = None -> m_vm_lazy model = [] -> fd1dead model ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms bufs code model Hte Hne Hfo Hh Hlazy Hd. apply exec_no_error.
  eapply exec_conseq;
    [exact (to_wexit_kill_exec ms bufs code Hte Hne Hfo model Hh Hlazy Hd) |].
  intros tr o (_ & Ho). destruct o; [exact (fun h => h) | destruct Ho].
Qed.

End WithSegs.

Definition wexit_launch (bufs : list (list byte)) (inp : ProcInput) : Prop :=
  bufs = [] \/ in_channel_reader inp = true.

Lemma init_model_fd1chan : forall reserved brk0 mb sp lim inp,
  in_channel_reader inp = true ->
  fd1chan (init_model reserved brk0 mb sp lim inp).
Proof. intros reserved brk0 mb sp lim inp Hr. split; [reflexivity | exact Hr]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma init_model_wexit_ready : forall reserved brk0 mb sp lim inp bufs,
  wexit_launch bufs inp ->
  wexit_ready bufs (init_model reserved brk0 mb sp lim inp).
Proof.
  intros reserved brk0 mb sp lim inp bufs [Hnil | Hr];
    [left; exact Hnil | right; apply init_model_fd1chan; exact Hr].
Qed.

Lemma wexit_ready_with_vdso : forall v m bufs,
  wexit_ready bufs m -> wexit_ready bufs (with_vdso v m).
Proof. intros v m bufs [Hnil | Hr]; [left; exact Hnil | right; exact Hr]. Qed.

Lemma fd1dead_with_vdso : forall v m, fd1dead m -> fd1dead (with_vdso v m).
Proof. intros v m H; exact H. Qed.

Definition sigpipe_fatal (inp : ProcInput) : Prop :=
  in_sigpipe_default inp = true /\ in_sigpipe_terminal inp = true
  /\ sigpipe_blocked (in_sigmask inp) = false.

Lemma init_model_fd1dead : forall reserved brk0 mb sp lim inp,
  in_channel_reader inp = false ->
  sigpipe_fatal inp ->
  fd1dead (init_model reserved brk0 mb sp lim inp).
Proof.
  intros reserved brk0 mb sp lim inp Hr (Hd & Ht & Hm).
  split; [reflexivity | split; [exact Hr | split; [exact Hd | split; [exact Ht | exact Hm]]]].
Qed.

Lemma cat_omni_run_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb) (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) bufs code ->
  bufs_modeled bufs ->
  wexit_launch bufs inp ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (wexit_post bufs code (in_fs inp)).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl.
  cbn [omni_run]. unfold init_config.
  exact (to_wexit_exec (run_segments segs inp sp mb) _ bufs code Hte
           (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp))
           eq_refl eq_refl
           (wexit_ready_with_vdso _ _ _
              (init_model_wexit_ready
                 (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp
                 lim inp bufs Hl)) Hbm).
Qed.

Lemma cat_obs_iff_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb) (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) bufs code ->
  bufs_modeled bufs ->
  wexit_launch bufs inp ->
  forall tr, obs_trace (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) tr
             <-> exists full, wpick (Z_to_bv 64 1) bufs full /\
                 is_prefix tr (full ++ [ExitEv code (in_fs inp)]).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl tr.
  set (fs0 := in_fs inp) in *.
  unfold init_config in *.
  set (ms := init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) in *.
  assert (Hh : m_halted (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) = None) by reflexivity.
  assert (Hlazy : m_vm_lazy (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) = []) by reflexivity.
  assert (Hfd : wexit_ready bufs (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)))
    by (apply wexit_ready_with_vdso;
        apply init_model_wexit_ready; exact Hl).
  assert (Hfs : m_fs (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp)) = fs0) by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    destruct (to_wexit_star_only (run_segments segs inp sp mb) ms bufs code Hte _ Hh Hlazy Hfd Hbm tr' c Hstar)
      as (full & Hw & Hpref).
    rewrite Hfs in Hpref.
    exists full. split; [exact Hw|].
    eapply is_prefix_trans; eauto.
  - intros (full & Hw & Hp).
    destruct (to_wexit_star_admits (run_segments segs inp sp mb) ms bufs code Hte _ full Hh Hlazy Hfd Hbm Hw)
      as [c Hstar].
    rewrite Hfs in Hstar.
    exists (full ++ [ExitEv code fs0]), c. split; assumption.
Qed.

Lemma cat_no_error_run_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb) (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) bufs code ->
  bufs_modeled bufs ->
  wexit_launch bufs inp ->
  ~ reaches_error (run_segments segs inp sp mb) (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl. apply exec_no_error.
  eapply exec_conseq; [exact (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
Lemma cat_must_exit_with_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb) (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) bufs code ->
  bufs_modeled bufs ->
  wexit_launch bufs inp ->
  must_exit_with code (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl. apply must_exit_with_iff.
  eapply exec_conseq; [exact (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl) |].
  intros tr o (_ & Hx). exact Hx.
Qed.

Lemma cat_omni_run_te_code_unique : forall segs pc ph sp brk0 mb rnd lim inp bufs code code',
  to_wexit (run_segments segs inp sp mb) (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) bufs code ->
  bufs_modeled bufs ->
  wexit_launch bufs inp ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp (exits_with code') ->
  code' = code.
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code code' Hte Hbm Hl Hex.
  pose proof (cat_omni_run_te segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hbm Hl) as Hrun.
  cbn [omni_run] in Hrun, Hex.
  destruct (exec_realizes _ _ _ Hrun) as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as Hx'. symmetry. exact Hx'.
Qed.

(* [comment removed for export] *)
Lemma cat_kill_omni_run_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
    bufs code ->
  bufs <> [] ->
  wfirst_ok (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ->
  in_channel_reader inp = false ->
  sigpipe_fatal inp ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (wkill_post (in_fs inp)).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hne Hfo Hr Hm.
  cbn [omni_run]. unfold init_config.
  exact (to_wexit_kill_exec (run_segments segs inp sp mb) _ bufs code Hte Hne Hfo
           (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp))
           eq_refl eq_refl
           (fd1dead_with_vdso _ _
              (init_model_fd1dead
                 (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp
                 lim inp Hr Hm))).
Qed.

Lemma cat_kill_obs_iff_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
    bufs code ->
  bufs <> [] ->
  wfirst_ok (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ->
  in_channel_reader inp = false ->
  sigpipe_fatal inp ->
  forall tr, obs_trace (run_segments segs inp sp mb)
               (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) tr
             <-> is_prefix tr [KillEv (Z_to_bv 64 SIGPIPE) (in_fs inp)].
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hne Hfo Hr Hm tr.
  unfold init_config.
  exact (to_wexit_kill_obs_iff (run_segments segs inp sp mb) _ bufs code
           (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp))
           Hte Hne Hfo eq_refl eq_refl
           (fd1dead_with_vdso _ _
              (init_model_fd1dead
                 (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp
                 lim inp Hr Hm)) tr).
Qed.

Lemma cat_kill_no_error_run_te : forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  to_wexit (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp)
    bufs code ->
  bufs <> [] ->
  wfirst_ok (run_segments segs inp sp mb)
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ->
  in_channel_reader inp = false ->
  sigpipe_fatal inp ->
  ~ reaches_error (run_segments segs inp sp mb)
      (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp).
Proof.
  intros segs pc ph sp brk0 mb rnd lim inp bufs code Hte Hne Hfo Hr Hm.
  unfold init_config.
  exact (to_wexit_kill_no_error (run_segments segs inp sp mb) _ bufs code
           (with_vdso (vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp))
           Hte Hne Hfo eq_refl eq_refl
           (fd1dead_with_vdso _ _
              (init_model_fd1dead
                 (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp
                 lim inp Hr Hm))).
Qed.

Definition cat_launch (source_segs : list Segment) (ms_source : machine_state)
    (target_segs : list Segment) (ms_target : machine_state)
    (bufs : list (list byte)) (inp : ProcInput) : Prop :=
  wexit_launch bufs inp
  \/ (sigpipe_fatal inp
      /\ wfirst_ok source_segs ms_source /\ wfirst_ok target_segs ms_target).

Lemma cat_launch_cases : forall source_segs ms_source target_segs ms_target bufs inp,
  cat_launch source_segs ms_source target_segs ms_target bufs inp ->
  wexit_launch bufs inp
  \/ (bufs <> [] /\ in_channel_reader inp = false
      /\ sigpipe_fatal inp
      /\ wfirst_ok source_segs ms_source /\ wfirst_ok target_segs ms_target).
Proof.
  intros source_segs ms_source target_segs ms_target bufs inp
    [Hw | (Hm & Hfs & Hft)]; [left; exact Hw |].
  destruct bufs as [| b bs]; [left; left; reflexivity |].
  destruct (in_channel_reader inp) eqn:Hr; [left; right; exact Hr |].
  right. split; [discriminate |].
  split; [reflexivity | split; [exact Hm | split; [exact Hfs | exact Hft]]].
Qed.

Lemma cat_omni_strong_equiv_te :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp,
  to_wexit (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) bufs code ->
  to_wexit (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) bufs code ->
  bufs_modeled bufs ->
  cat_launch (run_segments source_segs inp rsp rmb)
             (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
             (run_segments target_segs inp asp amb)
             (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
             bufs inp ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp
    Hsource Htarget Hbm Hl.
  destruct (cat_launch_cases _ _ _ _ _ _ Hl) as [Hw | (Hne & Hr & Hm & Hfs & Hft)].
  - (* a reader, or no write: both runs exit after the same deliveries *)
    split.
    { cbn [img_segments].
      eapply coexec_conseq;
        [apply exec_coexec;
         exact (cat_omni_run_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code Hsource Hbm Hw) |].
      intros tr o (_ & Hx).
      exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
    right. split.
    + apply trace_equiv_iff_omni. intro tr. cbn.
      rewrite (cat_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code Hsource Hbm Hw tr).
      rewrite (cat_obs_iff_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code Htarget Hbm Hw tr).
      reflexivity.
    + apply bh_errors_iff. cbn.
      apply (cat_no_error_run_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code Htarget Hbm Hw).
  - (* no reader, signal 13 open: both runs die at their first write *)
    split.
    { cbn [img_segments].
      eapply coexec_conseq;
        [apply exec_coexec;
         exact (cat_kill_omni_run_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code
                  Hsource Hne Hfs Hr Hm) |].
      intros tr o (_ & Ho). apply never_errors_covered.
      destruct o; [exact (fun h => h) | destruct Ho]. }
    right. split.
    + apply trace_equiv_iff_omni. intro tr. cbn.
      rewrite (cat_kill_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code
                 Hsource Hne Hfs Hr Hm tr).
      rewrite (cat_kill_obs_iff_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code
                 Htarget Hne Hft Hr Hm tr).
      reflexivity.
    + apply bh_errors_iff. cbn.
      apply (cat_kill_no_error_run_te target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code
               Htarget Hne Hft Hr Hm).
Qed.

(* [comment removed for export] *)
Lemma cat_strong_equiv_te :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp,
  to_wexit (run_segments source_segs inp rsp rmb)
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) bufs code ->
  to_wexit (run_segments target_segs inp asp amb)
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) bufs code ->
  bufs_modeled bufs ->
  cat_launch (run_segments source_segs inp rsp rmb)
             (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp)
             (run_segments target_segs inp asp amb)
             (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp)
             bufs inp ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp
    Hsource Htarget Hbm Hl.
  destruct (cat_launch_cases _ _ _ _ _ _ Hl) as [Hw | (Hne & Hr & Hm & Hfs & Hft)].
  - split.
    { apply no_error_run_modeled.
      apply (cat_no_error_run_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code Hsource Hbm Hw). }
    right. split.
    + intro tr. cbn.
      rewrite (cat_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code Hsource Hbm Hw tr).
      rewrite (cat_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp bufs code Htarget Hbm Hw tr).
      reflexivity.
    + cbn. apply (cat_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp bufs code Htarget Hbm Hw).
  - split.
    { apply no_error_run_modeled.
      apply (cat_kill_no_error_run_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
               Hsource Hne Hfs Hr Hm). }
    right. split.
    + intro tr. cbn.
      rewrite (cat_kill_obs_iff_te source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
                 Hsource Hne Hfs Hr Hm tr).
      rewrite (cat_kill_obs_iff_te target_segs apc aph asp abrk amb arnd alim inp bufs code
                 Htarget Hne Hft Hr Hm tr).
      reflexivity.
    + cbn. apply (cat_kill_no_error_run_te target_segs apc aph asp abrk amb arnd alim inp bufs code
                    Htarget Hne Hft Hr Hm).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fdchan (fd ch : word) (model : Model) : Prop :=
  fd_lookup (m_fds model) fd = Some (FdChannel ch) /\ w_is0 ch = false
  /\ m_channel_reader model = true.

Lemma fd1chan_fdchan : forall model,
  fd1chan model -> fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model.
Proof.
  intros model [H Hr]. split; [exact H | split; [reflexivity | exact Hr]].
Qed.

Lemma init_model_fdchan2 : forall reserved brk0 mb sp lim inp,
  in_channel_reader inp = true ->
  fdchan (Z_to_bv 64 2) (Z_to_bv 64 2) (init_model reserved brk0 mb sp lim inp).
Proof.
  intros reserved brk0 mb sp lim inp Hr.
  split; [reflexivity | split; [reflexivity | exact Hr]].
Qed.

Lemma write_ch_check_n : forall segs ms x8 model fd ch buf n,
  fdchan fd ch model ->
  fd32 fd = fd ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* see [write1_check_n] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  check_write (sys_input segs ms x8)
    (fd32 (ms_gpr ms 0)) (ms_gpr ms 1) (ms_gpr ms 2)
    (with_copyins [(ms_gpr ms 1, n)]
      (mkEffect (len_word (firstn n buf)) [] [])) model
    = CheckOk model (map (WriteEv ch) (firstn n buf)).
Proof.
  intros segs ms x8 model fd ch buf n [Hfd [Hch Hrdr]] H32 Hno Hg Hr Hok Hcnt Hn1 Hn2.
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  pose proof (word_unsigned_range (ms_gpr ms 2)) as Hcr.
  assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
    by (unfold buf_modeled in Hcnt; lia).
  assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
    by (apply rw_range_in_range; exact Hcw).
  unfold check_write.
  rewrite Hg, H32, Hfd, Hch. cbv beta iota.
  rewrite Hmc. cbv beta iota.
  assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
  rewrite Hc. cbv beta iota. cbv zeta.
  rewrite Hok. cbn [negb]. cbv beta iota.
  rewrite Hrdr. change (negb true) with false. cbv beta iota.
  rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb).
  assert (Hg0 : Nat.eqb (length buf) 0 = false) by (apply Nat.eqb_neq; lia).
  rewrite Hg0. cbv beta iota. unfold with_copyins; cbn.
  assert (Hlenf : Z.of_nat (length (firstn n buf)) = Z.of_nat n)
    by (rewrite length_firstn; lia).
  assert (Hru : bv_unsigned (len_word (firstn n buf)) = Z.of_nat n).
  { rewrite (len_word_unsigned (firstn n buf));
      [exact Hlenf | rewrite Hlenf; lia]. }
  rewrite ?Hru.
  assert (Hg1 : (1 <=? Z.of_nat n)%Z = true) by (apply Z.leb_le; lia).
  assert (Hg2 : (Z.of_nat n <=? Z.of_nat (length buf))%Z = true)
    by (apply Z.leb_le; lia).
  rewrite ?Hg1, ?Hg2. cbn [andb].
  rewrite ?Nat2Z.id, bv_eqb_refl, Nat.eqb_refl. reflexivity.
Qed.

Lemma write_ch_ok_n : forall segs ms x8 model fd ch buf n,
  fdchan fd ch model -> fd32 fd = fd ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= n)%nat -> (n <= length buf)%nat ->
  syscall_spec (sys_input segs ms x8) model
    (Ok (with_copyins [(ms_gpr ms 1, n)]
          (mkEffect (len_word (firstn n buf)) [] [])) model
        (map (WriteEv ch) (firstn n buf))).
Proof.
  intros segs ms x8 model fd ch buf n Hfdc H32 Hno Hg Hr Hok Hcnt Hn1 Hn2.
  apply (proj2 (syscall_spec_write _ _ _ _ _ Hno)).
  apply check_write_sound_ok. eapply write_ch_check_n; eassumption.
Qed.

Lemma write_ch_ok_inv : forall segs ms x8 model fd ch eff model' evs buf,
  fdchan fd ch model -> fd32 fd = fd ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  (* see [write1_ok_inv] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  (1 <= length buf)%nat ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    eff = with_copyins [(ms_gpr ms 1, n)]
            (mkEffect (len_word (firstn n buf)) [] []) /\ model' = model /\
    evs = map (WriteEv ch) (firstn n buf).
Proof.
  intros segs ms x8 model fd ch eff model' evs buf Hfdc H32 Hno Hg Hr Hok Hnb Hspec.
  destruct Hfdc as [Hfd [Hch Hrdr]].
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply check_write_complete_ok in Hspec.
  unfold check_write in Hspec.
  rewrite Hg, H32, Hfd, Hch in Hspec. cbv beta iota in Hspec.
  (* see [write1_ok_inv]: [Ok] rules the guard out *)
  destruct (negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)));
    cbv beta iota in Hspec; [discriminate|].
  assert (Hc : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
  rewrite Hc in Hspec. cbv beta iota zeta in Hspec.
  rewrite Hok in Hspec. cbn [negb] in Hspec. cbv beta iota in Hspec.
  rewrite Hrdr in Hspec. change (negb true) with false in Hspec.
  cbv beta iota in Hspec.
  (* the source the transfer sees is the CLAMPED prefix of the range the
     call named -- [buf] itself for every count under [MAX_RW_COUNT], and
     a prefix of it above, which the gate above admits at an in-range
     buffer *)
  rewrite (write_source_prefix _ _ _ _ Hrb) in Hspec.
  pose proof (rw_count_clamp_range (ms_gpr ms 2)) as Hcl.
  set (c := Z.to_nat (rw_count_clamp (ms_gpr ms 2))) in *.
  assert (Hcpos : (1 <= c)%nat)
    by (unfold c, rw_count_clamp, MAX_RW_COUNT in *; lia).
  assert (Hfl : length (firstn c buf) = Nat.min c (length buf))
    by apply length_firstn.
  assert (Hg0 : Nat.eqb (length (firstn c buf)) 0 = false)
    by (rewrite Hfl; apply Nat.eqb_neq; lia).
  rewrite Hg0 in Hspec. cbv beta iota in Hspec.
  destruct eff as [ret ws zs us cs copyins]; destruct ws as [|? ?];
    destruct zs as [|? ?]; destruct us as [|? ?];
      destruct cs as [|? ?]; try discriminate.
  destruct ((1 <=? bv_unsigned ret)%Z
            && (bv_unsigned ret <=? Z.of_nat (length (firstn c buf)))%Z) eqn:Hgr;
    [|discriminate].
  destruct (access_ranges_eqb copyins [(ms_gpr ms 1, Z.to_nat (bv_unsigned ret))])
    eqn:Hreads; [|discriminate].
  inversion Hspec; clear Hspec; subst.
  apply andb_true_iff in Hgr as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  rewrite Hfl in H2.
  apply access_ranges_eqb_eq in Hreads. subst copyins.
  exists (Z.to_nat (bv_unsigned ret)).
  assert (Hff : firstn (Z.to_nat (bv_unsigned ret)) (firstn c buf)
                = firstn (Z.to_nat (bv_unsigned ret)) buf)
    by (rewrite firstn_firstn; f_equal; lia).
  rewrite Hff.
  assert (Hlw : len_word (firstn (Z.to_nat (bv_unsigned ret)) buf) = ret)
    by (apply len_word_firstn_ret; lia).
  rewrite Hlw. repeat split; try reflexivity; lia.
Qed.

Lemma write_ch_no_unmodeled : forall segs ms x8 model fd ch buf,
  fdchan fd ch model -> fd32 fd = fd ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  buf_modeled buf ->
  (* see [write1_no_unmodeled]: a zero [count] is genuinely unmodeled *)
  (1 <= length buf)%nat ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled.
Proof.
  intros segs ms x8 model fd ch buf [Hfd [Hch Hrdr]] H32 Hno Hg Hr Hcnt Hnb Hspec.
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some buf).
  { rewrite in_mem_sys_input, read_bytes_map_read_byte. exact Hr. }
  pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
  assert (Hcw : (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z)
    by (unfold buf_modeled in Hcnt; lia).
  assert (Hmc : negb (modeled_rw_range (ms_gpr ms 1) (ms_gpr ms 2)) = false)
    by (apply rw_range_in_range; exact Hcw).
  apply (proj1 (syscall_spec_write _ _ _ _ _ Hno)) in Hspec.
  apply (check_write_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  unfold check_write in Hspec.
  rewrite Hg, H32, Hfd, Hch in Hspec. cbv beta iota in Hspec.
  rewrite Hmc in Hspec. cbv beta iota in Hspec.
  destruct (w_is0 (ms_gpr ms 2)) eqn:Hc; try rewrite Hc in Hspec.
  { exfalso.
    assert (Hc0 : w_is0 (ms_gpr ms 2) = false) by (apply w_is0_pos; lia).
    congruence. }
  (* [vfs_write]'s [access_ok]: a refused range is -EFAULT, an answer *)
  destruct (negb (access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)))).
  { now apply check_ret_only_no_unmodeled in Hspec. }
  rewrite Hrdr in Hspec. change (negb true) with false in Hspec.
  cbv beta iota in Hspec.
  rewrite (write_source_of_rw _ _ _ Hcw), (readable_bytes_full _ _ _ _ Hrb)
    in Hspec.
  destruct (length buf =? 0)%nat eqn:Hz; try rewrite Hz in Hspec.
  { now apply check_ret_only_no_unmodeled in Hspec. }
  discriminate Hspec.
Qed.

Section WithSegsCh.
Variable segs : list Segment.
Variable fd ch : word.

(* [comment removed for export] *)
Inductive to_wexit_ch : machine_state -> list (list byte) -> word -> Prop :=
| twc_exit : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    to_wexit_ch ms [] (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
| twc_write : forall ms x8 buf bufs code,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = fd ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
    (1 <= length buf)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
       to_wexit_ch (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) bufs code) ->
    to_wexit_ch ms (buf :: bufs) code
| twc_step : forall ms ms' bufs code,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wexit_ch ms' bufs code ->
    to_wexit_ch ms bufs code.

Lemma msteps_to_wexit_ch : forall ms ms' bufs code,
  msteps segs ms ms' -> to_wexit_ch ms' bufs code -> to_wexit_ch ms bufs code.
Proof.
  intros ms ms' bufs code H; induction H; [auto|].
  intro Hw. eapply twc_step; eauto.
Qed.

Hypothesis Hfd32 : fd32 fd = fd.

Lemma sstep_write_ch_inv : forall ms model x8 buf evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  ms_gpr ms 0 = fd ->
  ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some buf ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  buf_modeled buf ->
  (1 <= length buf)%nat ->
  sstep segs (mkCfg ms model) evs st ->
  exists n, (1 <= n)%nat /\ (n <= length buf)%nat /\
    evs = map (WriteEv ch) (firstn n buf) /\
    st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n buf)))) model).
Proof.
  intros ms model x8 buf evs st Hh Hlazy Hfdc Hsvc Hno Hg Hr Hok Hcnt Hnb Hss.
  revert Hg Hfdc. inversion Hss; subst; intros Hg Hfdc; try congruence.
  - match goal with
    | H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf Hfdc Hfd32 Hno Hg Hr Hok Hnb H3)
        as (n & Hn1 & Hn2 & Heff & Hm & Hevs);
      subst eff model' evs0; exists n
    end.
    match goal with
    | Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
        rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
        inversion Hmat; subst model''
    end.
    rewrite apply_effect_copyins_no_write. repeat split; auto.
  - exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf
                  Hfdc Hfd32 Hno Hg Hr Hok Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
      discriminate
    end.
  - exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf Hfdc Hfd32 Hno Hg Hr Hok Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite Hh in H6; discriminate
    end.
  - (* sstep_killed: the write arm hands back the model it was given, and
       a running model is not a killed one *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (write_ch_ok_inv segs ms x8 model fd ch eff model' evs0 buf Hfdc Hfd32 Hno Hg Hr Hok Hnb H3)
        as (n & _ & _ & _ & Hm & _);
      subst model'; rewrite (m_killed_of_m_halted_none model Hh) in H6;
      discriminate
    end.
  - exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x, H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      apply (write_ch_no_unmodeled segs ms x8 model fd ch buf Hfdc Hfd32 Hno Hg Hr Hcnt Hnb H3)
    end.
Qed.

End WithSegsCh.

(* [comment removed for export] *)
Lemma to_wexit_ch_1 : forall segs ms bufs code,
  to_wexit segs ms bufs code ->
  to_wexit_ch segs (Z_to_bv 64 1) ms bufs code.
Proof.
  intros segs ms bufs code H; induction H.
  - eapply twc_exit; eassumption.
  - eapply twc_write; eassumption.
  - eapply twc_step; eassumption.
Qed.

Lemma wevents_ch_1 : forall bufs, wevents_ch (Z_to_bv 64 1) bufs = wevents bufs.
Proof.
  induction bufs as [|b bs IH]; cbn [wevents_ch wevents]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.
End CatSim.

(* [comment removed for export] *)
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require PropExec.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
Module CatExec.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Vdso LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ExitSim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec CatSim.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.

Section WithFP.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ms_read_bytes_aux_rdn : forall segs ms n addr,
  ms_rom ms = seg_rom segs ->
  ms_read_bytes_aux ms addr n = rdn segs (ms_mem ms) addr n.
Proof.
  intros segs ms n. induction n as [|n IH]; intros addr Hrom; [reflexivity|].
  cbn [ms_read_bytes_aux rdn]. unfold ms_read_byte. rewrite Hrom.
  destruct (ms_mem ms addr) as [b|].
  - rewrite IH by exact Hrom. reflexivity.
  - unfold seg_rom. destruct (memory_read segs addr 1) as [[|b r]|];
      try reflexivity; rewrite IH by exact Hrom; reflexivity.
Qed.

Lemma ms_read_bytes_rdn : forall segs ms addr len,
  ms_rom ms = seg_rom segs ->
  ms_read_bytes ms addr len = rdn segs (ms_mem ms) addr (word_to_nat len).
Proof. intros. unfold ms_read_bytes. apply ms_read_bytes_aux_rdn; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint wbytes (m : word -> option byte) (addr : word) (bs : list byte)
    : word -> option byte :=
  match bs with
  | [] => m
  | b :: rest => wbytes (fun a => if bv_eqb a addr then Some b else m a) (addr+1) rest
  end.

(* [comment removed for export] *)
Lemma wbytes_above : forall bs m (addr x : word),
  (bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbytes m addr bs x = m x.
Proof.
  induction bs as [|b rest IH]; intros m addr x Hle; [reflexivity|].
  cbn [wbytes length] in *.
  pose proof (u64_range x) as Hx.
  assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z)
    by (apply u_add1; lia).
  rewrite IH by lia.
  cbv beta.
  assert (Hne : bv_eqb x addr = false)
    by (unfold bv_eqb; apply Z.eqb_neq; lia).
  rewrite Hne. reflexivity.
Qed.

Lemma rdn_wbytes_disjoint : forall segs bs m (addr a : word) n,
  (bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof.
  intros segs bs m addr a n Hle Hnw. apply rdn_ext; [exact Hnw|].
  intros x Hx. apply wbytes_above. lia.
Qed.

(* [comment removed for export] *)
Lemma wbytes_below : forall bs m (addr x : word),
  (bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
  (bv_unsigned x < bv_unsigned addr)%Z ->
  wbytes m addr bs x = m x.
Proof.
  induction bs as [|b rest IH]; intros m addr x Hnw Hlt; [reflexivity|].
  cbn [wbytes length] in *.
  assert (Hne : bv_eqb x addr = false)
    by (unfold bv_eqb; apply Z.eqb_neq; lia).
  destruct rest as [|b' rest'].
  - cbn [wbytes]. rewrite Hne. reflexivity.
  - assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z)
      by (apply u_add1; cbn [length] in Hnw; lia).
    rewrite IH by lia.
    cbv beta. rewrite Hne. reflexivity.
Qed.

Lemma rdn_wbytes_below : forall segs bs m (addr a : word) n,
  (bv_unsigned a + Z.of_nat n <= bv_unsigned addr)%Z ->
  (bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
  rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof.
  intros segs bs m addr a n Hle Hnw.
  pose proof (u64_range addr) as Ha.
  apply rdn_ext; [lia|].
  intros x Hx. apply wbytes_below; [exact Hnw|lia].
Qed.

(* [comment removed for export] *)
Lemma rdn_wbytes_out : forall segs bs m (addr a : word) n,
  (bv_unsigned a + Z.of_nat n <= bv_unsigned addr
   \/ bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  (bv_unsigned addr + Z.of_nat (length bs) <= 2^64)%Z ->
  rdn segs (wbytes m addr bs) a n = rdn segs m a n.
Proof.
  intros segs bs m addr a n [Hb|Hd] Hnw Hnw'.
  - apply rdn_wbytes_below; [exact Hb | exact Hnw'].
  - apply rdn_wbytes_disjoint; [exact Hd | exact Hnw].
Qed.

Lemma length_Z_to_le_bytes : forall n z, length (Z_to_le_bytes n z) = n.
Proof.
  induction n as [|n IH]; intro z; [reflexivity|].
  cbn [Z_to_le_bytes length]. rewrite IH. reflexivity.
Qed.

Lemma length_N_to_le_bytes : forall n (v : word), length (word_to_le_bytes n v) = n.
Proof. intros. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.

(* [comment removed for export] *)
Lemma write_to_mem_wbytes : forall bs (m : word -> option byte) (addr : word),
  write_to_mem m addr bs = wbytes m addr bs.
Proof.
  induction bs as [|b rest IH]; intros m addr; [reflexivity|].
  cbn [write_to_mem wbytes]. apply IH.
Qed.

(* [comment removed for export] *)
Lemma step_sd : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 8%nat = true ->
  exists bs, length bs = 8%nat /\
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm)) bs) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  exists (word_to_le_bytes 8 (getr regs rs2)). split; [reflexivity|].
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma launch_string_base_arith : forall v inp mbase (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (bv_unsigned sp
   + Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp)
                 (in_envp inp))
   + Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                 (in_execfn inp))
   + 8 <= bv_unsigned (ed_top draw))%Z.
Proof.
  intros v inp mbase sp brk draw Hlaunch.
  cbn [entry_launch_ok_va] in Hlaunch.
  destruct Hlaunch as (_ & (_ & _ & Hhi) & _).
  unfold launch_sp_hi, align_down16 in Hhi.
  pose proof (Z.mod_pos_bound
    (bv_unsigned (ed_top draw) - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                   (in_execfn inp))) 16 ltac:(lia)).
  lia.
Qed.

Lemma launch_sp_le_ed_top : forall v inp mbase (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (bv_unsigned sp <= bv_unsigned (ed_top draw))%Z.
Proof.
  intros v inp mbase sp brk draw Hlaunch.
  pose proof (launch_string_base_arith v inp mbase sp brk draw Hlaunch).
  pose proof (Nat2Z.is_nonneg
    (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  pose proof (Nat2Z.is_nonneg
    (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
  lia.
Qed.

Lemma stack_max_size_val : stack_max_size = 8388608%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma wrap_mem_below :
  forall v inp mbase ph entry (sp brk : word) draw (addr : word),
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (bv_unsigned addr < bv_unsigned sp - stack_max_size)%Z ->
  wrap_mem inp mbase ph entry sp draw addr = None.
Proof.
  intros v inp mbase ph entry sp brk draw addr Hlau Hlt.
  pose proof stack_max_size_val as Hsms.
  pose proof (launch_sp_le_ed_top v inp mbase sp brk draw Hlau) as Htop.
  pose proof (Z.le_max_l (bv_unsigned (ed_top draw) - stack_max_size)
                (bv_unsigned mbase + stack_guard_gap_bytes (in_kernel inp))) as Hmax.
  unfold wrap_mem, stack_to_mem.
  assert (Hsp : Z.leb (bv_unsigned sp) (bv_unsigned addr) = false)
    by (apply Z.leb_gt; lia).
  rewrite Hsp.
  assert (Hgate : Z.leb (stack_window_lo (in_kernel inp) mbase draw)
                        (bv_unsigned addr) = false)
    by (apply Z.leb_gt; unfold stack_window_lo in *; lia).
  rewrite Hgate. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma flat_map_app' : forall {A B : Type} (f : A -> list B) l1 l2,
  flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
  intros A B f l1 l2. induction l1 as [|x xs IH]; cbn; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Lemma skipn_nth : forall {A : Type} (l : list A) k d, (k < length l)%nat ->
  skipn k l = nth k l d :: skipn (S k) l.
Proof.
  induction l as [|x xs IH]; intros k d Hk; [cbn in Hk; lia|].
  destruct k as [|k']; [reflexivity|].
  cbn [skipn nth]. apply IH. cbn in Hk; lia.
Qed.

Lemma flat_map_split : forall {A B : Type} (f : A -> list B) l k d, (k < length l)%nat ->
  flat_map f l = flat_map f (firstn k l) ++ f (nth k l d) ++ flat_map f (skipn (S k) l).
Proof.
  intros A B f l k d Hk.
  rewrite <- (firstn_skipn k l) at 1.
  rewrite flat_map_app'.
  rewrite (skipn_nth l k d Hk). reflexivity.
Qed.

Lemma flat_map_le8_decomp : forall (l : list word) k, (k < length l)%nat ->
  flat_map word_le8 l =
  flat_map word_le8 (firstn k l) ++ word_le8 (nth k l (Z_to_bv 64 0))
    ++ flat_map word_le8 (skipn (S k) l).
Proof. intros l k Hk. apply (flat_map_split word_le8 l k (Z_to_bv 64 0) Hk). Qed.

Lemma flatten_strings_decomp : forall strs k, (k < length strs)%nat ->
  flatten_strings strs =
  flatten_strings (firstn k strs) ++ (nth k strs [] ++ [Z_to_bv 8 0])
    ++ flatten_strings (skipn (S k) strs).
Proof.
  intros strs k Hk.
  apply (flat_map_split (fun s => s ++ [Z_to_bv 8 0]) strs k [] Hk).
Qed.

Lemma total_arg_bytes_cons : forall s l,
  total_arg_bytes_nat (s :: l) = (length s + 1 + total_arg_bytes_nat l)%nat.
Proof. reflexivity. Qed.

Lemma total_arg_bytes_firstn_le : forall k l,
  (total_arg_bytes_nat (firstn k l) <= total_arg_bytes_nat l)%nat.
Proof.
  induction k as [|k IH]; intros l.
  - change (total_arg_bytes_nat (firstn 0 l)) with 0%nat. lia.
  - destruct l as [|s rest]; [cbn; lia|].
    cbn [firstn]. rewrite !total_arg_bytes_cons. specialize (IH rest). lia.
Qed.

Lemma total_arg_bytes_firstn_within : forall (l : list (list byte)) k,
  (k < length l)%nat ->
  (total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1
   <= total_arg_bytes_nat l)%nat.
Proof.
  intros l. induction l as [|s rest IH]; intros k Hk; [cbn in Hk; lia|].
  destruct k as [|k'].
  - cbn [firstn nth]. change (total_arg_bytes_nat []) with 0%nat.
    rewrite total_arg_bytes_cons. lia.
  - cbn [firstn nth]. rewrite !total_arg_bytes_cons.
    specialize (IH k' ltac:(cbn in Hk; lia)). lia.
Qed.

Lemma natN_le : forall n m, (n <= m)%nat -> (N.of_nat n <= N.of_nat m)%N.
Proof. intros n m H. lia. Qed.

(* [comment removed for export] *)
Lemma of_nat_131071 : Z.of_nat 131071 = 131071%Z.
Proof. vm_compute. reflexivity. Qed.
Lemma of_nat_2097152 : Z.of_nat 2097152 = 2097152%Z.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_Z2bv_lt : forall z, (0 <= z)%Z -> (z < 2 ^ 64)%Z ->
  bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z H0 H1. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  apply Z.mod_small. lia.
Qed.

Lemma word_add_nat_Z2bv : forall (a : word) (n : nat),
  a + nat_to_word n = Z_to_bv 64 (bv_unsigned a + Z.of_nat n).
Proof.
  intros a n. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zplus_mod_idemp_r.
Qed.

Lemma word_sub_nat : forall (a : word) (n : nat),
  a - nat_to_word n = Z_to_bv 64 (bv_unsigned a - Z.of_nat n).
Proof.
  intros a n. apply bv_eq. unfold nat_to_word.
  rewrite bv_sub_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  apply Zminus_mod_idemp_r.
Qed.

Definition cat_struct_size (av ev : list (list byte)) : nat :=
  (8 * block_items av ev)%nat.

Definition cat_string_base (top : word) (av ev : list (list byte))
    (execfn : list byte) : word :=
  string_base_addr top av ev execfn.

Definition cat_env_base (top : word) (av ev : list (list byte))
    (execfn : list byte) : word :=
  cat_string_base top av ev execfn + nat_to_word (total_arg_bytes_nat av).

(* [comment removed for export] *)
Definition cat_argv_ptr (top : word) (av ev : list (list byte))
    (execfn : list byte) (k : nat) : word :=
  nth k (fst (string_addrs (cat_string_base top av ev execfn) av)) (Z_to_bv 64 0).

Definition cat_string_off (rseq : bool) (sp top : word)
    (av ev : list (list byte)) (execfn : list byte) : nat :=
  (block_head_size rseq av ev + block_pad_len rseq sp top av ev execfn)%nat.

Lemma nth_string_addrs : forall strs (base : word) k, (k < length strs)%nat ->
  nth k (fst (string_addrs base strs)) (Z_to_bv 64 0)
  = base + nat_to_word (total_arg_bytes_nat (firstn k strs)).
Proof.
  induction strs as [|s rest IH]; intros base k Hk; [cbn in Hk; lia|].
  rewrite string_addrs_fst_structure.
  destruct k as [|k'].
  - cbn [nth firstn]. change (total_arg_bytes_nat []) with 0%nat.
    rewrite word_add_0. reflexivity.
  - cbn [nth]. rewrite (IH (base + len_word s + 1) k' ltac:(cbn in Hk; lia)).
    cbn [firstn]. rewrite total_arg_bytes_cons.
    rewrite len_word_nat, word1_nat, !nat_to_word_add_merge.
    f_equal. f_equal. lia.
Qed.

Lemma cat_argv_ptr_offset : forall top av ev execfn k, (k < length av)%nat ->
  cat_argv_ptr top av ev execfn k
  = cat_string_base top av ev execfn
    + nat_to_word (total_arg_bytes_nat (firstn k av)).
Proof. intros. unfold cat_argv_ptr. apply nth_string_addrs. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma u_cat_string_base : forall v inp mbase (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  bv_unsigned (cat_string_base (ed_top draw) (in_argv inp) (in_envp inp)
                 (in_execfn inp))
  = (bv_unsigned (ed_top draw) - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                   (in_execfn inp)))%Z.
Proof.
  intros v inp mbase sp brk draw Hlaunch.
  pose proof (launch_string_base_arith v inp mbase sp brk draw Hlaunch) as HA.
  pose proof (u64_range sp). pose proof (u64_range (ed_top draw)).
  pose proof (Nat2Z.is_nonneg
    (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  unfold cat_string_base, string_base_addr. rewrite word_sub_nat.
  assert (Hz : (0 <= bv_unsigned (ed_top draw)
                     - Z.of_nat (8 + launch_string_bytes (in_argv inp)
                                       (in_envp inp) (in_execfn inp))
                < 2 ^ 64)%Z).
  { rewrite Nat2Z.inj_add. change (Z.of_nat 8) with 8%Z. lia. }
  rewrite (u_Z2bv_lt _ (proj1 Hz) (proj2 Hz)).
  rewrite Nat2Z.inj_add. change (Z.of_nat 8) with 8%Z. lia.
Qed.

Lemma cat_string_base_offset : forall v inp mbase (sp brk : word) draw,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  cat_string_base (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp)
  = sp + nat_to_word (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
                        (in_argv inp) (in_envp inp) (in_execfn inp)).
Proof.
  intros v inp mbase sp brk draw Hlaunch.
  pose proof (launch_string_base_arith v inp mbase sp brk draw Hlaunch) as HA.
  pose proof (u_cat_string_base v inp mbase sp brk draw Hlaunch) as Hu.
  pose proof (u64_range sp). pose proof (u64_range (ed_top draw)).
  apply bv_eq. rewrite Hu, word_add_nat_Z2bv.
  unfold cat_string_off, block_pad_len.
  rewrite u_Z2bv_lt
    by (rewrite Nat2Z.inj_add; rewrite Z2Nat.id by lia; lia).
  rewrite Nat2Z.inj_add. rewrite Z2Nat.id by lia. lia.
Qed.

Definition cat_struct_prefix (top : word) (av ev : list (list byte))
    (execfn : list byte) : list byte :=
  word_le8 (len_word av)
  ++ flat_map word_le8 (fst (string_addrs (cat_string_base top av ev execfn) av))
  ++ word_le8 (Z_to_bv 64 0)
  ++ flat_map word_le8 (fst (string_addrs (cat_env_base top av ev execfn) ev))
  ++ word_le8 (Z_to_bv 64 0).

Lemma length_cat_struct_prefix : forall top av ev execfn,
  length (cat_struct_prefix top av ev execfn) = cat_struct_size av ev.
Proof.
  intros top av ev execfn.
  unfold cat_struct_prefix, cat_struct_size, block_items.
  rewrite !length_app, !length_flat_map_le8, !length_string_addrs_fst,
    !length_n_to_le_8.
  lia.
Qed.

(* [comment removed for export] *)
Definition cat_block_head (la : LaunchAuxv) (ph : PhdrInfo)
    (entry sp top : word) (av ev : list (list byte)) (execfn : list byte)
    (uid gid hw : word) (draw : EntryDraw) : list byte :=
  block_below_random la ph entry sp top av ev execfn uid gid hw
  ++ at_random_bytes (ed_random draw)
  ++ repeat (Z_to_bv 8 0) (block_pad_len (la_rseq la) sp top av ev execfn).

Lemma length_cat_block_head :
  forall la ph entry sp top av ev execfn uid gid hw draw,
  length (cat_block_head la ph entry sp top av ev execfn uid gid hw draw)
  = cat_string_off (la_rseq la) sp top av ev execfn.
Proof.
  intros la ph entry sp top av ev execfn uid gid hw draw.
  unfold cat_block_head, block_below_random, cat_string_off. cbv zeta.
  rewrite (string_addrs_pair av). cbv beta iota.
  rewrite (string_addrs_pair ev). cbv beta iota.
  rewrite !length_app, !repeat_length, !length_flat_map_le8,
    !length_string_addrs_fst, length_auxv_bytes, length_at_random_bytes,
    !length_n_to_le_8.
  unfold block_head_size, block_items. lia.
Qed.

Lemma bsb_argv_prefix : forall inp mbase ph entry (sp : word) draw, exists tail,
  entry_stack_image inp mbase ph entry sp draw =
    word_le8 (len_word (in_argv inp))
    ++ flat_map word_le8
         (fst (string_addrs
                 (cat_string_base (ed_top draw) (in_argv inp) (in_envp inp)
                    (in_execfn inp))
                 (in_argv inp)))
    ++ tail.
Proof.
  intros inp mbase ph entry sp draw.
  rewrite entry_stack_image_block.
  unfold build_stack_bytes, cat_string_base. cbv zeta.
  rewrite (string_addrs_pair (in_argv inp)). cbv beta iota.
  rewrite (string_addrs_pair (in_envp inp)). cbv beta iota.
  eexists. rewrite <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bsb_ptr_k : forall inp mbase ph entry (sp : word) draw k,
  (k < length (in_argv inp))%nat -> exists post,
  entry_stack_image inp mbase ph entry sp draw =
    (word_le8 (len_word (in_argv inp))
      ++ flat_map word_le8
           (firstn k (fst (string_addrs
                             (cat_string_base (ed_top draw) (in_argv inp)
                                (in_envp inp) (in_execfn inp))
                             (in_argv inp)))))
    ++ word_le8 (nth k (fst (string_addrs
                               (cat_string_base (ed_top draw) (in_argv inp)
                                  (in_envp inp) (in_execfn inp))
                               (in_argv inp))) (Z_to_bv 64 0))
    ++ post.
Proof.
  intros inp mbase ph entry sp draw k Hk.
  destruct (bsb_argv_prefix inp mbase ph entry sp draw) as [tail E].
  assert (Hk' : (k < length (fst (string_addrs
                   (cat_string_base (ed_top draw) (in_argv inp) (in_envp inp)
                      (in_execfn inp)) (in_argv inp))))%nat)
    by (rewrite length_string_addrs_fst; exact Hk).
  rewrite (flat_map_le8_decomp _ k Hk') in E.
  eexists. rewrite E. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma read_argv_ptr_k : forall segs inp mbase ph entry (sp : word) draw k,
  (k < length (in_argv inp))%nat ->
  (bv_unsigned sp
   + Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw))
     < 2 ^ 64)%Z ->
  rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
      (sp + nat_to_word (8 + 8 * k)) 8%nat
  = Some (word_le8 (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                      (in_execfn inp) k)).
Proof.
  intros segs inp mbase ph entry sp draw k Hk Hnw.
  destruct (bsb_ptr_k inp mbase ph entry sp draw k Hk) as [post E].
  pose proof (read_at_offset_image segs inp mbase ph entry sp draw
    (word_le8 (len_word (in_argv inp))
      ++ flat_map word_le8
           (firstn k (fst (string_addrs
                             (cat_string_base (ed_top draw) (in_argv inp)
                                (in_envp inp) (in_execfn inp))
                             (in_argv inp)))))
    (word_le8 (nth k (fst (string_addrs
                             (cat_string_base (ed_top draw) (in_argv inp)
                                (in_envp inp) (in_execfn inp))
                             (in_argv inp))) (Z_to_bv 64 0)))
    post 8%nat E (length_n_to_le_8 _) Hnw) as H'.
  assert (Hlen : length (word_le8 (len_word (in_argv inp))
      ++ flat_map word_le8
           (firstn k (fst (string_addrs
                             (cat_string_base (ed_top draw) (in_argv inp)
                                (in_envp inp) (in_execfn inp))
                             (in_argv inp)))))
    = (8 + 8 * k)%nat).
  { rewrite length_app, length_n_to_le_8, length_flat_map_le8, firstn_length_le;
      [reflexivity | rewrite length_string_addrs_fst; lia]. }
  rewrite Hlen in H'.
  rewrite H'. unfold cat_argv_ptr. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma bsb_strings_split : forall inp mbase ph entry (sp : word) draw, exists tail,
  entry_stack_image inp mbase ph entry sp draw
  = cat_block_head (launch_auxv inp sp mbase) ph entry sp (ed_top draw)
      (in_argv inp) (in_envp inp) (in_execfn inp)
      (in_uid inp) (in_gid inp) (in_hwcap inp) draw
    ++ flatten_strings (in_argv inp) ++ tail.
Proof.
  intros inp mbase ph entry sp draw.
  rewrite entry_stack_image_block, build_stack_bytes_split_random.
  unfold cat_block_head, block_above_random.
  eexists. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma bsb_byte_k : forall inp mbase ph entry (sp : word) draw k,
  (k < length (in_argv inp))%nat -> exists pre post,
  entry_stack_image inp mbase ph entry sp draw
  = pre ++ (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]) ++ post
  /\ length pre
     = (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
          (in_argv inp) (in_envp inp) (in_execfn inp)
        + total_arg_bytes_nat (firstn k (in_argv inp)))%nat.
Proof.
  intros inp mbase ph entry sp draw k Hk.
  destruct (bsb_strings_split inp mbase ph entry sp draw) as [tail E].
  rewrite (flatten_strings_decomp (in_argv inp) k Hk) in E.
  exists (cat_block_head (launch_auxv inp sp mbase) ph entry sp (ed_top draw)
            (in_argv inp) (in_envp inp) (in_execfn inp)
            (in_uid inp) (in_gid inp) (in_hwcap inp) draw
          ++ flatten_strings (firstn k (in_argv inp))).
  eexists.
  split.
  - rewrite E. rewrite <- !app_assoc. reflexivity.
  - rewrite length_app, length_cat_block_head, length_flatten_strings.
    reflexivity.
Qed.

Lemma read_argv_byte_k :
  forall v segs inp mbase ph entry (sp brk : word) draw k j,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (k < length (in_argv inp))%nat ->
  (j <= length (nth k (in_argv inp) []))%nat ->
  rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
      (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k
       + nat_to_word j) 1%nat
  = Some [nth j (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)].
Proof.
  intros v segs inp mbase ph entry sp brk draw k j Hlaunch Hk Hj.
  pose proof (entry_stack_image_no_wrap v inp mbase ph entry sp brk draw Hlaunch)
    as Hnw.
  destruct (bsb_byte_k inp mbase ph entry sp draw k Hk) as [pre [post [E Hlen]]].
  pose proof (read_byte_at_image segs inp mbase ph entry sp draw
    pre (nth k (in_argv inp) [] ++ [Z_to_bv 8 0]) post j E) as H'.
  rewrite Hlen in H'.
  replace (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
             (in_execfn inp) k + nat_to_word j)
    with (sp + nat_to_word
                 (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
                    (in_argv inp) (in_envp inp) (in_execfn inp)
                  + total_arg_bytes_nat (firstn k (in_argv inp)) + j)).
  2:{ rewrite (cat_argv_ptr_offset _ _ _ _ k Hk),
        (cat_string_base_offset v inp mbase sp brk draw Hlaunch).
      rewrite !nat_to_word_add_merge. f_equal. f_equal. lia. }
  apply H'; [rewrite length_app; cbn [length]; lia | exact Hnw].
Qed.

Lemma read_argv_str_k :
  forall v segs inp mbase ph entry (sp brk : word) draw k,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (k < length (in_argv inp))%nat ->
  rdn segs (stack_to_mem sp (entry_stack_image inp mbase ph entry sp draw))
      (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k)
      (length (nth k (in_argv inp) []))
  = Some (nth k (in_argv inp) []).
Proof.
  intros v segs inp mbase ph entry sp brk draw k Hlaunch Hk.
  pose proof (entry_stack_image_no_wrap v inp mbase ph entry sp brk draw Hlaunch)
    as Hnw.
  destruct (bsb_byte_k inp mbase ph entry sp draw k Hk) as [pre [post [E Hlen]]].
  pose proof (read_at_offset_image segs inp mbase ph entry sp draw
    pre (nth k (in_argv inp) []) ([Z_to_bv 8 0] ++ post)
    (length (nth k (in_argv inp) []))) as H.
  rewrite Hlen in H.
  replace (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
             (in_execfn inp) k)
    with (sp + nat_to_word
                 (cat_string_off (kb_rseq (in_kernel inp)) sp (ed_top draw)
                    (in_argv inp) (in_envp inp) (in_execfn inp)
                  + total_arg_bytes_nat (firstn k (in_argv inp)))).
  2:{ rewrite (cat_argv_ptr_offset _ _ _ _ k Hk),
        (cat_string_base_offset v inp mbase sp brk draw Hlaunch).
      rewrite nat_to_word_add_merge. reflexivity. }
  apply H; [ | reflexivity | exact Hnw].
  rewrite E. rewrite <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition byte_at (s : list byte) (k : nat) : byte :=
  nth k (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0).

Lemma nth_lt_byte_at : forall s j, (j < length s)%nat ->
  byte_at s j = nth j s (Z_to_bv 8 0).
Proof. intros s j Hj. unfold byte_at. apply app_nth1. exact Hj. Qed.

Lemma byte_at_len : forall s, byte_at s (length s) = Z_to_bv 8 0.
Proof.
  intros s. unfold byte_at. rewrite app_nth2 by lia.
  rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma byte_at_nz : forall s j, ~ In (Z_to_bv 8 0) s -> (j < length s)%nat ->
  byte_at s j <> Z_to_bv 8 0.
Proof.
  intros s j Hnz Hj Hc.
  apply Hnz. rewrite <- Hc. rewrite nth_lt_byte_at by exact Hj.
  apply nth_In. exact Hj.
Qed.

(* [comment removed for export] *)
Lemma byte_at_bound : forall s j, (bv_unsigned (byte_at s j) < 256)%Z.
Proof. intros s j. unfold byte_at. apply nth_app0_bound. Qed.

Lemma valid_argv_len : forall av, valid_argv av ->
  (Z.of_nat (length av) <= 1024)%Z.
Proof. intros av [Hlen _]. lia. Qed.

Lemma valid_argv_nonempty : forall av, valid_argv av -> (1 <= length av)%nat.
Proof. intros av [Hlen _]. lia. Qed.

Lemma valid_argv_str_len : forall av k, valid_argv av -> (k < length av)%nat ->
  (Z.of_nat (length (nth k av [])) <= 131071)%Z.
Proof.
  intros av k [_ [_ [Hstr _]]] Hk.
  rewrite Forall_forall in Hstr.
  specialize (Hstr _ (nth_In av [] Hk)). exact Hstr.
Qed.

Lemma valid_argv_str_nz : forall av k, valid_argv av -> (k < length av)%nat ->
  ~ In (Z_to_bv 8 0) (nth k av []).
Proof.
  intros av k [_ [_ [_ [Hnz _]]]] Hk.
  rewrite Forall_forall in Hnz. apply Hnz. apply nth_In. exact Hk.
Qed.

(* [comment removed for export] *)
Lemma valid_argv_str_plain : forall av k, valid_argv av ->
  (S k < length av)%nat ->
  path_eqb (nth (S k) av []) dot_path = false ->
  openat_plain_name (nth (S k) av []) = true.
Proof.
  intros av k [_ [_ [_ [_ Hpl]]]] Hk Hdot.
  assert (Hnth : nth (S k) av [] = nth k (tl av) []).
  { destruct av as [|a av']; [cbn in Hk; lia | reflexivity]. }
  assert (Hk' : (k < length (tl av))%nat).
  { destruct av as [|a av']; cbn in *; lia. }
  rewrite Forall_forall in Hpl.
  destruct (Hpl _ (nth_In (tl av) [] Hk')) as [Hsl Hdd].
  rewrite Hnth in Hdot |- *.
  unfold openat_plain_name, path_is_dirref.
  rewrite Hdot, Hsl, Hdd. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma valid_argv_str_bytes : forall av k, valid_argv av -> (k < length av)%nat ->
  Forall (fun b : byte => (bv_unsigned b < 256)%Z) (nth k av []).
Proof.
  intros av k _ _. apply Forall_forall. intros b _. apply u8_range.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma v_addi_pred : forall x : word, v_addi (x + 1) (-1) = x.
Proof.
  intro x. apply bv_eq. unfold v_addi.
  rewrite Z_to_bv_unsigned, bv_add_unsigned.
  change (bv_unsigned (1 : word)) with 1%Z.
  rewrite bv_wrap_add_idemp_l.
  replace (bv_unsigned x + 1 + -1)%Z with (bv_unsigned x) by lia.
  apply bv_wrap_bv_unsigned.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
    : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some (Z_to_bv 64 64);
     ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}.

(* [comment removed for export] *)
Lemma adv_set : forall regs pc sv mem rom v,
  advance_past_svc (set_gpr0
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
       ms_mem := mem; ms_rom := rom |} v)
  = mkst (regupd regs 10 v) (v_addi pc 4) mem rom.
Proof.
  intros regs pc sv mem rom v.
  unfold advance_past_svc, set_gpr0, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tw_write_gen : forall segs regs pc mem rom buf bufs code,
  ms_gpr (pend regs pc mem rom) 0 = Z_to_bv 64 1 ->
  ms_read_bytes (pend regs pc mem rom)
    (ms_gpr (pend regs pc mem rom) 1) (ms_gpr (pend regs pc mem rom) 2) = Some buf ->
  (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
  access_okb (ms_gpr (pend regs pc mem rom) 1)
    (bv_unsigned (ms_gpr (pend regs pc mem rom) 2)) = true ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     to_wexit segs (mkst (regupd regs 10 (len_word (firstn n buf)))
                         (v_addi pc 4) mem rom) bufs code) ->
  to_wexit segs (pend regs pc mem rom) (buf :: bufs) code.
Proof.
  intros segs regs pc mem rom buf bufs code Hg0 Hr Hok Hnb Hcont.
  eapply tw_write;
    [reflexivity | reflexivity | exact Hg0 | exact Hr | exact Hok | exact Hnb | ].
  intros n Hn1 Hn2. unfold pend. rewrite adv_set. apply Hcont; assumption.
Qed.

(* [comment removed for export] *)
Lemma tw_exit0 : forall segs ms x8,
  ms_svc_pending ms = Some x8 -> is_exit_no x8 ->
  ms_gpr ms 0 = Z_to_bv 64 0 ->
  to_wexit segs ms [] (Z_to_bv 64 0).
Proof.
  intros segs ms x8 Hsvc Hex Hg0.
  assert (Hc : bv_and (ms_gpr ms 0) (Z_to_bv 64 255) = Z_to_bv 64 0).
  { rewrite Hg0. apply bv_eq.
    rewrite bv_and_unsigned, !Z_to_bv_unsigned. reflexivity. }
  rewrite <- Hc. eapply tw_exit; eassumption.
Qed.

(* [comment removed for export] *)
Lemma tw_write_rec : forall segs regs pc mem rom buf bufs code,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = Z_to_bv 64 1 ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some buf ->
  access_okb (reg_get regs 11) (bv_unsigned (reg_get regs 12)) = true ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     to_wexit segs (mkst (regupd regs 10 (len_word (firstn n buf)))
                         (v_addi pc 4) mem rom) bufs code) ->
  to_wexit segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |}
    (buf :: bufs) code.
Proof.
  intros segs regs pc mem rom buf bufs code H17 H10 Hr Hok Hnb Hcont.
  eapply tw_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_0. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_1, arg_reg_2. exact Hr.
  - unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_1, arg_reg_2. exact Hok.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. apply Hcont; assumption.
Qed.

(* [comment removed for export] *)
Lemma tw_exit_rec : forall segs regs pc mem rom,
  bv_unsigned (getr regs 17) = 93%Z ->
  reg_get regs 10 = Z_to_bv 64 0 ->
  to_wexit segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |} [] (Z_to_bv 64 0).
Proof.
  intros segs regs pc mem rom H17 H10.
  eapply tw_exit0.
  - cbn [ms_svc_pending]. reflexivity.
  - left. exact H17.
  - unfold ms_gpr. cbn [ms_regs].
    rewrite arg_reg_0. exact H10.
Qed.
End WithFP.
End CatExec.

(* [comment removed for export] *)
Module SeqExec.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Vdso LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ExitSim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec CatSim CatExec.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition v_jalr (x : word) (imm : Z) : word := Z_to_bv 64 (jalr_tgtZ x imm).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_jal_link : forall segs regs pc mem rom w rd (imm : bv 21),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal rd imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
                  (btgt pc (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rd imm Hfetch Hecall Hdecode.
  step_pipeline Hfetch Hecall Hdecode.
  destruct (is_x0 rd); cbv beta iota;
    rewrite ?b_npc4, ?b_addsext;
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_jalr : forall segs regs pc mem rom w rd rs1 (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (v_addi pc 4))
                  (v_jalr (getr regs rs1) (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 imm Hf He Hd.
  exact (step_jalr_gen segs regs pc mem rom w rd rs1 imm Hf He Hd).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_sd_val : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 8%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes 8 (getr regs rs2))) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc4.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_sd_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 8%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 8 v)) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
  rewrite (step_sd_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, Hv. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

(* [comment removed for export] *)
Lemma step_addi_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_ADD rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_addi (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_addi segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_add_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_ADD rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_add (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_add segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_sub_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Op ALU_SUB rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_sub (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_sub segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_lui_at : forall segs regs pc mem rom w rd (imm : bv 20) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Lui rd imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_lui (Z.shiftl (bv_signed imm) 12) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd imm v Hf He Hd Hrd Hv.
  rewrite (step_lui segs regs pc mem rom w rd imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_auipc_at : forall segs regs pc mem rom w rd (imm : bv 20) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Auipc rd imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_auipc pc (Z.shiftl (bv_signed imm) 12) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd imm v Hf He Hd Hrd Hv.
  rewrite (step_auipc segs regs pc mem rom w rd imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_addiw_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm32 rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_addiw (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_addiw segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_sltiu_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_SLTU rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_sltiu (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_sltiu segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_xori_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_XOR rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_xori (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_xori segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_mul_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_MUL rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_mul (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv.
  rewrite (step_mul segs regs pc mem rom w rd rs1 rs2 Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_andi_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_AND rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_andi (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_andi segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_ori_at : forall segs regs pc mem rom w rd rs (imm : bv 12) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (OpImm ALU_OR rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_ori (getr regs rs) (bv_signed imm) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm v Hf He Hd Hrd Hv.
  rewrite (step_ori segs regs pc mem rom w rd rs imm Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_slli_at : forall segs regs pc mem rom w rd rs (sh : bv 6) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm ALU_SLL rd rs sh, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_slli (getr regs rs) (bv_unsigned sh) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv.
  rewrite (step_slli segs regs pc mem rom w rd rs sh Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_srli_at : forall segs regs pc mem rom w rd rs (sh : bv 6) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm ALU_SRL rd rs sh, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_srli (getr regs rs) (bv_unsigned sh) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv.
  rewrite (PropExec.step_srli segs regs pc mem rom w rd rs sh Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

Lemma step_srai_at : forall segs regs pc mem rom w rd rs (sh : bv 6) v,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (ShiftImm ALU_SRA rd rs sh, 4%Z) ->
  bv_eqb rd 0 = false ->
  v_srai (getr regs rs) (bv_unsigned sh) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs sh v Hf He Hd Hrd Hv.
  rewrite (step_srai segs regs pc mem rom w rd rs sh Hf He Hd).
  rewrite Hrd, Hv. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rdn_wbytes_hit : forall segs bs m (a : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
  rdn segs (wbytes m a bs) a (length bs) = Some bs.
Proof.
  intros segs bs. induction bs as [|b rest IH]; intros m a Hnw; [reflexivity|].
  cbn [length] in Hnw |- *.
  change (wbytes m a (b :: rest))
    with (wbytes (fun x => if bv_eqb x a then Some b else m x) (a+1) rest).
  set (m' := fun x : word => if bv_eqb x a then Some b else m x).
  cbn [rdn].
  destruct rest as [|b' rest'].
  - cbn [wbytes rdn]. unfold m'. rewrite bv_eqb_refl. reflexivity.
  - assert (Hu1 : bv_unsigned (a+1) = (bv_unsigned a + 1)%Z)
      by (apply u_add1; cbn [length] in Hnw; lia).
    assert (Hread : wbytes m' (a+1) (b' :: rest') a = Some b).
    { rewrite (wbytes_below (b' :: rest') m' (a+1) a);
        [ unfold m'; rewrite bv_eqb_refl; reflexivity
        | cbn [length] in *; lia
        | pose proof (u64_range a); lia ]. }
    rewrite Hread.
    rewrite (IH m' (a+1)) by (cbn [length] in *; lia).
    reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rdn_wbytes_hit8 : forall segs m (a v : word),
  (bv_unsigned a + 8 <= 2^64)%Z ->
  rdn segs (wbytes m a (word_to_le_bytes 8 v)) a 8%nat = Some (word_to_le_bytes 8 v).
Proof.
  intros segs m a v Hnw.
  pose proof (rdn_wbytes_hit segs (word_to_le_bytes 8 v) m a) as H.
  rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
Qed.

(* [comment removed for export] *)
Lemma bytes_le_to_Z_8 : forall v : word,
  bytes_le_to_Z (word_to_le_bytes 8 v) = bv_unsigned v.
Proof.
  intro v. rewrite bytes_le_N.
  change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z.
  apply Z.mod_small. apply u64_range.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma c_ltu_ltb : forall x y : word,
  c_ltu x y = (bv_unsigned x <? bv_unsigned y)%Z.
Proof. reflexivity. Qed.

Lemma v_addiw_small : forall (x : word) imm,
  (0 <= bv_unsigned x + imm)%Z -> (bv_unsigned x + imm < 2^31)%Z -> (0 <= imm)%Z ->
  bv_unsigned (v_addiw x imm) = (bv_unsigned x + imm)%Z.
Proof.
  intros x imm Hlo Hhi _. unfold v_addiw.
  rewrite Z_to_bv_unsigned.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

(* [comment removed for export] *)
Lemma v_addiw_id : forall x : word, (bv_unsigned x < 2^31)%Z -> v_addiw x 0 = x.
Proof.
  intros x Hx. apply bv_eq.
  rewrite (v_addiw_small x 0); [lia | pose proof (u64_range x); lia .. ].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma land_255_small : forall c : word, (bv_unsigned c < 256)%Z ->
  bv_and c (Z_to_bv 64 255) = c.
Proof.
  intros c Hc. apply bv_eq.
  rewrite bv_and_unsigned, Z_to_bv_unsigned.
  change (bv_wrap 64 255) with (Z.ones 8).
  rewrite Z.land_ones by lia.
  apply Z.mod_small.
  pose proof (u64_range c). change (2^8)%Z with 256%Z. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma tw_write_ret : forall segs regs pc mem rom buf bufs code,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = Z_to_bv 64 1 ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some buf ->
  (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
  access_okb (reg_get regs 11) (bv_unsigned (reg_get regs 12)) = true ->
  (1 <= length buf)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length buf)%nat ->
     to_wexit segs (mkst (regupd regs 10 (len_word (firstn n buf)))
                         (v_addi pc 4) mem rom) bufs code) ->
  to_wexit segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |}
    (buf :: bufs) code.
Proof.
  intros segs regs pc mem rom buf bufs code H17 H10 Hr Hok Hnb Hcont.
  eapply tw_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_0. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_1, arg_reg_2. exact Hr.
  - unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_1, arg_reg_2. exact Hok.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. apply Hcont; assumption.
Qed.

(* [comment removed for export] *)
Lemma tw_exit_coden : forall segs regs pc mem rom (c : word),
  bv_unsigned (getr regs 17) = 93%Z ->
  reg_get regs 10 = c -> (bv_unsigned c < 256)%Z ->
  to_wexit segs {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                   ms_mem := mem; ms_rom := rom |} [] c.
Proof.
  intros segs regs pc mem rom c H17 H10 Hc.
  assert (Hg : bv_and (ms_gpr {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                                 ms_svc_pending := Some (getr regs 17); ms_resv := None; ms_fcsr := fp_csr;
                                 ms_mem := mem; ms_rom := rom |} 0)
                      (Z_to_bv 64 255) = c).
  { unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_0, H10.
    apply land_255_small. exact Hc. }
  rewrite <- Hg.
  eapply tw_exit.
  - cbn [ms_svc_pending]. reflexivity.
  - left. exact H17.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition argv_layout_slack : Z := 4300000%Z.

(* [comment removed for export] *)

Local Lemma argv_struct_arith : forall a e : Z,
  (0 <= a)%Z -> (a <= 1024)%Z -> (0 <= e)%Z -> (e <= 256)%Z ->
  (8 + (a + 1) * 8 + (e + 1) * 8 + 160 <= 10424)%Z.
Proof. intros. lia. Qed.

Local Lemma argv_sum_arith : forall a b : Z,
  (a <= 10424)%Z -> (b <= 2097152)%Z -> (a + b <= 2107576)%Z.
Proof. intros. lia. Qed.

Local Lemma argv_mod_arith : forall s m : Z,
  (0 <= s)%Z -> (0 <= m)%Z -> (m <= 2107576)%Z -> (s + 4300000 < 2^64)%Z ->
  (0 <= s + m < 2^64)%Z.
Proof. intros. lia. Qed.

Local Lemma argv_final_arith : forall s m l : Z,
  (0 <= m)%Z -> (0 <= l)%Z -> (m <= 2107576)%Z -> (l <= 131071)%Z ->
  (s + 4300000 < 2^64)%Z ->
  (s <= s + m)%Z /\ (s + m + l + 1 < 2^64)%Z.
Proof. intros. lia. Qed.

Lemma argv_ptr_bounds : forall v inp mbase (sp brk : word) draw k,
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (k < length (in_argv inp))%nat ->
  (bv_unsigned sp
   <= bv_unsigned (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                     (in_execfn inp) k))%Z
  /\ (bv_unsigned (cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp)
                     (in_execfn inp) k)
      + Z.of_nat (length (nth k (in_argv inp) [])) + 1 < 2 ^ 64)%Z.
Proof.
  intros v inp mbase sp brk draw k Hlaunch Hk.
  pose proof (launch_string_base_arith v inp mbase sp brk draw Hlaunch) as HA.
  pose proof (u_cat_string_base v inp mbase sp brk draw Hlaunch) as Hu.
  pose proof (u64_range sp). pose proof (u64_range (ed_top draw)).
  pose proof (Nat2Z.is_nonneg
    (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  pose proof (Nat2Z.is_nonneg
    (total_arg_bytes_nat (firstn k (in_argv inp)))).
  assert (Hstr : (Z.of_nat (total_arg_bytes_nat (firstn k (in_argv inp)))
                  + Z.of_nat (length (nth k (in_argv inp) [])) + 1
                  <= Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                 (in_execfn inp)))%Z).
  { pose proof (total_arg_bytes_firstn_within (in_argv inp) k Hk) as Hw.
    unfold launch_string_bytes. rewrite length_flatten_strings.
    pose proof (Nat2Z.is_nonneg (length (flatten_strings (in_envp inp)))).
    pose proof (Nat2Z.is_nonneg (length (in_execfn inp))).
    lia. }
  rewrite (cat_argv_ptr_offset _ _ _ _ k Hk), word_add_nat_Z2bv, Hu.
  rewrite u_Z2bv_lt by lia.
  split; lia.
Qed.

(* [comment removed for export] *)
Lemma step_jalr_x0 : forall segs regs pc mem rom w rs1 (imm : bv 12) tgt,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr 0 rs1 imm, 4%Z) ->
  getr regs rs1 = tgt ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_jalr tgt (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rs1 imm tgt Hf He Hd Ht.
  rewrite (step_jalr segs regs pc mem rom w 0 rs1 imm Hf He Hd).
  rewrite Ht. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_jalr_link : forall segs regs pc mem rom w rd rs1 (imm : bv 12) tgt,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Jalr rd rs1 imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  getr regs rs1 = tgt ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd (v_addi pc 4)) (v_jalr tgt (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 imm tgt Hf He Hd Hrd Ht.
  rewrite (step_jalr segs regs pc mem rom w rd rs1 imm Hf He Hd).
  rewrite Ht, Hrd. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma getr_zero : forall regs, getr regs 0 = Z_to_bv 64 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
End WithFP1.
Ltac reg_neq_tac :=
  let Hc := fresh "Hc" in intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate Hc.

Section WithFP2.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP2.
Ltac getr_resolve :=
  repeat first [ rewrite getr_same by reg_neq_tac
               | rewrite getr_other by reg_neq_tac ];
  rewrite ?getr_zero;
  rewrite ?getr_nz by reg_neq_tac.

Section WithFP3.
Context {fx : FPState}.

(* [comment removed for export] *)
End WithFP3.
Ltac regupd_resolve :=
  repeat first [ rewrite regupd_same
               | rewrite regupd_other by reg_neq_tac ].

Section WithFP4.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition v_divu (x y : word) : word :=
  Z_to_bv 64 (bv_unsigned x / bv_unsigned y).
Definition v_remu (x y : word) : word :=
  Z_to_bv 64 (bv_unsigned x mod bv_unsigned y).

(* [comment removed for export] *)
Lemma m_divu : forall a b : word, (bv_unsigned b <> 0)%Z ->
  mul_div M_DIVU a b = v_divu a b.
Proof.
  intros a b Hb.
  change (mul_div M_DIVU a b)
    with (if (bv_unsigned b =? 0)%Z then Z_to_bv 64 (-1) else bv_divu a b).
  rewrite (proj2 (Z.eqb_neq _ _) Hb).
  apply bv_eq. unfold v_divu.
  rewrite bv_divu_unsigned, Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  change (bv_modulus 64) with (2^64)%Z.
  pose proof (u64_range a). pose proof (u64_range b).
  split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with (bv_unsigned a); [|lia].
  apply Z.div_le_upper_bound; nia.
Qed.

Lemma m_remu : forall a b : word, (bv_unsigned b <> 0)%Z ->
  mul_div M_REMU a b = v_remu a b.
Proof.
  intros a b Hb.
  change (mul_div M_REMU a b)
    with (if (bv_unsigned b =? 0)%Z then a else bv_modu a b).
  rewrite (proj2 (Z.eqb_neq _ _) Hb).
  apply bv_eq. unfold v_remu.
  rewrite bv_modu_unsigned, Z_to_bv_unsigned.
  symmetry; apply bv_wrap_small.
  change (bv_modulus 64) with (2^64)%Z.
  pose proof (u64_range a). pose proof (u64_range b).
  pose proof (Z.mod_pos_bound (bv_unsigned a) (bv_unsigned b) ltac:(lia)).
  lia.
Qed.

Lemma step_divu : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_DIVU rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs2) <> 0)%Z ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (v_divu (getr regs rs1) (getr regs rs2)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 Hf He Hd Hnz.
  erewrite step_mul_gen by eassumption.
  rewrite m_divu by exact Hnz. reflexivity.
Qed.

Lemma step_remu : forall segs regs pc mem rom w rd rs1 rs2,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Mul M_REMU rd rs1 rs2, 4%Z) ->
  (bv_unsigned (getr regs rs2) <> 0)%Z ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (if bv_eqb rd 0 then regs
                   else regupd regs rd (v_remu (getr regs rs1) (getr regs rs2)))
                  (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs1 rs2 Hf He Hd Hnz.
  erewrite step_mul_gen by eassumption.
  rewrite m_remu by exact Hnz. reflexivity.
Qed.

Lemma step_lw_zero : forall segs regs pc mem rom w rd rs (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
  bv_eqb rd 0 = false ->
  rdn segs mem (v_addi (getr regs rs) (bv_signed imm)) 4%nat
    = Some [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst (regupd regs rd (Z_to_bv 64 0)) (v_addi pc 4) mem rom).
Proof.
  intros segs regs pc mem rom w rd rs imm Hf He Hd Hrd Hr.
  assert (Hval : sext 64 (bv_extract 0 32 (le_bytes_to_word
                    [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]))
                 = Z_to_bv 64 0)
    by (apply bv_eq; reflexivity).
  step_pipeline Hf He Hd.
  rewrite bv_eqb0_is_x0 in Hrd.
  unfold getr in Hr; rewrite ?bv_eqb0_is_x0 in Hr.
  rewrite ov_rdn, b_addsext, Hr; cbv beta iota.
  rewrite Hval, Hrd; cbv beta iota.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_sb : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 1%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes 1 (getr regs rs2))) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  assert (Hsb : forall u : word,
    Z_to_le_bytes 1%nat (bv_unsigned (bv_extract 0 8 u)) = word_to_le_bytes 1 u).
  { intro u. unfold word_to_le_bytes. cbn [Z_to_le_bytes].
    f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, bv_extract_unsigned, Z.shiftr_0_r.
    apply bv_wrap_bv_wrap. lia. }
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, Hsb, b_npc4.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_sb256 : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 1%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes 1 (getr regs rs2))) rom).
Proof. exact step_sb. Qed.

(* [comment removed for export] *)
Lemma N_to_le_bytes_1_small : forall v : word,
  word_to_le_bytes 1 v = [Z_to_bv 8 (bv_unsigned v)].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma Zmod_pow2_div8 : forall z m, (8 <= m)%Z ->
  ((z mod 2^m) / 2^8)%Z = ((z / 2^8) mod 2^(m-8))%Z.
Proof.
  intros z m Hm.
  rewrite <- !Z.shiftr_div_pow2 by lia.
  apply Z.bits_inj'; intros i Hi.
  rewrite !Z.shiftr_spec by lia.
  destruct (Z.lt_ge_cases i (m - 8)) as [Hlt|Hge].
  - rewrite !Z.mod_pow2_bits_low by lia.
    rewrite Z.shiftr_spec by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma Z_to_le_bytes_wrap : forall n (m : N) z,
  (8 * Z.of_nat n <= Z.of_N m)%Z ->
  Z_to_le_bytes n (bv_wrap m z) = Z_to_le_bytes n z.
Proof.
  induction n as [|n IH]; intros m z Hm; cbn [Z_to_le_bytes]; [reflexivity|].
  f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned.
    apply bv_wrap_bv_wrap. lia.
  - replace (Z.shiftr (bv_wrap m z) 8) with (bv_wrap (m - 8) (Z.shiftr z 8)).
    + apply IH. lia.
    + unfold bv_wrap, bv_modulus.
      rewrite !Z.shiftr_div_pow2 by lia.
      rewrite Zmod_pow2_div8 by lia.
      do 2 f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma store_bytes_low16 : forall u : word,
  Z_to_le_bytes 2 (bv_unsigned (bv_extract 0 16 u)) = word_to_le_bytes 2 u.
Proof.
  intro u. unfold word_to_le_bytes.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  apply Z_to_le_bytes_wrap. lia.
Qed.

(* [comment removed for export] *)
Lemma store_bytes_low32 : forall u : word,
  Z_to_le_bytes 4 (bv_unsigned (low32 u)) = word_to_le_bytes 4 u.
Proof.
  intro u. unfold low32, word_to_le_bytes.
  rewrite bv_extract_unsigned, Z.shiftr_0_r.
  apply Z_to_le_bytes_wrap. lia.
Qed.

(* [comment removed for export] *)
Lemma step_sw_val : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 4%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes 4 (getr regs rs2))) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, store_bytes_low32, b_npc4.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_sw_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 4%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 4 v)) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
  rewrite (step_sw_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, Hv. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

(* [comment removed for export] *)
Lemma step_sh_val : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ2 rs1 rs2 imm, 4%Z) ->
  RiscvSemantics.store_ok segs mem
    (v_addi (getr regs rs1) (bv_signed imm)) 2%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4)
    (wbytes mem (v_addi (getr regs rs1) (bv_signed imm))
            (word_to_le_bytes 2 (getr regs rs2))) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, store_bytes_low16, b_npc4.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma step_sh_at : forall segs regs pc mem rom w (rs1 rs2 : reg) (imm : bv 12) (a v : word),
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Store SZ2 rs1 rs2 imm, 4%Z) ->
  v_addi (getr regs rs1) (bv_signed imm) = a ->
  getr regs rs2 = v ->
  RiscvSemantics.store_ok segs mem a 2%nat = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) =
  MachineOk (mkst regs (v_addi pc 4) (wbytes mem a (word_to_le_bytes 2 v)) rom).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm a v Hf He Hd Ha Hv Hok.
  rewrite (step_sh_val segs regs pc mem rom w rs1 rs2 imm Hf He Hd).
  - rewrite Ha, Hv. reflexivity.
  - rewrite Ha. exact Hok.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma v_divu_small : forall x y : word, (0 < bv_unsigned y)%Z ->
  bv_unsigned (v_divu x y) = (bv_unsigned x / bv_unsigned y)%Z.
Proof.
  intros x y Hy. unfold v_divu.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 64) with (2^64)%Z.
  pose proof (u64_range x). pose proof (u64_range y).
  split; [apply Z.div_pos; lia|].
  apply Z.le_lt_trans with (bv_unsigned x); [|lia].
  apply Z.div_le_upper_bound; nia.
Qed.

Lemma v_remu_small : forall x y : word, (0 < bv_unsigned y)%Z ->
  bv_unsigned (v_remu x y) = (bv_unsigned x mod bv_unsigned y)%Z.
Proof.
  intros x y Hy. unfold v_remu.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  change (bv_modulus 64) with (2^64)%Z.
  pose proof (u64_range y).
  pose proof (Z.mod_pos_bound (bv_unsigned x) (bv_unsigned y) Hy).
  lia.
Qed.

Lemma v_subw_small : forall x y : word,
  (bv_unsigned y <= bv_unsigned x)%Z ->
  (bv_unsigned x - bv_unsigned y < 2^31)%Z ->
  bv_unsigned (v_subw x y) = (bv_unsigned x - bv_unsigned y)%Z.
Proof.
  intros x y Hle Hlt. unfold v_subw.
  rewrite Z_to_bv_unsigned.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31)%Z; lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia.
Qed.

Lemma land_d48 : forall d : Z, (0 <= d)%Z -> (d < 16)%Z -> Z.land d 48 = 0%Z.
Proof.
  intros d Hd0 Hd. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 4) as [Hi4|Hi4].
  - replace 48%Z with (Z.shiftl 3 4)%Z by reflexivity.
    rewrite Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite (Z_testbit_high 4 d i) by lia. reflexivity.
Qed.

Lemma lor_small_add : forall d : Z, (0 <= d)%Z -> (d < 16)%Z ->
  Z.lor d 48 = (d + 48)%Z.
Proof.
  intros d Hd0 Hd.
  rewrite <- Z.lxor_lor by (apply land_d48; assumption).
  rewrite <- Z.add_nocarry_lxor by (apply land_d48; assumption).
  reflexivity.
Qed.

Lemma v_ori_lor : forall d : word, (bv_unsigned d < 16)%Z ->
  v_ori d 48 = Z_to_bv 64 (bv_unsigned d + 48).
Proof.
  intros d Hd. unfold v_ori.
  change (bv_wrap 64 48) with 48%Z.
  f_equal. apply lor_small_add; [apply u64_range | exact Hd].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_app : forall segs mem n1 n2 (a : word) bs1 bs2,
  rdn segs mem a n1 = Some bs1 ->
  rdn segs mem (a + nat_to_word n1) n2 = Some bs2 ->
  rdn segs mem a (n1 + n2)%nat = Some (bs1 ++ bs2).
Proof.
  intros segs mem n1. induction n1 as [|n1 IH]; intros n2 a bs1 bs2 H1 H2.
  - cbn in H1. injection H1 as <-. cbn [app].
    rewrite word_add_0 in H2. exact H2.
  - change (S n1 + n2)%nat with (S (n1 + n2))%nat.
    cbn [rdn] in H1 |- *.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
      as [b|]; [|discriminate].
    destruct (rdn segs mem (a+1) n1) as [rest|] eqn:Er; [|discriminate].
    injection H1 as <-.
    rewrite (IH n2 (a+1) rest bs2 Er); [reflexivity|].
    replace (a + 1 + nat_to_word n1) with (a + nat_to_word (S n1))
      by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
    exact H2.
Qed.

Lemma rdn_nth : forall segs mem n (a : word) bs j,
  rdn segs mem a n = Some bs -> (j < n)%nat ->
  rdn segs mem (a + nat_to_word j) 1%nat = Some [nth j bs (Z_to_bv 8 0)].
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs j H Hj; [lia|].
  cbn [rdn] in H.
  destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
    as [b|] eqn:Eb; [|discriminate].
  destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
  injection H as <-.
  destruct j as [|j].
  - rewrite word_add_0. cbn [rdn nth]. rewrite Eb. reflexivity.
  - cbn [nth].
    replace (a + nat_to_word (S j)) with (a + 1 + nat_to_word j)
      by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
    apply (IH (a+1) rest j Er). lia.
Qed.

(* [comment removed for export] *)
Lemma v_addi_m : forall (x : word) (k : Z),
  (k <= bv_unsigned x)%Z -> (0 < k)%Z ->
  v_addi x (- k) = Z_to_bv 64 (bv_unsigned x - k).
Proof. intros x k _ _. reflexivity. Qed.

Lemma rdn_skipn : forall segs mem n (a : word) bs k,
  rdn segs mem a n = Some bs -> (k <= n)%nat ->
  rdn segs mem (a + nat_to_word k) (n - k)%nat = Some (skipn k bs).
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs k H Hk.
  - assert (k = 0)%nat by lia. subst k. rewrite word_add_0.
    cbn in H |- *. injection H as <-. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
      as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct k as [|k].
    + rewrite word_add_0. cbn [Nat.sub skipn rdn]. rewrite Eb, Er. reflexivity.
    + cbn [Nat.sub skipn].
      replace (a + nat_to_word (S k)) with (a + 1 + nat_to_word k)
        by (rewrite word1_nat, nat_to_word_add_merge; reflexivity).
      apply (IH (a+1) rest k Er). lia.
Qed.

Lemma rdn_firstn : forall segs mem n (a : word) bs k,
  rdn segs mem a n = Some bs -> (k <= n)%nat ->
  rdn segs mem a k = Some (firstn k bs).
Proof.
  intros segs mem n. induction n as [|n IH]; intros a bs k H Hk.
  - assert (k = 0)%nat by lia. subst k. cbn in H |- *.
    injection H as <-. reflexivity.
  - cbn [rdn] in H.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end)
      as [b|] eqn:Eb; [|discriminate].
    destruct (rdn segs mem (a+1) n) as [rest|] eqn:Er; [|discriminate].
    injection H as <-.
    destruct k as [|k]; [reflexivity|].
    cbn [rdn firstn]. rewrite Eb.
    rewrite (IH (a+1) rest k Er) by lia. reflexivity.
Qed.
End WithFP4.
End SeqExec.

(* [comment removed for export] *)
Module StreamExec.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Vdso LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ExitSim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.PropExec CatSim CatExec SeqExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma v_lui_4096 : v_lui 4096 = Z_to_bv 64 4096.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma c_lts_0_0 : c_lts (Z_to_bv 64 0) (Z_to_bv 64 0) = false.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma write_to_mem_below : forall data mem (buf a : word),
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  (bv_unsigned a < bv_unsigned buf)%Z ->
  write_to_mem mem buf data a = mem a.
Proof.
  intros data mem buf a Hnw Ha.
  rewrite write_to_mem_wbytes. apply wbytes_below; assumption.
Qed.

(* [comment removed for export] *)
Lemma write_to_mem_above : forall data mem (buf a : word),
  (bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned a)%Z ->
  write_to_mem mem buf data a = mem a.
Proof.
  intros data mem buf a Ha.
  rewrite write_to_mem_wbytes. apply wbytes_above; assumption.
Qed.

(* [comment removed for export] *)
Lemma rdn_wtm_out : forall segs data m (buf a : word) n,
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  ((bv_unsigned buf + Z.of_nat (length data) <= bv_unsigned a)%Z \/
   (bv_unsigned a + Z.of_nat n <= bv_unsigned buf)%Z) ->
  rdn segs (write_to_mem m buf data) a n = rdn segs m a n.
Proof.
  intros segs data m buf a n Hna Hnb Hd. apply rdn_ext; [exact Hna|].
  intros x Hx. destruct Hd as [Hd | Hd].
  - apply write_to_mem_above. lia.
  - apply write_to_mem_below; [exact Hnb | lia].
Qed.

(* [comment removed for export] *)
Lemma rdn_write_to_mem : forall segs data mem (buf : word),
  (bv_unsigned buf + Z.of_nat (length data) <= 2^64)%Z ->
  rdn segs (write_to_mem mem buf data) buf (length data) = Some data.
Proof.
  intros segs data mem buf Hnw.
  rewrite write_to_mem_wbytes. apply rdn_wbytes_hit. exact Hnw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma adv_apply_write : forall regs pc sv mem rom ret buf data,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
       ms_mem := mem; ms_rom := rom |}
    (mkEffect ret [(buf, data)] []))
  = mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof.
  intros regs pc sv mem rom ret buf data.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
       apply_zeros apply_unmaps apply_writes].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma adv_apply_delivered : forall regs pc sv mem rom ret buf data,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := sv; ms_resv := None; ms_fcsr := fp_csr;
       ms_mem := mem; ms_rom := rom |}
    (mkEffect ret (delivered_writes buf data) []))
  = mkst (regupd regs 10 ret) (v_addi pc 4) (write_to_mem mem buf data) rom.
Proof.
  intros regs pc sv mem rom ret buf data.
  destruct data as [|b rest]; [|apply adv_apply_write].
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies
       apply_zeros apply_unmaps apply_writes
       delivered_writes write_to_mem].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.
End WithFP1.
End StreamExec.

(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ExitSim.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ExitSim.SimInv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ExitSim.
Import CatSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import PropExec.
Import SeqExec.
Import CatExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.
Section WithFP1.
Context {fx : FPState}.


(* [comment removed for export] *)
Lemma fd32_1 : fd32 (Z_to_bv 64 1) = Z_to_bv 64 1.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma fd32_2 : fd32 (Z_to_bv 64 2) = Z_to_bv 64 2.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma u_len_word : forall {A} (l : list A), (Z.of_nat (length l) < 2^64)%Z ->
  bv_unsigned (len_word l) = Z.of_nat (length l).
Proof.
  intros A l H. unfold len_word. apply Z_to_bv_small.
  unfold bv_modulus. change (Z.of_N 64) with 64%Z. lia.
Qed.

(* [comment removed for export] *)

Lemma len_word_firstn_nat : forall n (bs : list byte),
  (n <= length bs)%nat ->
  len_word (firstn n bs) = nat_to_word n.
Proof.
  intros n bs Hn. unfold len_word, nat_to_word.
  rewrite firstn_length_le by exact Hn. reflexivity.
Qed.

Lemma u_len_word_firstn : forall n (bs : list byte),
  (n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
  bv_unsigned (len_word (firstn n bs)) = Z.of_nat n.
Proof.
  intros n bs Hn Hlen.
  rewrite len_word_unsigned by (rewrite firstn_length_le by exact Hn;
                                unfold two_pow_64; lia).
  rewrite firstn_length_le by exact Hn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma v_add_len_firstn : forall (p : word) n (bs : list byte),
  (n <= length bs)%nat ->
  v_add p (len_word (firstn n bs)) = p + nat_to_word n.
Proof.
  intros p n bs Hn. rewrite len_word_firstn_nat by exact Hn.
  unfold v_add. apply bv_eq.
  rewrite Z_to_bv_unsigned, bv_add_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma v_add_len_firstn_Z : forall (p : word) n (bs : list byte),
  (n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
  v_add p (len_word (firstn n bs)) = Z_to_bv 64 (bv_unsigned p + Z.of_nat n).
Proof.
  intros p n bs Hn Hlen. unfold v_add.
  rewrite u_len_word_firstn by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma word_add_nat_Z : forall (p : word) (k : nat),
  (Z.of_nat k < 2^64)%Z ->
  p + nat_to_word k = Z_to_bv 64 (bv_unsigned p + Z.of_nat k).
Proof.
  intros p k Hk. apply bv_eq.
  rewrite bv_add_unsigned. unfold nat_to_word.
  rewrite Z_to_bv_small
    by (unfold bv_modulus; change (Z.of_N 64) with 64%Z; lia).
  rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma v_sub_len_firstn : forall n (bs : list byte),
  (n <= length bs)%nat -> (Z.of_nat (length bs) < 2^64)%Z ->
  v_sub (len_word bs) (len_word (firstn n bs)) = len_word (skipn n bs).
Proof.
  intros n bs Hn Hlen. apply bv_eq.
  rewrite v_sub_small
    by (rewrite u_len_word_firstn by assumption;
        rewrite len_word_unsigned by (unfold two_pow_64; lia); lia).
  rewrite u_len_word_firstn by assumption.
  rewrite !len_word_unsigned
    by (unfold two_pow_64; rewrite ?length_skipn; lia).
  rewrite length_skipn. lia.
Qed.

Section WithSegsCh.
Variable segs : list Segment.
Variable fd ch : word.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive to_wall : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twl_write : forall ms x8 rest k,
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 64%Z ->
    ms_gpr ms 0 = fd ->
    ms_read_bytes ms (ms_gpr ms 1) (ms_gpr ms 2) = Some rest ->
    (* the range [vfs_write]'s [access_ok] accepts; see [CatSim.write1_check_n] *)
    access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
    (1 <= length rest)%nat ->
    (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
       to_wall_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest))))
         (skipn n rest) k) ->
    to_wall ms rest k
with to_wall_tail : machine_state -> list byte -> (machine_state -> Prop) -> Prop :=
| twt_done : forall ms k, k ms -> to_wall_tail ms [] k
| twt_more : forall ms rest k,
    (1 <= length rest)%nat ->
    to_wall ms rest k ->
    to_wall_tail ms rest k
| twt_step : forall ms ms' rest k,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wall_tail ms' rest k ->
    to_wall_tail ms rest k.

Scheme to_wall_min := Minimality for to_wall Sort Prop
  with to_wall_tail_min := Minimality for to_wall_tail Sort Prop.
Combined Scheme to_wall_mutind from to_wall_min, to_wall_tail_min.

(* [comment removed for export] *)
Lemma msteps_to_wall_tail : forall ms ms' rest k,
  msteps segs ms ms' -> to_wall_tail ms' rest k -> to_wall_tail ms rest k.
Proof.
  intros ms ms' rest k H; induction H; [auto|].
  intro Hw. eapply twt_step; eauto.
Qed.

(* [comment removed for export] *)
Lemma to_wall_tail_nil_msteps : forall ms k,
  to_wall_tail ms [] k -> exists ms', msteps segs ms ms' /\ k ms'.
Proof.
  intros ms k H.
  remember ([] : list byte) as rest eqn:Hrest.
  induction H as [ms k Hk | ms rest k Hnb Hw | ms ms' rest k Hsvc Hstep Ht IH].
  - exists ms. split; [apply mst_refl | exact Hk].
  - subst rest. cbn in Hnb. lia.
  - destruct (IH Hrest) as (ms'' & Hm & Hk).
    exists ms''. split; [eapply mst_step; eauto | exact Hk].
Qed.

Hypothesis Hfd32 : fd32 fd = fd.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sstep_to_wall_inv : forall ms rest k model evs st,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  buf_modeled rest ->
  to_wall ms rest k ->
  sstep segs (mkCfg ms model) evs st ->
  exists n, (1 <= n)%nat /\ (n <= length rest)%nat /\
    evs = map (WriteEv ch) (firstn n rest) /\
    st = SNext (mkCfg (advance_past_svc (set_gpr0 ms (len_word (firstn n rest)))) model) /\
    to_wall_tail (advance_past_svc (set_gpr0 ms (len_word (firstn n rest))))
      (skipn n rest) k.
Proof.
  intros ms rest k model evs st Hh Hlazy Hfdc Hbm Hw Hss.
  revert Hbm.
  destruct Hw as [ms x8 rest k Hsvc Hno Hg Hr Hok Hnb Hcont]. intro Hbm.
  destruct (sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs st
              Hh Hlazy Hfdc Hsvc Hno Hg Hr Hok Hbm Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hst).
  exists n. repeat split; try assumption.
  apply (Hcont n Hn1 Hn2).
Qed.

Lemma to_wall_no_error_sstep : forall ms rest k model evs,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  buf_modeled rest ->
  to_wall ms rest k ->
  ~ sstep segs (mkCfg ms model) evs SError.
Proof.
  intros ms rest k model evs Hh Hlazy Hfdc Hbm Hw Hss.
  destruct (sstep_to_wall_inv ms rest k model evs SError Hh Hlazy Hfdc Hbm Hw Hss)
    as (n & _ & _ & _ & Hst & _).
  discriminate Hst.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_wall_star_admits_mut : forall model tr_k,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms rest k, to_wall ms rest k ->
     buf_modeled rest ->
     (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
     exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)
  /\ (forall ms rest k, to_wall_tail ms rest k ->
     buf_modeled rest ->
     (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
     exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c).
Proof.
  intros model tr_k Hh Hlazy Hfdc.
  apply (to_wall_mutind
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
       exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
       exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c)).
  - (* twl_write: deliver everything in one syscall *)
    intros ms x8 rest k Hsvc Hno Hg Hr Hok Hnb Hcont IH Hbm Hk.
    destruct (IH (length rest) Hnb (Nat.le_refl _)
                (buf_modeled_skipn (length rest) rest Hbm) Hk) as [c Hstar].
    exists c.
    replace (map (WriteEv ch) rest ++ tr_k)
      with (map (WriteEv ch) (firstn (length rest) rest)
              ++ (map (WriteEv ch) (skipn (length rest) rest) ++ tr_k))
      by (rewrite firstn_all, skipn_all; reflexivity).
    eapply star_step; [| exact Hstar].
    rewrite <- (apply_effect_copyins_no_write ms
                  (len_word (firstn (length rest) rest))
                  [(ms_gpr ms 1, length rest)]).
    apply (sstep_syscall segs ms model x8
             (with_copyins [(ms_gpr ms 1, length rest)]
                (mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
             (map (WriteEv ch) (firstn (length rest) rest)));
      [exact Hh | exact Hsvc | | exact Hh |].
    eapply write_ch_ok_n; try eassumption. apply Nat.le_refl.
    rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
  - (* twt_done: hand off to the continuation *)
    intros ms k Hk Hbm Hcont. cbn [map app]. apply (Hcont ms Hk).
  - (* twt_more *)
    intros ms rest k Hnb Hw IH Hbm Hk. exact (IH Hbm Hk).
  - (* twt_step *)
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm Hk.
    destruct (IH Hbm Hk) as [c Hstar].
    exists c.
    replace (map (WriteEv ch) rest ++ tr_k)
      with (([] : list event) ++ (map (WriteEv ch) rest ++ tr_k)) by reflexivity.
    eapply star_step; [| exact Hstar].
    apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

Lemma to_wall_star_admits : forall ms rest k,
  to_wall ms rest k ->
  buf_modeled rest ->
  forall model tr_k,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
  exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c.
Proof.
  intros ms rest k Hw Hbm model tr_k Hh Hlazy Hfdc Hk.
  exact (proj1 (to_wall_star_admits_mut model tr_k Hh Hlazy Hfdc) ms rest k Hw Hbm Hk).
Qed.

Lemma to_wall_tail_star_admits : forall ms rest k,
  to_wall_tail ms rest k ->
  buf_modeled rest ->
  forall model tr_k,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms', k ms' -> exists c, star segs (mkCfg ms' model) tr_k c) ->
  exists c, star segs (mkCfg ms model) (map (WriteEv ch) rest ++ tr_k) c.
Proof.
  intros ms rest k Hw Hbm model tr_k Hh Hlazy Hfdc Hk.
  exact (proj2 (to_wall_star_admits_mut model tr_k Hh Hlazy Hfdc) ms rest k Hw Hbm Hk).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_wall_star_only_mut : forall model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms rest k, to_wall ms rest k ->
     buf_modeled rest ->
     (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
     forall tr c, star segs (mkCfg ms model) tr c ->
     is_prefix tr (map (WriteEv ch) rest ++ T))
  /\ (forall ms rest k, to_wall_tail ms rest k ->
     buf_modeled rest ->
     (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
     forall tr c, star segs (mkCfg ms model) tr c ->
     is_prefix tr (map (WriteEv ch) rest ++ T)).
Proof.
  intros model T Hh Hlazy Hfdc.
  apply (to_wall_mutind
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
       forall tr c, star segs (mkCfg ms model) tr c ->
       is_prefix tr (map (WriteEv ch) rest ++ T))
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
       forall tr c, star segs (mkCfg ms model) tr c ->
       is_prefix tr (map (WriteEv ch) rest ++ T))).
  - (* twl_write *)
    intros ms x8 rest k Hsvc Hno Hg Hr Hok Hnb Hcont IH Hbm HK tr c Hstar.
    inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
    { apply is_prefix_nil. }
    destruct (sstep_write_ch_inv segs fd ch Hfd32 ms model x8 rest evs (SNext c2)
                Hh Hlazy Hfdc Hsvc Hno Hg Hr Hok Hbm Hnb Hss) as (n & Hn1 & Hn2 & Hevs & Hc2).
    subst evs. inversion Hc2; subst c2.
    pose proof (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) HK tr2 c Hstar2) as Hp.
    rewrite <- (firstn_skipn n rest) at 2.
    rewrite map_app, <- app_assoc.
    apply is_prefix_app_mono. exact Hp.
  - (* twt_done *)
    intros ms k Hk Hbm HK tr c Hstar. cbn [map app]. exact (HK ms tr c Hk Hstar).
  - (* twt_more *)
    intros ms rest k Hnb Hw IH Hbm HK tr c Hstar. exact (IH Hbm HK tr c Hstar).
  - (* twt_step *)
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm HK tr c Hstar.
    inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
    { apply is_prefix_nil. }
    destruct (sstep_instr_inv segs ms model ms' evs (SNext c2) Hlazy Hsvc Hstep Hss)
      as [Hevs Hc2].
    subst evs. inversion Hc2; subst c2. cbn [app].
    exact (IH Hbm HK tr2 c Hstar2).
Qed.

Lemma to_wall_star_only : forall ms rest k,
  to_wall ms rest k ->
  buf_modeled rest ->
  forall model T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms' tr c, k ms' -> star segs (mkCfg ms' model) tr c -> is_prefix tr T) ->
  forall tr c, star segs (mkCfg ms model) tr c ->
  is_prefix tr (map (WriteEv ch) rest ++ T).
Proof.
  intros ms rest k Hw Hbm model T Hh Hlazy Hfdc HK tr c Hstar.
  exact (proj1 (to_wall_star_only_mut model T Hh Hlazy Hfdc) ms rest k Hw Hbm HK tr c Hstar).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma twl_write_rec : forall (k : machine_state -> Prop) rest regs pc mem rom,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = fd ->
  ms_read_bytes {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
                   ms_svc_pending := Some (getr regs 17); ms_resv := None;
                   ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    (reg_get regs 11) (reg_get regs 12) = Some rest ->
  access_okb (reg_get regs 11) (bv_unsigned (reg_get regs 12)) = true ->
  (1 <= length rest)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length rest)%nat ->
     to_wall_tail (mkst (regupd regs 10 (len_word (firstn n rest)))
                        (v_addi pc 4) mem rom)
       (skipn n rest) k) ->
  to_wall {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;
             ms_svc_pending := Some (getr regs 17); ms_resv := None;
             ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |}
    rest k.
Proof.
  intros k rest regs pc mem rom H17 H10 Hr Hok Hnb Hcont.
  assert (E10 : Z_to_bv 5 (10 + Z.of_nat 0) = (10 : reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (10 + Z.of_nat 1) = (11 : reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (10 + Z.of_nat 2) = (12 : reg)) by (apply bv_eq; reflexivity).
  eapply twl_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E10. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hr.
  - unfold ms_gpr. cbn [ms_regs]. rewrite E11, E12. exact Hok.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. exact (Hcont n Hn1 Hn2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint to_wallexit (bufs : list (list byte)) (code : word)
    (ms : machine_state) : Prop :=
  match bufs with
  | [] => to_wexit segs ms [] code
  | buf :: rest =>
      (1 <= length buf)%nat /\
      to_wall_tail ms buf (to_wallexit rest code)
  end.

(* [comment removed for export] *)
Lemma to_wall_k_ex_mut :
  (forall ms rest k, to_wall ms rest k -> exists ms', k ms')
  /\ (forall ms rest k, to_wall_tail ms rest k -> exists ms', k ms').
Proof.
  apply (to_wall_mutind
           (fun ms rest k => exists ms', k ms')
           (fun ms rest k => exists ms', k ms')).
  - intros ms x8 rest k Hsvc Hno Hg Hr Hok Hnb Hcont IH.
    exact (IH (length rest) Hnb (Nat.le_refl _)).
  - intros ms k Hk. exists ms. exact Hk.
  - intros ms rest k Hnb Hw IH. exact IH.
  - intros ms ms' rest k Hsvc Hstep Ht IH. exact IH.
Qed.

Lemma to_wall_tail_k_ex : forall ms rest k,
  to_wall_tail ms rest k -> exists ms', k ms'.
Proof. exact (proj2 to_wall_k_ex_mut). Qed.

Lemma to_wallexit_bufs_nonempty : forall bufs code ms,
  to_wallexit bufs code ms ->
  Forall (fun b : list byte => (1 <= length b)%nat) bufs.
Proof.
  induction bufs as [|buf rest IH]; intros code ms Hw; [constructor|].
  destruct Hw as [Hnb Hw]. constructor; [exact Hnb|].
  destruct (to_wall_tail_k_ex _ _ _ Hw) as [ms' Hk].
  exact (IH code ms' Hk).
Qed.

(* [comment removed for export] *)
Lemma twe_step : forall ms ms' bufs code,
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
  intros ms ms' bufs code Hsvc Hstep Hw.
  destruct bufs as [|buf rest].
  - eapply tw_step; eauto.
  - destruct Hw as [Hnb Hw]. split; [exact Hnb|].
    eapply twt_step; eauto.
Qed.

Lemma msteps_to_wallexit : forall ms ms' bufs code,
  msteps segs ms ms' -> to_wallexit bufs code ms' -> to_wallexit bufs code ms.
Proof.
  intros ms ms' bufs code Hms Hw. destruct bufs as [|buf rest].
  - exact (msteps_to_wexit segs ms ms' [] code Hms Hw).
  - destruct Hw as [Hnb Hw]. split; [exact Hnb|].
    eapply msteps_to_wall_tail; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_wall_exec_mut : forall model (Q : post),
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  (forall ms rest k, to_wall ms rest k ->
     buf_modeled rest ->
     (forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
     OmniRun.exec segs (mkCfg ms model)
       (fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))
  /\ (forall ms rest k, to_wall_tail ms rest k ->
     buf_modeled rest ->
     (forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
     OmniRun.exec segs (mkCfg ms model)
       (fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o)).
Proof.
  intros model Q Hh Hlazy Hfdc.
  apply (to_wall_mutind
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
       OmniRun.exec segs (mkCfg ms model)
         (fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))
    (fun ms rest k =>
       buf_modeled rest ->
       (forall ms', k ms' -> OmniRun.exec segs (mkCfg ms' model) Q) ->
       OmniRun.exec segs (mkCfg ms model)
         (fun tr o => exists tr', tr = map (WriteEv ch) rest ++ tr' /\ Q tr' o))).
  - (* twl_write: every delivered length is a successor, each covered by the IH *)
    intros ms x8 rest k Hsvc Hno Hg Hr Hok Hnb Hcont IH Hbm HK.
    assert (Hw : to_wall ms rest k) by (eapply twl_write; eassumption).
    apply exec_step; [exact Hh | | |].
    + (* progress: deliver everything in one syscall *)
      eexists; eexists.
      apply (sstep_syscall segs ms model x8
               (with_copyins [(ms_gpr ms 1, length rest)]
                  (mkEffect (len_word (firstn (length rest) rest)) [] [])) model model
               (map (WriteEv ch) (firstn (length rest) rest)));
        [exact Hh | exact Hsvc | | exact Hh |].
      * eapply write_ch_ok_n; try eassumption. apply Nat.le_refl.
      * rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity.
    + intros evs Hss.
      destruct (sstep_to_wall_inv ms rest k model evs SError Hh Hlazy Hfdc Hbm Hw Hss)
        as (n & _ & _ & _ & Habs & _).
      discriminate Habs.
    + intros evs c' Hss.
      destruct (sstep_to_wall_inv ms rest k model evs (SNext c') Hh Hlazy Hfdc Hbm Hw Hss)
        as (n & Hn1 & Hn2 & -> & Hc' & _).
      injection Hc' as ->.
      eapply exec_conseq;
        [exact (IH n Hn1 Hn2 (buf_modeled_skipn n rest Hbm) HK) |].
      intros tr o (tr' & -> & HQ). exists tr'. split; [| exact HQ].
      rewrite <- (firstn_skipn n rest) at 3. rewrite map_app, <- app_assoc. reflexivity.
  - (* twt_done: the continuation's own judgment *)
    intros ms k Hk Hbm HK.
    eapply exec_conseq; [exact (HK ms Hk) |].
    intros tr o HQ. exists tr. split; [reflexivity | exact HQ].
  - (* twt_more *)
    intros ms rest k Hnb Hw IH Hbm HK. exact (IH Hbm HK).
  - (* twt_step: one silent instruction *)
    intros ms ms' rest k Hsvc Hstep Ht IH Hbm HK.
    apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbm HK) |]. intros tr o H. cbn [app]. exact H.
Qed.

(* [comment removed for export] *)
Lemma to_wexit_nil_exec_aux : forall ms bufs code model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_wexit segs ms bufs code ->
  bufs = [] ->
  OmniRun.exec segs (mkCfg ms model)
    (fun tr o => tr = [ExitEv code (m_fs model)] /\ exits_with code tr o).
Proof.
  intros ms bufs code model Hh Hlazy Hte.
  induction Hte as
    [ms x8 Hsvc Hx8
    | ms x8 buf bufs code Hsvc Hno Hg Hr Hok Hnb Hcont IH
    | ms ms' bufs code Hsvc Hstep Hte IH]; intro Hbufs; [| discriminate Hbufs |].
  - apply (exec_step_only segs _ _
             [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
             (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))).
    + replace [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)]
        with ([] ++ [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
                       (m_fs (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model))])
        by (cbn; reflexivity).
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model) []
               (bv_and (ms_gpr ms 0) (Z_to_bv 64 255))).
      * exact Hh.
      * exact Hsvc.
      * apply (exit_dispatch_ok (sys_input segs ms x8) model).
        rewrite in_sysno_sys_input. exact Hx8.
      * cbn. reflexivity.
      * apply m_killed_with_halted.
    + intros evs st Hss. exact (sstep_exit_inv segs ms model x8 evs st Hh Hsvc Hx8 Hss).
    + apply exec_halt.
      * cbn. rewrite m_halted_with_halted. discriminate.
      * cbn beta. rewrite app_nil_r. split; [reflexivity |].
        cbn [exits_with cfg_model]. split;
          [ rewrite m_halted_with_halted; reflexivity
          | apply m_killed_with_halted ].
  - apply (exec_step_only segs _ _ [] (mkCfg ms' model)).
    + apply (sstep_instr segs ms model ms' model); [exact Hh | exact Hsvc |].
      rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
    + intros evs st Hss. exact (sstep_instr_inv segs ms model ms' evs st Hlazy Hsvc Hstep Hss).
    + eapply exec_conseq; [exact (IH Hbufs) |]. intros tr o H. cbn [app]. exact H.
Qed.

Lemma to_wexit_nil_exec : forall ms code model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_wexit segs ms [] code ->
  OmniRun.exec segs (mkCfg ms model)
    (fun tr o => tr = [ExitEv code (m_fs model)] /\ exits_with code tr o).
Proof.
  intros ms code model Hh Hlazy Hte.
  exact (to_wexit_nil_exec_aux ms [] code model Hh Hlazy Hte eq_refl).
Qed.

(* [comment removed for export] *)
Lemma to_wallexit_exec : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  OmniRun.exec segs (mkCfg ms model)
    (fun tr o => tr = wevents_ch ch bufs ++ [ExitEv code (m_fs model)]
                 /\ exits_with code tr o).
Proof.
  induction bufs as [|buf rest IH]; intros code ms model Hh Hlazy Hfdc Hbm Hw.
  - cbn [wevents_ch app]. apply to_wexit_nil_exec; assumption.
  - destruct Hw as [Hnb Hw]. apply Forall_cons_iff in Hbm as [Hb Hbs].
    eapply exec_conseq;
      [exact (proj2 (to_wall_exec_mut model _ Hh Hlazy Hfdc) ms buf (to_wallexit rest code)
                Hw Hb (fun ms' Hk => IH code ms' model Hh Hlazy Hfdc Hbs Hk)) |].
    intros tr o (tr' & -> & Heq & Hx). split; [| exact Hx].
    rewrite Heq. cbn [wevents_ch]. rewrite <- app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_wallexit_star_admits : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  exists c, star segs (mkCfg ms model)
              (wevents_ch ch bufs ++ [ExitEv code (m_fs model)]) c.
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw.
  destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
    as (tr & [c' | c'] & Hm & Heq & Hx); [| destruct Hx].
  subst tr. destruct (mexec_halt_star _ _ _ _ Hm c' eq_refl) as (Hstar & _).
  exists c'. exact Hstar.
Qed.

(* [comment removed for export] *)
Lemma to_wallexit_no_other_exit : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  forall code', code' <> code ->
  ~ OmniRun.exec segs (mkCfg ms model) (exits_with code').
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw code' Hne Hex.
  destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
    as (tr & [c' | c'] & Hm & _ & Hx); [| destruct Hx].
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Hx'.
  cbn [exits_with] in Hx, Hx'. destruct Hx as (Hx & _). destruct Hx' as (Hx' & _).
  rewrite Hx in Hx'. injection Hx' as Hx'.
  exact (Hne (eq_sym Hx')).
Qed.

Lemma to_wallexit_trace_unique : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  forall tr', tr' <> wevents_ch ch bufs ++ [ExitEv code (m_fs model)] ->
  ~ OmniRun.exec segs (mkCfg ms model) (fun tr _ => tr = tr').
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw tr' Hne Hex.
  destruct (exec_realizes _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw))
    as (tr & o & Hm & Heq & _).
  pose proof (exec_sound _ _ _ Hex _ _ Hm) as Heq'. cbn beta in Heq'.
  apply Hne. rewrite <- Heq', Heq. reflexivity.
Qed.

Lemma to_wallexit_not_silent : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  ~ cosafe segs (mkCfg ms model) (fun tr => tr = []).
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw Hc.
  destruct (to_wallexit_star_admits bufs code ms model Hh Hlazy Hfdc Hbm Hw) as (c' & Hstar).
  pose proof (cosafe_star _ _ _ _ _ Hc Hstar) as Hnil.
  destruct (wevents_ch ch bufs); discriminate Hnil.
Qed.

Lemma to_wallexit_star_only : forall bufs code ms model,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  forall tr c, star segs (mkCfg ms model) tr c ->
  is_prefix tr (wevents_ch ch bufs ++ [ExitEv code (m_fs model)]).
Proof.
  intros bufs code ms model Hh Hlazy Hfdc Hbm Hw tr c Hstar.
  destruct (exec_realizes _ _ _
              (exec_star _ _ _ _ _ (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw) Hstar))
    as (tr' & o & _ & HQ).
  cbn beta in HQ. destruct HQ as (Heq & _). rewrite <- Heq. apply is_prefix_app.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma to_wallexit_no_error : forall ms model bufs code,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fdchan fd ch model ->
  bufs_modeled bufs ->
  to_wallexit bufs code ms ->
  ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model bufs code Hh Hlazy Hfdc Hbm Hw. apply exec_no_error.
  eapply exec_conseq; [exact (to_wallexit_exec bufs code ms model Hh Hlazy Hfdc Hbm Hw) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

End WithSegsCh.

(* [comment removed for export] *)
Abbreviation wexit1 segs ms bufs code :=
  (to_wallexit segs (Z_to_bv 64 1) bufs code ms).

(* [comment removed for export] *)
Lemma wevents_ch_fd1 : forall bufs,
  wevents_ch (Z_to_bv 64 1) bufs = wevents bufs.
Proof.
  induction bufs as [|b bs IH]; cbn [wevents_ch wevents];
    [reflexivity | rewrite IH; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fdchan_with_vdso : forall v m fd ch, fdchan fd ch m -> fdchan fd ch (with_vdso v m).
Proof. intros v m fd ch H; exact H. Qed.

Lemma wall_omni_run : forall fd ch, fd32 fd = fd ->
  forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  fdchan fd ch (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp) ->
  bufs_modeled bufs ->
  to_wallexit (run_segments segs inp sp mb) fd bufs code
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ->
  omni_run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp
    (fun tr o => tr = wevents_ch ch bufs ++ [ExitEv code (in_fs inp)]
                 /\ exits_with code tr o).
Proof.
  intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw.
  cbn [omni_run]. unfold init_config.
  exact (to_wallexit_exec (run_segments segs inp sp mb) fd ch Hfd32 bufs code _
           (with_vdso (Vdso.vdso_run_init (ed_vdso rnd))
              (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp))
           eq_refl eq_refl (fdchan_with_vdso _ _ _ _ Hfdc) Hbm Hw).
Qed.

Lemma wall_obs_iff : forall fd ch, fd32 fd = fd ->
  forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  fdchan fd ch (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp) ->
  bufs_modeled bufs ->
  to_wallexit (run_segments segs inp sp mb) fd bufs code
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ->
  forall tr, obs_trace (run_segments segs inp sp mb)
               (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) tr
             <-> is_prefix tr (wevents_ch ch bufs ++ [ExitEv code (in_fs inp)]).
Proof.
  intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw tr.
  apply exec_obs_iff.
  eapply exec_conseq;
    [exact (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw) |].
  intros tr' o (Heq & Hx). split; [exact Heq | exact (exits_with_never_errors _ _ _ Hx)].
Qed.

Lemma wall_no_error_run : forall fd ch, fd32 fd = fd ->
  forall segs pc ph sp brk0 mb rnd lim inp bufs code,
  fdchan fd ch (init_model (segments_reserved (run_segments segs inp sp mb)) brk0 mb sp lim inp) ->
  bufs_modeled bufs ->
  to_wallexit (run_segments segs inp sp mb) fd bufs code
    (init_machine_state (run_segments segs inp sp mb) pc ph sp mb rnd inp) ->
  ~ reaches_error (run_segments segs inp sp mb)
      (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp).
Proof.
  intros fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw. apply exec_no_error.
  eapply exec_conseq;
    [exact (wall_omni_run fd ch Hfd32 segs pc ph sp brk0 mb rnd lim inp bufs code Hfdc Hbm Hw) |].
  intros tr o (_ & Hx). exact (exits_with_never_errors _ _ _ Hx).
Qed.

(* [comment removed for export] *)
Lemma wall_omni_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp,
  to_wallexit (run_segments source_segs inp rsp rmb) (Z_to_bv 64 1) bufs code
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) ->
  to_wallexit (run_segments target_segs inp asp amb) (Z_to_bv 64 1) bufs code
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) ->
  bufs_modeled bufs ->
  in_channel_reader inp = true ->
  omni_strong_equiv (mkImage source_segs rpc rph) (mkImage target_segs apc aph)
                    (mkEntry rsp rbrk rmb rrnd) (mkEntry asp abrk amb arnd) inp.
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd target_segs apc aph asp abrk amb arnd bufs code inp
    Hsource Htarget Hbm Hr.
  assert (HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp source_alloc_limit inp))
    by (apply fd1chan_fdchan, init_model_fd1chan; exact Hr).
  assert (HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp target_alloc_limit inp))
    by (apply fd1chan_fdchan, init_model_fd1chan; exact Hr).
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [apply exec_coexec;
       exact (wall_omni_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1 source_segs rpc rph rsp rbrk rmb rrnd
                source_alloc_limit inp bufs code HfdS Hbm Hsource) |].
    intros tr o (_ & Hx).
    exact (never_errors_covered _ _ _ (exits_with_never_errors _ _ _ Hx)). }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               source_segs rpc rph rsp rbrk rmb rrnd source_alloc_limit inp bufs code HfdS Hbm Hsource tr).
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code HfdT Hbm Htarget tr).
    reflexivity.
  - apply bh_errors_iff. cbn.
    apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
             target_segs apc aph asp abrk amb arnd target_alloc_limit inp bufs code HfdT Hbm Htarget).
Qed.

(* [comment removed for export] *)
Lemma wall_strong_equiv :
  forall source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim bufs code inp,
  to_wallexit (run_segments source_segs inp rsp rmb) (Z_to_bv 64 1) bufs code
    (init_machine_state (run_segments source_segs inp rsp rmb) rpc rph rsp rmb rrnd inp) ->
  to_wallexit (run_segments target_segs inp asp amb) (Z_to_bv 64 1) bufs code
    (init_machine_state (run_segments target_segs inp asp amb) apc aph asp amb arnd inp) ->
  bufs_modeled bufs ->
  in_channel_reader inp = true ->
  Equivalence.modeled (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ Equivalence.equiv (run (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
                       (run (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
         bufs code inp Hsource Htarget Hbm Hr.
  assert (HfdS : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved (run_segments source_segs inp rsp rmb)) rbrk rmb rsp rlim inp))
    by (apply fd1chan_fdchan, init_model_fd1chan; exact Hr).
  assert (HfdT : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1)
    (init_model (segments_reserved (run_segments target_segs inp asp amb)) abrk amb asp alim inp))
    by (apply fd1chan_fdchan, init_model_fd1chan; exact Hr).
  split.
  { apply no_error_run_modeled.
    apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
             source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
             HfdS Hbm Hsource). }
  right. split.
  - intro tr. cbn.
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               source_segs rpc rph rsp rbrk rmb rrnd rlim inp bufs code
               HfdS Hbm Hsource tr).
    rewrite (wall_obs_iff (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
               target_segs apc aph asp abrk amb arnd alim inp bufs code
               HfdT Hbm Htarget tr).
    reflexivity.
  - cbn.
    apply (wall_no_error_run (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
             target_segs apc aph asp abrk amb arnd alim inp bufs code
             HfdT Hbm Htarget).
Qed.
End WithFP1.
