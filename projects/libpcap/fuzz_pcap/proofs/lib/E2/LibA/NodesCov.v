(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec ITree RelSpec Nodes.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import AcctCore ExecF ModelX MmXfer SpecXfer.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ITreeA NodesA NodesSil NodesMmSh NodesAS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section Cov.
Variable segs : list Segment.
Variable RNG : footprint.

(* [comment removed for export] *)
Definition node_cov (P : Model -> resp -> Model -> list event -> Prop) (ms : machine_state) (mo : Model) : Prop :=
  forall x8 eff mo' evs, ms_svc_pending ms = Some x8 ->
    syscall_spec (sys_input segs ms x8) mo (Ok eff mo' evs) -> Forall (acc_in RNG) (syscall_effect_accesses eff).

#[using="Type"] Lemma cov_det_gen : forall (P : Model -> resp -> Model -> list event -> Prop) ms mo x8 (e1 r1 : resp) mo1 evs0,
  ms_svc_pending ms = Some x8 -> m_halted mo = None ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <-> o = Ok e1 mo1 evs0) ->
  nret ms e1 = nret ms r1 ->
  (forall eff mo' evs, P mo eff mo' evs <-> (eff = r1 /\ mo' = mo1 /\ evs = evs0)) ->
  m_halted mo1 = None -> minv mo1 ->
  Forall (acc_in RNG) (syscall_effect_accesses e1) ->
  node_cov P ms mo.
Proof.
  intros P ms mo x8 e1 r1 mo1 evs0 Hsvc Hh Hchar Hnr HP Hh1 Hminv1 HC x8' eff mo' evs Hx Hsp.
  rewrite Hsvc in Hx. injection Hx as <-. apply Hchar in Hsp. apply Ok_inj in Hsp as (-> & _ & _). exact HC.
Qed.

#[using="Type"] Lemma cov_det : forall (P : Model -> resp -> Model -> list event -> Prop) ms mo x8 r ci mo1 evs0,
  ms_svc_pending ms = Some x8 -> m_halted mo = None ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <-> o = Ok (with_copyins ci (eff0 r)) mo1 evs0) ->
  (forall eff mo' evs, P mo eff mo' evs <-> (eff = eff0 r /\ mo' = mo1 /\ evs = evs0)) ->
  m_halted mo1 = None -> minv mo1 ->
  Forall (acc_in RNG) ci ->
  node_cov P ms mo.
Proof.
  intros P ms mo x8 r ci mo1 evs0 Hsvc Hh Hchar HP Hh1 Hminv1 HC.
  eapply cov_det_gen; [exact Hsvc|exact Hh|exact Hchar|apply nret_with_copyins|exact HP|exact Hh1|exact Hminv1|].
  unfold syscall_effect_accesses. cbn. rewrite app_nil_r. exact HC.
Qed.

#[using="Type"] Lemma cov_det0 : forall (P : Model -> resp -> Model -> list event -> Prop) ms mo x8 (e1 : resp) mo1 evs0,
  ms_svc_pending ms = Some x8 -> m_halted mo = None ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <-> o = Ok e1 mo1 evs0) ->
  (forall eff mo' evs, P mo eff mo' evs <-> (eff = e1 /\ mo' = mo1 /\ evs = evs0)) ->
  m_halted mo1 = None -> minv mo1 ->
  Forall (acc_in RNG) (syscall_effect_accesses e1) ->
  node_cov P ms mo.
Proof.
  intros P ms mo x8 e1 mo1 evs0 Hsvc Hh Hchar HP Hh1 Hminv1 HC.
  eapply cov_det_gen; [exact Hsvc|exact Hh|exact Hchar|reflexivity|exact HP|exact Hh1|exact Hminv1|exact HC].
Qed.

Ltac sysno K :=
  rewrite in_sysno_si; change (bv_unsigned (Z_to_bv 64 K)) with K; reflexivity.

(* [comment removed for export] *)
Ltac cov_nil := first [ constructor | (unfold syscall_effect_accesses; cbn; constructor) ].

#[using="Type"] Lemma cov_one : forall (a : word) (k : nat) len,
  rng RNG (bv_unsigned a) len -> Z.of_nat k <= len -> Forall (acc_in RNG) [(a, k)].
Proof.
  intros a k len HR Hk. constructor; [|constructor].
  eapply rng_acc_var; [exact HR|]. lia.
Qed.

#[using="Type"] Lemma write_family_cov : forall ms mo x8 fd bs (cis : nat -> list (word * nat)),
  ms_svc_pending ms = Some x8 -> m_halted mo = None -> minv mo ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <->
     exists k, (1 <= k <= length bs)%nat /\
       o = Ok (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] [] (cis k)) mo (map (WriteEv (Z_to_bv 64 fd)) (firstn k bs))) ->
  (1 <= length bs)%nat ->
  (forall k, (1 <= k <= length bs)%nat -> Forall (acc_in RNG) (cis k)) ->
  node_cov (write_result fd bs) ms mo.
Proof.
  intros ms mo x8 fd bs cis Hsvc Hh Hminv Hchar Hlen HC x8' eff mo' evs Hx Hsp.
  rewrite Hsvc in Hx. injection Hx as <-. apply Hchar in Hsp as (k & Hk & Heq). apply Ok_inj in Heq as (-> & _ & _).
  unfold syscall_effect_accesses. cbn. rewrite app_nil_r. apply HC. exact Hk.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma write_zero_cov : forall ms mo x8 fd ci,
  ms_svc_pending ms = Some x8 -> m_halted mo = None -> minv mo ->
  (forall o, syscall_spec (sys_input segs ms x8) mo o <-> o = Ok (with_copyins ci (eff0 (Z_to_bv 64 0))) mo []) ->
  Forall (acc_in RNG) ci ->
  node_cov (write_result fd []) ms mo.
Proof.
  intros ms mo x8 fd ci Hsvc Hh Hminv Hchar HC.
  eapply cov_det; [exact Hsvc|exact Hh|exact Hchar| |exact Hh|exact Hminv|exact HC].
  intros eff mo' evs. unfold write_result, wr_range. cbn [length firstn map]. split.
  - intros (-> & k & Hk & -> & ->). destruct Hk as [[_ ->]|Hk]; [|lia]. auto.
  - intros (-> & -> & ->). split; [reflexivity|]. exists 0%nat. auto.
Qed.

#[using="Type"] Lemma write_cov : forall ms mo fd bs,
  at_nodeA segs (NWrite fd bs) RNG ms -> minv mo -> m_halted mo = None ->
  node_cov (nstep (NWrite fd bs)) ms mo.
Proof.
  intros ms mo fd bs [(Hsvc & Hfd & Ha0 & Ha2 & Hlen & Hrom & Hbs) HCOV] Hminv Hh. cbn [ncov] in HCOV.
  unfold max_write, rw_bytes_max in Hlen.
  pose proof (bytes_at_in _ _ _ _ Hrom Hbs) as Hin.
  destruct (std_chan mo fd Hminv Hfd) as [Hlk Hw].
  apply (write_family_cov ms mo (Z_to_bv 64 64) fd bs (fun k => [(areg ms 11, k)]) Hsvc Hh Hminv); [|lia|].
  2:{ intros k Hk. eapply cov_one; [exact HCOV| lia]. }
  intros o. rewrite syscall_spec_64 by (sysno 64). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2.
  rewrite (write_chan_outcome _ _ _ _ _ _ (Z_to_bv 64 fd) bs Hlk Hw).
  - reflexivity.
  - rewrite unsigned_lit by lia. unfold rw_bytes_max. lia.
  - rewrite w_is0_lit by lia. apply Z.eqb_neq. lia.
  - rewrite in_mem_si. rewrite <- (wa_unsigned_id (areg ms 11)). apply read_bytes_map_bytes_in; [exact Hin|lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

#[using="Type"] Lemma copy_iovecs_accesses_cov : forall mp k (a : word),
  rng RNG (bv_unsigned a) (16 * Z.of_nat k) -> bv_unsigned a + 16 * Z.of_nat k <= 2^64 ->
  Forall (acc_in RNG) (copy_iovecs_accesses mp a k).
Proof.
  intros mp k. induction k as [|k IH]; intros a HR HB; cbn [copy_iovecs_accesses]; [constructor|].
  pose proof (bv_unsigned_in_range 64 a) as Ra. change (bv_modulus 64) with (2^64) in Ra.
  constructor.
  - eapply rng_acc_var; [exact HR|]. lia.
  - destruct (read_iovec_entry mp a); try constructor.
    destruct (Z.eq_dec (Z.of_nat k) 0) as [E|E]; [destruct k; [constructor| lia]|].
    assert (U : bv_unsigned (a + 16)%bv = bv_unsigned a + 16).
    { rewrite bv_add_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
      change (bv_unsigned (16 : word)) with 16. apply Z.mod_small. lia. }
    apply IH; rewrite U; [eapply rng_sub; [exact HR| lia| lia] | lia].
Qed.

#[using="Type"] Lemma import_iovecs_accesses_cov : forall mp (a : word) (cnt : nat),
  rng RNG (bv_unsigned a) (16 * Z.of_nat cnt) -> (cnt <= 1024)%nat -> bv_unsigned a + 16 * Z.of_nat cnt <= 2^64 ->
  Forall (acc_in RNG) (import_iovecs_accesses mp a (Z_to_bv 64 (Z.of_nat cnt))).
Proof.
  intros mp a cnt HR HC HB. unfold import_iovecs_accesses.
  destruct (bv_eqb (Z_to_bv 64 (Z.of_nat cnt)) (Z_to_bv 64 1)) eqn:E1.
  - destruct (negb (access_okb a 16)); [constructor|].
    apply bv_eqb_eq in E1. apply (f_equal bv_unsigned) in E1. rewrite !unsigned_lit in E1 by lia.
    eapply cov_one; [exact HR| lia].
  - destruct (bv_eqb (Z_to_bv 64 (Z.of_nat cnt)) (Z_to_bv 64 0)); [constructor|].
    destruct (IOV_MAX <? bv_unsigned (Z_to_bv 64 (Z.of_nat cnt))); [constructor|].
    destruct (negb (access_okb a (16 * bv_unsigned (Z_to_bv 64 (Z.of_nat cnt))))); [constructor|].
    rewrite word_to_nat_of_nat by lia. apply copy_iovecs_accesses_cov; assumption.
Qed.

#[using="Type"] Lemma iov_prefix_cov : forall (iovs : list (word * word)) (lens : list Z),
  Forall2 (fun iov l => snd iov = Z_to_bv 64 l /\ rng RNG (bv_unsigned (fst iov)) l) iovs lens ->
  Forall (fun l => 0 <= l < 2^64) lens ->
  forall k, Forall (acc_in RNG) (iov_prefix_accesses iovs k).
Proof.
  intros iovs lens HF. induction HF as [| [base len] l iovs lens (Hl & HR) HF IH]; intros HL k.
  - destruct k; constructor.
  - cbn [fst snd] in *. inversion HL as [|? ? L0 HL']; subst.
    destruct k as [|k']; cbn [iov_prefix_accesses]; [constructor|].
    rewrite word_to_nat_bounded_eq_min. unfold word_to_nat. rewrite unsigned_lit by lia.
    destruct (Nat.eqb_spec (Nat.min (Z.to_nat l) (S k')) 0) as [E|E].
    + apply IH. exact HL'.
    + constructor; [| apply IH; exact HL']. eapply rng_acc_var; [exact HR|]. lia.
Qed.

#[using="Type"] Lemma gather_cov_lens : forall ms (iovs : list (word * word)) (bufs : list (list byte)),
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                         bv_unsigned (fst iov) + Z.of_nat (length bs) <= 2^47 /\
                         bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs /\
                         rng RNG (bv_unsigned (fst iov)) (Z.of_nat (length bs))) iovs bufs ->
  Forall2 (fun iov l => snd iov = Z_to_bv 64 l /\ rng RNG (bv_unsigned (fst iov)) l) iovs (map (fun bs => Z.of_nat (length bs)) bufs)
  /\ Forall (fun l => 0 <= l < 2^64) (map (fun bs => Z.of_nat (length bs)) bufs).
Proof.
  intros ms iovs bufs HF. induction HF as [| iov bs iovs bufs (H1 & H2 & _ & H4) HF [IH1 IH2]]; cbn [map].
  - split; constructor.
  - split; constructor; auto. pose proof (bv_unsigned_in_range 64 (fst iov)) as R. change (bv_modulus 64) with (2^64) in R. lia.
Qed.

#[using="Type"] Lemma writev_cov : forall ms mo fd bufs,
  at_nodeA segs (NWritev fd bufs) RNG ms -> minv mo -> m_halted mo = None ->
  node_cov (nstep (NWritev fd bufs)) ms mo.
Proof.
  intros ms mo fd bufs (Hsvc & Hfd & Ha0 & Ha2 & Hcnt & Harr & Htot & Hrom & HRarr & iovs & Hiov & HbufsR) Hminv Hh.
  destruct (gather_cov_lens ms iovs bufs HbufsR) as [HRl HRb].
  assert (Hbufs : Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                                         bv_unsigned (fst iov) + Z.of_nat (length bs) <= 2^47 /\
                                         bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs).
  { eapply Forall2_impl; [| exact HbufsR]. cbn. intros a b (X & X2 & Y & _). auto. }
  assert (HCarr : Forall (acc_in RNG) (import_iovecs_accesses (ms_read_byte ms) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs)))))).
  { unfold iovcnt32. rewrite abi_low32_small by lia. apply import_iovecs_accesses_cov; [exact HRarr| lia| lia]. }
  unfold max_write in Htot.
  pose proof (iovs_ok_of_at _ _ _ _ Hrom Hbufs ltac:(lia)) as Hok.
  pose proof (iovs_range_of_at _ _ _ _ Hbufs) as Hrng.
  pose proof (Forall2_length Hbufs) as Hleq.
  destruct (std_chan mo fd Hminv Hfd) as [Hlk Hw].
  pose proof (iovs_total_ok _ _ _ Hok) as Htotal.
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs))) = Z_to_bv 64 (Z.of_nat (length bufs))).
  { unfold iovcnt32. apply abi_low32_small. lia. }
  assert (Himp : import_iovecs (ms_read_byte ms) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs)))) = ImpOk iovs).
  { rewrite Hcnt32, <- Hleq. apply import_iovecs_ok; [lia| rewrite Hleq; exact Harr | eapply bytes_at_in; eassumption | exact Hrng]. }
  change (nstep (NWritev fd bufs)) with (write_result fd (concat bufs)).
  destruct (concat bufs) as [|b0 bs0] eqn:Ebs.
  { (* [comment removed for export] *)
    apply (write_zero_cov ms mo (Z_to_bv 64 66) fd
             (import_iovecs_accesses (ms_read_byte ms) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs))))) Hsvc Hh Hminv); [| exact HCarr].
    intros o. rewrite syscall_spec_66 by (sysno 66). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2.
    rewrite (writev_chan_zero_outcome _ _ _ _ _ _ (Z_to_bv 64 fd) iovs Hlk Hw).
    - rewrite in_mem_si. reflexivity.
    - rewrite in_mem_si. exact Himp.
    - rewrite Htotal, ?Ebs. reflexivity. }
  assert (Hpos : (1 <= length (concat bufs))%nat) by (rewrite Ebs; cbn; lia).
  rewrite <- Ebs in *. clear Ebs b0 bs0.
  apply (write_family_cov ms mo (Z_to_bv 64 66) fd (concat bufs)
           (fun k => import_iovecs_accesses (ms_read_byte ms) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs))))
                     ++ iov_prefix_accesses iovs k) Hsvc Hh Hminv); [|lia|].
  2:{ intros k Hk. apply Forall_app. split; [exact HCarr| exact (iov_prefix_cov iovs _ HRl HRb k)]. }
  intros o. rewrite syscall_spec_66 by (sysno 66). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2.
  rewrite (writev_chan_outcome _ _ _ _ _ _ (Z_to_bv 64 fd) iovs (concat bufs) Hlk Hw).
  - rewrite in_mem_si. reflexivity.
  - rewrite in_mem_si. exact Himp.
  - rewrite Htotal. unfold MAX_RW_COUNT. lia.
  - rewrite in_mem_si. apply gather_iovecs_ok. exact Hok.
  - lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


#[using="Type"] Lemma cstr_access_len_le : forall str fuel mp a,
  bytes_in mp a (str ++ [Z_to_bv 8 0]) -> (cstr_access_len_aux mp (wa a) fuel <= length str + 1)%nat.
Proof.
  induction str as [|b str IH]; intros fuel mp a H; destruct fuel as [|fuel]; cbn [cstr_access_len_aux length]; try lia.
  - cbn [app] in H. apply bytes_in_cons in H as [Hb _]. rewrite Hb. rewrite (proj2 (bv_eqb_eq _ _) eq_refl). lia.
  - cbn [app] in H. apply bytes_in_cons in H as [Hb H]. rewrite Hb.
    destruct (bv_eqb b (Z_to_bv 8 0)); [lia|]. rewrite wa_succ. specialize (IH fuel mp (a + 1) H). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma path_reads_cov : forall ms (path : list byte),
  ms_rom ms = seg_rom segs ->
  bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0]) ->
  rng RNG (bv_unsigned (areg ms 11)) (Z.of_nat (length path) + 1) ->
  Forall (acc_in RNG) [(areg ms 11, cstr_access_len_aux (ms_read_byte ms) (areg ms 11) path_max)].
Proof.
  intros ms path Hrom Hp HR. pose proof (bytes_at_in _ _ _ _ Hrom Hp) as Hin.
  eapply cov_one; [exact HR|].
  pose proof (cstr_access_len_le path path_max _ _ Hin) as L. rewrite wa_unsigned_id in L. lia.
Qed.

#[using="Type"] Lemma open_out_result : forall R mo ent o,
  open_out R mo (fun fd => with_fds (fd_insert (m_fds mo) fd ent) mo) o <->
  exists eff mo', o = Ok (with_copyins R eff) mo' [] /\ open_result mo ent eff mo'.
Proof.
  intros R mo ent o. unfold open_out, open_result, efferr, eff0. split.
  - intros [(e & He & ->) | (Hfree & ->)].
    + eexists _, _. split; [reflexivity|]. left. exists e. auto.
    + eexists _, _. split; [reflexivity|]. right. auto.
  - intros (eff & mo' & -> & [(e & He & -> & ->) | (Hfree & -> & ->)]).
    + left. exists e. auto.
    + right. auto.
Qed.

#[using="Type"] Lemma open_cov : forall ms mo path,
  at_nodeA segs (NOpen path) RNG ms -> minv mo -> m_halted mo = None ->
  node_cov (nstep (NOpen path)) ms mo.
Proof.
  intros ms mo path [(Hsvc & Ha0 & Hfl & Hnz & Hsl & Hdd & Hrom & Hp) HCOV] Hminv Hh. cbn [ncov] in HCOV.
  pose proof (path_reads_cov ms path Hrom Hp HCOV) as COVR.
  pose proof (bytes_at_in _ _ _ _ Hrom Hp) as Hin.
  assert (Hmfl : modeled_open_flags (areg ms 12) = true).
  { unfold modeled_open_flags. rewrite Hfl. reflexivity. }
  assert (Hdir : fd32 (areg ms 10) = AT_FDCWD32) by (rewrite Ha0; reflexivity).
  set (i := sys_input segs ms (Z_to_bv 64 56)).
  assert (Hsp : forall o, syscall_spec i mo o <-> openat_spec (fd32 (areg ms 10)) (areg ms 11) (areg ms 12) i mo o).
  { intros o. unfold i. rewrite syscall_spec_56 by (sysno 56). rewrite in_a0_si, in_a1_si, in_a2_si. reflexivity. }
  assert (Hmem : in_mem i = ms_read_byte ms) by reflexivity.
  set (R := open_reads i (areg ms 11)).
  (* [comment removed for export] *)
  assert (Hcstr : read_cstr (in_mem i) (areg ms 11) =
                  if (path_max <=? length path)%nat then CstrTooLong else CstrOk path).
  { rewrite Hmem. unfold read_cstr. rewrite <- (wa_unsigned_id (areg ms 11)).
    destruct (Nat.leb_spec0 path_max (length path)) as [Hlong|Hshort].
    - apply (read_cstr_aux_toolong_bytes_in path_max path); [exact Hlong|exact Hnz|].
      apply bytes_in_app in Hin as [Hin _]. exact Hin.
    - apply (read_cstr_aux_bytes_in path path_max); [lia|exact Hnz|exact Hin]. }
  (* [comment removed for export] *)
  assert (Hchar :
    (exists r mo1, (forall o, syscall_spec i mo o <-> o = Ok (with_copyins R (eff0 r)) mo1 []) /\
                   (forall eff mo' evs, nstep (NOpen path) mo eff mo' evs <-> (eff = eff0 r /\ mo' = mo1 /\ evs = [])) /\
                   mo1 = mo)
    \/ (exists ent, (forall o, syscall_spec i mo o <-> exists eff mo', o = Ok (with_copyins R eff) mo' [] /\ open_result mo ent eff mo') /\
                    (forall eff mo' evs, nstep (NOpen path) mo eff mo' evs <-> (evs = [] /\ open_result mo ent eff mo')) /\
                    match ent with FdDir => True | FdFile p _ => fs_lookup (m_fs mo) p <> None | _ => False end)).
  { cbn [nstep]. destruct (path_max <=? length path)%nat eqn:Elong.
    - left. exists (errno_ret ENAMETOOLONG), mo. split; [|split; [unfold efferr; tauto|reflexivity]].
      intros o. rewrite Hsp. apply (openat_toolong_outcome _ _ _ _ _ Hmfl). exact Hcstr.
    - destruct path as [|c path'].
      + left. exists (errno_ret ENOENT), mo. split; [|split; [unfold efferr; tauto|reflexivity]].
        intros o. rewrite Hsp. apply (openat_empty_outcome _ _ _ _ _ Hmfl). exact Hcstr.
      + destruct (path_eqb (c :: path') dot_path) eqn:Edot.
        * right. exists FdDir. apply path_eqb_eq in Edot. split; [|split; [tauto|exact I]].
          intros o. rewrite Hsp, <- open_out_result. apply (openat_dot_outcome _ _ _ _ _ Hmfl Hdir Hfl). rewrite Hcstr, Edot. reflexivity.
        * assert (Hnd : c :: path' <> dot_path).
          { intros E. rewrite E, path_eqb_refl in Edot. discriminate. }
          destruct (fs_lookup (m_fs mo) (c :: path')) as [d|] eqn:Efs.
          -- right. exists (FdFile (c :: path') (Z_to_bv 64 0)). split; [|split; [tauto|rewrite Efs; discriminate]].
             intros o. rewrite Hsp, <- open_out_result.
             apply (openat_file_outcome _ _ _ _ _ Hmfl Hdir Hfl (c :: path') d); [exact Hcstr|discriminate|exact Hnd|exact Hsl|exact Hdd|exact Efs].
          -- left. exists (errno_ret ENOENT), mo. split; [|split; [unfold efferr; tauto|reflexivity]].
             intros o. rewrite Hsp.
             apply (openat_absent_outcome _ _ _ _ _ Hmfl Hdir Hfl (c :: path')); [exact Hcstr|discriminate|exact Hnd|exact Hsl|exact Hdd|exact Efs]. }
  destruct Hchar as [(r & mo1 & Hc & Hn & ->) | (ent & Hc & Hn & Hent)].
  - eapply cov_det; [exact Hsvc|exact Hh|exact Hc|exact Hn|exact Hh|exact Hminv| exact COVR].
  - intros x8' eff mo' evs Hx Hsp'. rewrite Hsvc in Hx. injection Hx as <-. fold i in Hsp'.
    apply Hc in Hsp' as (eff' & mo'' & Heq & Hor). apply Ok_inj in Heq as (-> & _ & _).
    unfold open_result in Hor. destruct Hor as [(e & _ & -> & _) | (_ & -> & _)];
      unfold syscall_effect_accesses, with_copyins, efferr, eff0; cbn [eff_copyins eff_writes write_accesses];
      rewrite app_nil_r; exact COVR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Ltac cov_tac :=
  unfold syscall_effect_accesses, with_copyins, efferr, eff0;
  cbn [eff_copyins eff_writes write_accesses app];
  try solve [constructor].

(* [comment removed for export] *)
#[using="Type"] Lemma delivered_cov : forall (buf len : Z) (bs : list byte),
  rng RNG buf len -> 0 <= buf < 2^64 -> Z.of_nat (length bs) <= len ->
  Forall (acc_in RNG) (write_accesses (delivered_writes (Z_to_bv 64 buf) bs)).
Proof.
  intros buf len bs HR HB HL. unfold delivered_writes. destruct bs as [|b bs]; [constructor|].
  cbn [write_accesses]. eapply cov_one; [rewrite unsigned_lit by lia; exact HR| exact HL].
Qed.

#[using="Type"] Lemma read_cov : forall ms mo fd buf count,
  at_nodeA segs (NRead fd buf count) RNG ms -> minv mo -> m_halted mo = None ->
  node_cov (nstep (NRead fd buf count)) ms mo.
Proof.
  intros ms mo fd buf count [(Hsvc & Hfd & Ha0 & Ha1 & Ha2 & Hc & Hbc & Hwr) HCOV] Hminv Hh. cbn [ncov] in HCOV.
  unfold max_read in Hc.
  pose proof Hwr as (Hb0 & Hbn & _).
  set (i := sys_input segs ms (Z_to_bv 64 63)).
  assert (Hsp : forall o, syscall_spec i mo o <-> read_spec (Z_to_bv 64 fd) (Z_to_bv 64 buf) (Z_to_bv 64 count) i mo o).
  { intros o. unfold i. rewrite syscall_spec_63 by (sysno 63). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha1, Ha2.
    rewrite fd32_small by lia. reflexivity. }
  assert (Hwm : in_wmem i = wview segs (ms_mem ms)) by reflexivity.
  assert (Hmap : forall c, 0 <= c <= count -> exists w, read_bytes_map (in_wmem i) (Z_to_bv 64 buf) (Z_to_bv 64 c) = Some w).
  { intros c Hcc. rewrite Hwm. change (Z_to_bv 64 buf) with (wa buf). apply (read_bytes_map_wr_at segs _ buf count); [exact Hwr|].
    rewrite unsigned_lit by lia. lia. }
  (* [comment removed for export] *)
  assert (Hacc : access_okb (Z_to_bv 64 buf) (bv_unsigned (Z_to_bv 64 count)) = true).
  { rewrite !unsigned_lit by lia. unfold access_okb, TASK_SIZE. rewrite unsigned_lit by lia.
    apply andb_true_intro; split; apply Z.leb_le; lia. }
  unfold i in *; clear i. cbn [nstep].
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  - pose proof (proj1 (proj2 (proj2 (proj2 Hminv))) _ _ Hlk) as Hok. destruct e as [ch|p off|p off|p off|p off| |sk|pid w|rd wr| ]; cbn [fd_ok] in Hok.
    + (* [comment removed for export] *) exfalso. rewrite unsigned_lit in Hok by lia. lia.
    + (* [comment removed for export] *)
      destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs; [|exfalso; exact (Hok eq_refl)].
      cbv zeta. set (bs := file_read data off (Z_to_bv 64 count)).
      assert (Hcl : Z_to_bv 64 (rw_count_clamp (Z_to_bv 64 count)) = Z_to_bv 64 count).
      { rewrite rw_count_clamp_small by (rewrite unsigned_lit by lia; unfold MAX_RW_COUNT; lia).
        apply Z_to_bv_bv_unsigned. }
      assert (Hlen : Z.of_nat (length bs) <= count).
      { pose proof (length_file_read_le data off (Z_to_bv 64 count)) as L. fold bs in L.
        unfold word_to_nat in L. rewrite unsigned_lit in L by lia. lia. }
      destruct (Hmap (Z.of_nat (length bs)) ltac:(lia)) as [w Hw].
      eapply (cov_det0 _ ms mo (Z_to_bv 64 63) (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) [])
                (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo) []);
        [exact Hsvc|exact Hh| | |exact Hh|eapply minv_update_file; eassumption|cov_tac].
      * intros o. rewrite Hsp.
        pose proof (read_file_outcome (Z_to_bv 64 fd) (Z_to_bv 64 buf) (Z_to_bv 64 count) (sys_input segs ms (Z_to_bv 64 63)) mo o p off data w Hlk Hacc Hfs) as RF.
        cbv zeta in RF. rewrite Hcl in RF. fold bs in RF. rewrite RF; [unfold eff0; reflexivity|].
        unfold len_word. exact Hw.
      * intros eff mo' evs. cbn [nstep]. rewrite Hlk, Hfs. tauto.
      * rewrite ?app_nil_r. apply (delivered_cov buf count bs HCOV); [pose proof Hwr as (W0 & W1 & _); lia| exact Hlen].
    + (* [comment removed for export] *)
      eapply (cov_det0 _ ms mo (Z_to_bv 64 63) (efferr EBADF) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv|cov_tac].
      * intros o. rewrite Hsp. apply (read_filew_outcome _ _ _ _ _ _ p off Hlk).
      * intros eff mo' evs. cbn [nstep]. rewrite Hlk. tauto.
    + destruct Hok.
    + destruct Hok.
    + (* [comment removed for export] *)
      eapply (cov_det0 _ ms mo (Z_to_bv 64 63) (efferr EISDIR) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv|cov_tac].
      * intros o. rewrite Hsp. apply (read_dir_outcome _ _ _ _ _ _ Hlk Hacc).
      * intros eff mo' evs. cbn [nstep]. rewrite Hlk. tauto.
    + destruct Hok.
    + destruct Hok.
    + (* [comment removed for export] *)
      destruct Hok as [-> ->].
      eapply (cov_det0 _ ms mo (Z_to_bv 64 63) (efferr EBADF) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv|cov_tac].
      * intros o. rewrite Hsp. apply (read_null_outcome _ _ _ _ _ _ Hlk).
      * intros eff mo' evs. cbn [nstep]. rewrite Hlk. tauto.
    + destruct Hok.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    eapply (cov_det0 _ ms mo (Z_to_bv 64 63) (efferr EBADF) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv|cov_tac].
    * intros o. rewrite Hsp. apply (read_badfd_outcome _ _ _ _ _ _ Hlk).
    * intros eff mo' evs. cbn [nstep]. rewrite Hlk. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


#[using="Type"] Lemma close_cov : forall ms mo fd,
  at_node segs (NClose fd) ms -> minv mo -> m_halted mo = None ->
  node_cov (nstep (NClose fd)) ms mo.
Proof.
  intros ms mo fd (Hsvc & Hfd & Ha0) Hminv Hh.
  set (i := sys_input segs ms (Z_to_bv 64 57)).
  assert (Hsp : forall o, syscall_spec i mo o <-> close_spec (Z_to_bv 64 fd) i mo o).
  { intros o. unfold i. rewrite syscall_spec_57 by (sysno 57). rewrite in_a0_si, Ha0.
    rewrite fd32_small by lia. reflexivity. }
  unfold i in *; clear i. cbn [nstep]. destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  - eapply (cov_det0 _ ms mo (Z_to_bv 64 57) (eff0 (Z_to_bv 64 0)) (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo) []);
      [exact Hsvc|exact Hh| | |exact Hh|apply minv_remove; assumption|cov_tac].
    + intros o. rewrite Hsp. apply (close_outcome _ _ _ _ _ Hlk).
    + intros eff mo' evs. cbn [nstep]. rewrite Hlk. tauto.
  - eapply (cov_det0 _ ms mo (Z_to_bv 64 57) (efferr EBADF) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv|cov_tac].
    + intros o. rewrite Hsp. apply (close_badfd_outcome _ _ _ _ Hlk).
    + intros eff mo' evs. cbn [nstep]. rewrite Hlk. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma ioctl_cov : forall ms mo fd req,
  at_node segs (NIoctl fd req) ms -> minv mo -> m_halted mo = None ->
  node_cov (nstep (NIoctl fd req)) ms mo.
Proof.
  intros ms mo fd req (Hsvc & Hfd & Hreq & Ha0 & Ha1) Hminv Hh.
  set (i := sys_input segs ms (Z_to_bv 64 29)).
  assert (Hsp : forall o, syscall_spec i mo o <-> ioctl_spec (Z_to_bv 64 fd) (Z_to_bv 64 req) i mo o).
  { intros o. unfold i. rewrite syscall_spec_29 by (sysno 29). rewrite in_a0_si, in_a1_si, Ha0, Ha1.
    rewrite fd32_small by lia. unfold cmd32. rewrite abi_low32_small by lia. reflexivity. }
  assert (Htty : tty_only_request (Z_to_bv 64 req) = true) by (subst req; reflexivity).
  assert (Hwz : bv_eqb (Z_to_bv 64 req) TIOCGWINSZ = true) by (subst req; reflexivity).   (* [comment removed for export] *)
  unfold i in *; clear i. cbn [nstep]. destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  - eapply (cov_det0 _ ms mo (Z_to_bv 64 29) (efferr ENOTTY) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv|cov_tac].
    + intros o. rewrite Hsp. apply (ioctl_any_outcome _ _ _ _ _ e Hlk Htty Hwz (minv_not_urandom _ _ _ Hminv Hlk)).
    + intros eff mo' evs. cbn [nstep]. rewrite Hlk. tauto.
  - eapply (cov_det0 _ ms mo (Z_to_bv 64 29) (efferr EBADF) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv|cov_tac].
    + intros o. rewrite Hsp. apply (ioctl_badfd_outcome _ _ _ _ _ Hlk).
    + intros eff mo' evs. cbn [nstep]. rewrite Hlk. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


#[using="Type"] Lemma openw_cov : forall ms mo path mode,
  at_nodeA segs (NOpenW path mode) RNG ms -> minv mo -> m_halted mo = None ->
  node_cov (nstep (NOpenW path mode)) ms mo.
Proof.
  intros ms mo path mode [(Hsvc & Ha0 & Hfl & Ha3 & Hnz & Hslash & Hrom & Hp) HCOV] Hminv Hh. cbn [ncov] in HCOV.
  pose proof (path_reads_cov ms path Hrom Hp HCOV) as COVR.
  pose proof (bytes_at_in _ _ _ _ Hrom Hp) as Hin.
  assert (Hmfl : modeled_open_flags (areg ms 12) = true) by (apply modeled_open_flags_wr; exact Hfl).
  assert (Hdir : fd32 (areg ms 10) = AT_FDCWD32) by (rewrite Ha0; reflexivity).
  set (i := sys_input segs ms (Z_to_bv 64 56)).
  assert (Hsp : forall o, syscall_spec i mo o <-> openat_spec (fd32 (areg ms 10)) (areg ms 11) (areg ms 12) i mo o).
  { intros o. unfold i. rewrite syscall_spec_56 by (sysno 56). rewrite in_a0_si, in_a1_si, in_a2_si. reflexivity. }
  assert (Hmem : in_mem i = ms_read_byte ms) by reflexivity.
  set (R := open_reads i (areg ms 11)).
  assert (Hcstr : read_cstr (in_mem i) (areg ms 11) =
                  if (path_max <=? length path)%nat then CstrTooLong else CstrOk path).
  { rewrite Hmem. unfold read_cstr. rewrite <- (wa_unsigned_id (areg ms 11)).
    destruct (Nat.leb_spec0 path_max (length path)) as [Hlong|Hshort].
    - apply (read_cstr_aux_toolong_bytes_in path_max path); [exact Hlong|exact Hnz|].
      apply bytes_in_app in Hin as [Hin _]. exact Hin.
    - apply (read_cstr_aux_bytes_in path path_max); [lia|exact Hnz|exact Hin]. }
  (* [comment removed for export] *)
  assert (Hchar :
    (exists r, (forall o, syscall_spec i mo o <-> o = Ok (with_copyins R (eff0 r)) mo []) /\
               (forall eff mo' evs, nstep (NOpenW path mode) mo eff mo' evs <-> (eff = eff0 r /\ mo' = mo /\ evs = [])))
    \/ (exists OR : resp -> Model -> Prop,
        (forall o, syscall_spec i mo o <-> exists eff mo', o = Ok (with_copyins R eff) mo' [] /\ OR eff mo') /\
        (forall eff mo' evs, nstep (NOpenW path mode) mo eff mo' evs <-> (evs = [] /\ OR eff mo')) /\
        (forall eff mo', OR eff mo' -> m_halted mo' = None /\ minv mo') /\
        OR (efferr ENOMEM) mo /\
        (forall eff mo', OR eff mo' -> eff_writes eff = []))).
  { cbn [nstep]. destruct (path_max <=? length path)%nat eqn:Elong.
    - left. exists (errno_ret ENAMETOOLONG). split; [|unfold efferr; tauto].
      intros o. rewrite Hsp. apply (openat_toolong_outcome _ _ _ _ _ Hmfl). exact Hcstr.
    - destruct path as [|c path'].
      + left. exists (errno_ret ENOENT). split; [|unfold efferr; tauto].
        intros o. rewrite Hsp. apply (openat_empty_outcome _ _ _ _ _ Hmfl). exact Hcstr.
      + destruct (path_eqb (c :: path') devnull_path) eqn:Edn.
        * (* [comment removed for export] *)
          apply path_eqb_eq in Edn. right. exists (open_result mo FdNull). split; [|split; [tauto|split; [|split]]].
          -- intros o. rewrite Hsp, <- open_out_result.
             destruct (minv_devnull_absent mo Hminv) as [Hdl Hdu].
             apply (openat_devnull_outcome _ _ _ _ _ Hdir Hfl); [rewrite Hcstr, Edn; reflexivity|exact Hdl|exact Hdu].
          -- intros eff mo' [(e & _ & _ & ->) | (Hfree & _ & ->)]; [auto|].
             split; [exact Hh|]. apply minv_open_insert; [exact Hminv|exact Hfree|exact I].
          -- left. exists ENOMEM. split; [left; reflexivity|auto].
          -- intros eff mo' [(e & _ & -> & _) | (_ & -> & _)]; reflexivity.
        * assert (Hsl : path_has_slash (c :: path') = false).
          { destruct Hslash as [Hs|Hs]; [exact Hs|]. rewrite Hs, path_eqb_refl in Edn. discriminate. }
          rewrite Hsl.
          destruct (write_dirref (c :: path') mo) eqn:Edir.
          -- left. exists (errno_ret EISDIR). split; [|unfold efferr; tauto].
             intros o. rewrite Hsp.
             apply (openat_create_dirref_outcome _ _ _ _ _ Hdir Hfl (c :: path')); [exact Hcstr|discriminate|exact Hsl|exact Edir].
          -- right. exists (openw_result mo (c :: path')). split; [|split; [tauto|split; [|split]]].
             ++ intros o. rewrite Hsp. rewrite (openat_create_outcome _ _ _ _ _ Hdir Hfl (c :: path')); [|exact Hcstr|discriminate|exact Hsl|exact Edir].
                unfold open_out, openw_result, efferr, eff0. split.
                ** intros [(e & He & ->) | (Hfree & ->)]; eexists _, _; (split; [reflexivity|]); [left; exists e; auto| right; auto].
                ** intros (eff & mo' & -> & [(e & He & -> & ->) | (Hfree & -> & ->)]); [left; exists e; auto| right; auto].
             ++ intros eff mo' [(e & _ & _ & ->) | (Hfree & _ & ->)]; [auto|].
                split; [exact Hh|]. apply minv_openw_insert; [exact Hminv|exact Hfree|exact Hsl].
             ++ left. exists ENOMEM. split; [left; reflexivity|auto].
             ++ intros eff mo' [(e & _ & -> & _) | (_ & -> & _)]; reflexivity. }
  destruct Hchar as [(r & Hc & Hn) | (OR & Hc & Hn & Hpres & Hprog & Hw)].
  - eapply cov_det; [exact Hsvc|exact Hh|exact Hc|exact Hn|exact Hh|exact Hminv|exact COVR].
  - intros x8' eff mo' evs Hx Hsp'. rewrite Hsvc in Hx. injection Hx as <-. fold i in Hsp'.
    apply Hc in Hsp' as (eff' & mo'' & Heq & Hor). apply Ok_inj in Heq as (-> & _ & _).
    unfold syscall_effect_accesses, with_copyins. cbn [eff_copyins eff_writes]. rewrite (Hw _ _ Hor).
    cbn [write_accesses]. rewrite app_nil_r. exact COVR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma writevf_cov : forall ms mo fd bufs,
  at_nodeA segs (NWritevF fd bufs) RNG ms -> minv mo -> m_halted mo = None -> nsafe (NWritevF fd bufs) mo ->
  node_cov (nstep (NWritevF fd bufs)) ms mo.
Proof.
  intros ms mo fd bufs (Hsvc & Hfd & Ha0 & Ha2 & Hcnt & Harr & Htot & Hrom & HRarr & iovs & Hiov & HbufsR) Hminv Hh Hsafe.
  destruct (gather_cov_lens ms iovs bufs HbufsR) as [HRl HRb].
  assert (Hbufs : Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                                         bv_unsigned (fst iov) + Z.of_nat (length bs) <= 2^47 /\
                                         bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs).
  { eapply Forall2_impl; [| exact HbufsR]. cbn. intros a b (X & X2 & Y & _). auto. }
  assert (HCarr : Forall (acc_in RNG) (import_iovecs_accesses (ms_read_byte ms) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs)))))).
  { unfold iovcnt32. rewrite abi_low32_small by lia. apply import_iovecs_accesses_cov; [exact HRarr| lia| lia]. }
  unfold max_write in Htot.
  pose proof (iovs_ok_of_at _ _ _ _ Hrom Hbufs ltac:(lia)) as Hok.
  pose proof (iovs_range_of_at _ _ _ _ Hbufs) as Hrng.
  pose proof (Forall2_length Hbufs) as Hleq.
  pose proof (iovs_total_ok _ _ _ Hok) as Htotal.
  set (bs := concat bufs) in *.
  assert (Hlw : len_word bs = Z_to_bv 64 (Z.of_nat (length bs))) by reflexivity.
  assert (C1 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs))) = Z_to_bv 64 (Z.of_nat (length bufs))) by (unfold iovcnt32; apply abi_low32_small; lia).
  assert (Himp : import_iovecs (in_mem (sys_input segs ms (Z_to_bv 64 66))) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs)))) = ImpOk iovs).
  { rewrite in_mem_si, C1, <- Hleq. apply import_iovecs_ok; [lia| rewrite Hleq; exact Harr | eapply bytes_at_in; eassumption | exact Hrng]. }
  assert (C5 : iovs_total iovs <= MAX_RW_COUNT) by (rewrite Htotal; unfold MAX_RW_COUNT; subst bs; lia).
  destruct Hsafe as [(p & off & data & Hlk & Hfs & Hgap & Hpos) | Hlk].
  - (* [comment removed for export] *)
    eapply (cov_det_gen _ ms mo (Z_to_bv 64 66)
              (mkEffectU (len_word bs) [] [] [] []
                 (import_iovecs_accesses (ms_read_byte ms) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs))))
                  ++ iov_prefix_accesses iovs (length bs)))
              (eff0 (Z_to_bv 64 (Z.of_nat (length bs))))
              (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFileW p (off + len_word bs)%bv))
                 (with_fs (fs_set (m_fs mo) p (file_write data off bs)) mo)) []);
      [exact Hsvc|exact Hh| |reflexivity| |exact Hh|eapply minv_write_filew; eassumption|cov_tac].
    + intros o. rewrite syscall_spec_66 by (sysno 66). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2.
      rewrite fd32_small by lia.
      assert (C6 : gather_iovecs (in_mem (sys_input segs ms (Z_to_bv 64 66))) iovs = Some bs) by (rewrite in_mem_si; apply gather_iovecs_ok; exact Hok).
      assert (C7 : 1 <= Z.of_nat (length bs)) by (subst bs; lia).
      assert (C8 : bv_unsigned off + iovs_total iovs <= 2^63 - 1) by (rewrite Htotal; exact Hpos).
      pose proof (writev_file_outcome (Z_to_bv 64 fd) (areg ms 11) _ _ mo o p off data iovs bs Hlk Hfs Hgap Himp C5 C8 C6 C7) as W.
      cbv zeta in W. rewrite in_mem_si in W. exact W.
    + intros eff mo' evs. cbn [nstep]. rewrite Hlk, Hfs. cbv zeta. fold bs. rewrite <- Hlw. unfold eff0. tauto.
    + rewrite ?app_nil_r. apply Forall_app. split; [exact HCarr| exact (iov_prefix_cov iovs _ HRl HRb _)].
  - (* [comment removed for export] *)
    eapply (cov_det_gen _ ms mo (Z_to_bv 64 66)
              (with_copyins (import_iovecs_accesses (ms_read_byte ms) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length bufs)))))
                 (mkEffect (Z_to_bv 64 (iovs_total iovs)) [] []))
              (eff0 (Z_to_bv 64 (Z.of_nat (length bs))))
              mo []);
      [exact Hsvc|exact Hh| | | |exact Hh|exact Hminv|cov_tac].
    + intros o. rewrite syscall_spec_66 by (sysno 66). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2.
      rewrite fd32_small by lia.
      pose proof (writev_null_outcome (Z_to_bv 64 fd) (areg ms 11) _ _ mo o iovs Hlk Himp C5) as W.
      rewrite in_mem_si in W. exact W.
    + rewrite Htotal. reflexivity.
    + intros eff mo' evs. cbn [nstep]. rewrite Hlk. fold bs. tauto.
    + rewrite ?app_nil_r. exact HCarr.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


#[using="Type"] Lemma lseek_cov : forall ms mo fd off whence,
  at_node segs (NLseek fd off whence) ms -> minv mo -> m_halted mo = None -> nsafe (NLseek fd off whence) mo ->
  node_cov (nstep (NLseek fd off whence)) ms mo.
Proof.
  intros ms mo fd off whence (Hsvc & Hfd & Hwh & Ha0 & Ha1 & Ha2) Hminv Hh Hsafe. cbn [nsafe] in Hsafe.
  set (i := sys_input segs ms (Z_to_bv 64 62)).
  assert (Hsp : forall o, syscall_spec i mo o <-> lseek_spec (Z_to_bv 64 fd) (Z_to_bv 64 off) (Z_to_bv 64 whence) i mo o).
  { intros o. unfold i. rewrite syscall_spec_62 by (sysno 62). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha1, Ha2.
    rewrite fd32_small by lia. unfold whence32. rewrite abi_low32_small by lia. reflexivity. }
  assert (Hbase : forall cur len, exists b, lseek_base (Z_to_bv 64 whence) cur len = Some b).
  { intros cur len. unfold lseek_base. rewrite unsigned_lit by lia. unfold SEEK_SET, SEEK_CUR, SEEK_END.
    destruct (Z.eqb_spec whence 0); [eexists; reflexivity|]. destruct (Z.eqb_spec whence 1); [eexists; reflexivity|].
    destruct (Z.eqb_spec whence 2); [eexists; reflexivity|]. lia. }
  unfold i in *; clear i. cbn [nstep].
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  - pose proof (proj1 (proj2 (proj2 (proj2 Hminv))) _ _ Hlk) as Hok.
    destruct e as [ch|p cur|p cur|p cur|p cur| |sk|pid w|rd wr| ]; cbn [fd_ok] in Hok; try (destruct Hok; fail); try congruence.
    + exfalso. rewrite unsigned_lit in Hok by lia. lia.
    + (* [comment removed for export] *)
      destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs; [|exfalso; exact (Hok eq_refl)].
      destruct (Hbase cur (len_word data)) as [b Hb].
      pose proof (fun o => lseek_file_outcome (Z_to_bv 64 fd) (Z_to_bv 64 off) (Z_to_bv 64 whence) (sys_input segs ms (Z_to_bv 64 62)) mo o p cur data b Hlk Hfs Hb) as Hout.
      unfold lseek_out in Hout.
      destruct (lseek_dest b (Z_to_bv 64 off)) as [r|] eqn:Hd.
      * eapply (cov_det0 _ ms mo (Z_to_bv 64 62) (eff0 r) (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p r)) mo) []);
          [exact Hsvc|exact Hh| | |exact Hh|eapply minv_update_file; eassumption|cov_tac].
        -- intros o. rewrite Hsp. apply Hout.
        -- intros eff mo' evs. cbn [nstep]. rewrite Hlk, Hfs, Hb. unfold lseek_result. rewrite Hd. unfold eff0. tauto.
      * eapply (cov_det0 _ ms mo (Z_to_bv 64 62) (efferr EINVAL) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv|cov_tac].
        -- intros o. rewrite Hsp. apply Hout.
        -- intros eff mo' evs. cbn [nstep]. rewrite Hlk, Hfs, Hb. unfold lseek_result. rewrite Hd. unfold efferr, eff0. tauto.
    + (* [comment removed for export] *)
      destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs; [|exfalso; exact (Hok eq_refl)].
      destruct (Hbase cur (len_word data)) as [b Hb].
      pose proof (fun o => lseek_filew_outcome (Z_to_bv 64 fd) (Z_to_bv 64 off) (Z_to_bv 64 whence) (sys_input segs ms (Z_to_bv 64 62)) mo o p cur data b Hlk Hfs Hb) as Hout.
      unfold lseek_out in Hout.
      destruct (lseek_dest b (Z_to_bv 64 off)) as [r|] eqn:Hd.
      * eapply (cov_det0 _ ms mo (Z_to_bv 64 62) (eff0 r) (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFileW p r)) mo) []);
          [exact Hsvc|exact Hh| | |exact Hh|eapply minv_update_filew; eassumption|cov_tac].
        -- intros o. rewrite Hsp. apply Hout.
        -- intros eff mo' evs. cbn [nstep]. rewrite Hlk, Hfs, Hb. unfold lseek_result. rewrite Hd. unfold eff0. tauto.
      * eapply (cov_det0 _ ms mo (Z_to_bv 64 62) (efferr EINVAL) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv|cov_tac].
        -- intros o. rewrite Hsp. apply Hout.
        -- intros eff mo' evs. cbn [nstep]. rewrite Hlk, Hfs, Hb. unfold lseek_result. rewrite Hd. unfold efferr, eff0. tauto.
    + (* [comment removed for export] *)
      destruct Hok as [-> ->].
      eapply (cov_det0 _ ms mo (Z_to_bv 64 62) (eff0 (Z_to_bv 64 0)) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv|cov_tac].
      * intros o. rewrite Hsp. apply (lseek_null_outcome _ _ _ _ _ _ Hlk). rewrite unsigned_lit by lia. unfold SEEK_MAX. lia.
      * intros eff mo' evs. cbn [nstep]. rewrite Hlk. unfold eff0. tauto.
  - (* [comment removed for export] *)
    eapply (cov_det0 _ ms mo (Z_to_bv 64 62) (efferr EBADF) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv|cov_tac].
    + intros o. rewrite Hsp. apply (lseek_badfd_outcome _ _ _ _ _ _ Hlk).
    + intros eff mo' evs. cbn [nstep]. rewrite Hlk. unfold efferr, eff0. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


#[using="Type"] Lemma unlink_cov : forall ms mo path rmdir,
  at_nodeA segs (NUnlink path rmdir) RNG ms -> minv mo -> m_halted mo = None -> nsafe (NUnlink path rmdir) mo ->
  node_cov (nstep (NUnlink path rmdir)) ms mo.
Proof.
  intros ms mo path rmdir [(Hsvc & Ha0 & Ha2 & Hnz & Hne & Hnd & Hndd & Hsl & Hlen & Hrom & Hp) HCOV] Hminv Hh Hsafe. cbn [nsafe] in Hsafe.
  cbn [ncov] in HCOV. pose proof (path_reads_cov ms path Hrom Hp HCOV) as COVR.
  pose proof (bytes_at_in _ _ _ _ Hrom Hp) as Hin.
  set (i := sys_input segs ms (Z_to_bv 64 35)).
  assert (Hfl : modeled_unlink_flags (areg ms 12) = true).
  { rewrite Ha2. unfold modeled_unlink_flags, flag32. destruct rmdir; reflexivity. }
  assert (Hrm : unlink_rmdir (areg ms 12) = rmdir).
  { rewrite Ha2. unfold unlink_rmdir, flag32. destruct rmdir; reflexivity. }
  assert (Hdir : fd32 (areg ms 10) = AT_FDCWD32) by (rewrite Ha0; reflexivity).
  assert (Hcstr : read_cstr (in_mem i) (areg ms 11) = CstrOk path).
  { change (in_mem i) with (ms_read_byte ms). unfold read_cstr. rewrite <- (wa_unsigned_id (areg ms 11)).
    apply (read_cstr_aux_bytes_in path path_max); [unfold path_max; unfold NAME_MAX in Hlen; lia|exact Hnz|exact Hin]. }
  destruct Hsafe as [Hu Hnames].
  assert (Hsp : forall o, syscall_spec i mo o <-> unlink_out (unlink_reads i (areg ms 11)) mo path rmdir o).
  { intros o. unfold i. rewrite syscall_spec_35 by (sysno 35). rewrite in_a0_si, in_a1_si, in_a2_si. fold i. rewrite <- Hrm.
    apply (unlinkat_outcome _ _ _ i mo o path Hdir Hfl Hcstr Hne Hnd Hndd Hsl Hlen Hu). rewrite Hrm. exact Hnames. }
  set (R := unlink_reads i (areg ms 11)) in *.
  unfold unlink_out in Hsp. unfold i in *; clear i. cbn [nstep].
  destruct (fs_lookup (m_fs mo) path) as [d|] eqn:Hl.
  2:{ eapply (cov_det _ ms mo (Z_to_bv 64 35) (errno_ret ENOENT) R mo []); [exact Hsvc|exact Hh|exact Hsp| |exact Hh|exact Hminv|exact COVR].
      intros eff mo' evs. cbn [nstep]. rewrite Hsl, Hu, Hl. unfold efferr, eff0. tauto. }
  destruct rmdir.
  { eapply (cov_det _ ms mo (Z_to_bv 64 35) (errno_ret ENOTDIR) R mo []); [exact Hsvc|exact Hh|exact Hsp| |exact Hh|exact Hminv|exact COVR].
    intros eff mo' evs. cbn [nstep]. rewrite Hsl, Hu, Hl. unfold efferr, eff0. tauto. }
  intros x8' eff mo' evs Hx Hsp'. rewrite Hsvc in Hx. injection Hx as <-.
  apply Hsp in Hsp' as [(e & He & Heq) | Heq]; apply Ok_inj in Heq as (-> & _ & _);
    unfold syscall_effect_accesses, with_copyins, efferr, eff0; cbn [eff_copyins eff_writes write_accesses];
    rewrite app_nil_r; exact COVR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
#[using="Type"] Lemma scatterw_cov : forall (iovs : list (word * word)) (bs : list byte),
  Forall (fun iov => rng RNG (bv_unsigned (fst iov)) (bv_unsigned (snd iov))) iovs ->
  Forall (acc_in RNG) (write_accesses (scatterw iovs bs)).
Proof.
  induction iovs as [|[base len] rest IH]; intros bs HF.
  - destruct bs; constructor.
  - inversion HF as [|? ? HR HF']; subst. cbn [fst snd] in HR.
    destruct bs as [|b0 bs0]; [constructor|]. cbn [scatterw]. cbv zeta.
    set (n := word_to_nat_bounded len (length (b0 :: bs0))).
    destruct (firstn n (b0 :: bs0)) as [|h hs] eqn:EF; [apply IH; exact HF'|].
    cbn [write_accesses]. constructor; [| apply IH; exact HF'].
    eapply rng_acc_var; [exact HR|].
    assert (L : (length (h :: hs) <= n)%nat) by (rewrite <- EF; apply firstn_le_length).
    unfold n in L. rewrite word_to_nat_bounded_eq_min in L. unfold word_to_nat in L.
    pose proof (bv_unsigned_in_range 64 len). lia.
Qed.

#[using="Type"] Lemma readv_cov : forall ms mo fd dsts,
  at_nodeA segs (NReadv fd dsts) RNG ms -> minv mo -> m_halted mo = None -> nsafe (NReadv fd dsts) mo ->
  node_cov (nstep (NReadv fd dsts)) ms mo.
Proof.
  intros ms mo fd dsts [(Hsvc & Hfd & Ha0 & Ha2 & Hn & Harr & Hfirst & Htot & Hdsts & Hrom & Hiov) [HCarr0 HCd]] Hminv Hh Hsafe.
  assert (HCarr : Forall (acc_in RNG) (import_iovecs_accesses (ms_read_byte ms) (areg ms 11) (Z_to_bv 64 (Z.of_nat (length dsts))))).
  { apply import_iovecs_accesses_cov; [exact HCarr0| lia| lia]. }
  assert (HCw : forall bs, Forall (acc_in RNG) (write_accesses (scatterw (iovs_of dsts) bs))).
  { intros bs. apply scatterw_cov. unfold iovs_of. apply Forall_map.
    rewrite Forall_forall in HCd, Hdsts |- *. intros [bb ll] Hd. specialize (HCd _ Hd). specialize (Hdsts _ Hd).
    cbn [fst snd] in *. destruct Hdsts as (D0 & D1 & (W0 & _)). rewrite !unsigned_lit by lia. exact HCd. }
  cbn [nsafe] in Hsafe.
  unfold MAX_RW_COUNT in Htot.
  pose proof (bytes_at_in _ _ _ _ Hrom Hiov) as Hin. pose proof (bv_unsigned_in_range 64 (areg ms 11)) as Ha11.
  set (iovs := iovs_of dsts) in *.
  assert (Hr3 : Forall (fun d => 0 <= snd d /\ fst d + snd d <= 2^47 /\ 0 <= fst d) dsts).
  { apply Forall_impl with (2 := Hdsts). intros [b l] (H1 & H2 & (H3 & _ & _)). cbn [fst snd] in *. lia. }
  pose proof (iovs_total_of dsts ltac:(apply Forall_impl with (2 := Hr3); intros [? ?] (? & ? & ?); cbn [fst snd] in *; lia)) as Htotal.
  fold iovs in Htotal.
  assert (Hposd : 1 <= dsts_total dsts).
  { destruct dsts as [|[b0 l0] r]; [destruct Hfirst|]. cbn. apply Forall_cons_iff in Hr3 as [_ Hr].
    pose proof (dsts_total_nonneg r ltac:(apply Forall_impl with (2 := Hr); intros [? ?] (? & ? & ?); assumption)). lia. }
  assert (Hleniovs : length iovs = length dsts) by (subst iovs; apply length_iovs_of).
  set (i := sys_input segs ms (Z_to_bv 64 65)).
  assert (Hsp : forall o, syscall_spec i mo o <-> readv_spec (Z_to_bv 64 fd) (areg ms 11) (Z_to_bv 64 (Z.of_nat (length dsts))) i mo o).
  { intros o. unfold i. rewrite syscall_spec_65 by (sysno 65). rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2.
    rewrite fd32_small by lia. reflexivity. }
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length dsts))) = Z_to_bv 64 (Z.of_nat (length dsts))).
  { unfold iovcnt32. apply abi_low32_small. lia. }
  assert (Hcnt : bv_unsigned (Z_to_bv 64 (Z.of_nat (length dsts))) <= UIO_FASTIOV).
  { rewrite unsigned_lit by lia. unfold UIO_FASTIOV. lia. }
  assert (Himp : import_iovecs (in_mem i) (areg ms 11) (Z_to_bv 64 (Z.of_nat (length dsts))) = ImpOk iovs).
  { rewrite <- Hleniovs. apply import_iovecs_ok; [lia| lia | exact Hin |].
    subst iovs. unfold iovs_of. apply Forall_map. apply Forall_impl with (2 := Hr3).
    intros [b l] (H1 & H2 & H3). cbn [fst snd] in *. rewrite !unsigned_lit by lia. lia. }
  assert (Htotr : 1 <= iovs_total iovs <= MAX_RW_COUNT) by (rewrite Htotal; unfold MAX_RW_COUNT; lia).
  assert (Hwm : in_wmem i = wview segs (ms_mem ms)) by reflexivity.
  assert (Hwr : Forall (iov_writable (in_wmem i)) iovs).
  { rewrite Hwm. subst iovs. unfold iovs_of. apply Forall_map. apply Forall_impl with (2 := Hdsts).
    intros [b l] (H1 & H2 & H3). cbn [fst snd] in H1, H2, H3. pose proof H3 as (Hb0 & _ & _). intros n Hnl. cbn [fst snd] in Hnl |- *.
    rewrite unsigned_lit in Hnl by lia.
    destruct (read_bytes_map_wr_at segs (ms_mem ms) b l (Z_to_bv 64 (Z.of_nat n)) H3 ltac:(rewrite unsigned_lit by lia; lia)) as [w Hw].
    change (Z_to_bv 64 b) with (wa b). rewrite Hw. discriminate. }
  unfold i in *; clear i. cbn [nstep]. fold iovs.
  destruct (fd_lookup (m_fds mo) (Z_to_bv 64 fd)) as [e|] eqn:Hlk.
  - pose proof (proj1 (proj2 (proj2 (proj2 Hminv))) _ _ Hlk) as Hok. destruct e as [ch|p off|p off|p off|p off| |sk|pid w|rd wr| ]; cbn [fd_ok] in Hok.
    + exfalso. rewrite unsigned_lit in Hok by lia. lia.
    + (* [comment removed for export] *)
      destruct (fs_lookup (m_fs mo) p) as [data|] eqn:Hfs; [|exfalso; exact (Hok eq_refl)].
      cbv zeta. set (bs := file_read data off (Z_to_bv 64 (iovs_total iovs))).
      assert (Hpos : bv_unsigned off + iovs_total iovs <= 2^63 - 1) by (rewrite Htotal; exact (Hsafe p off eq_refl)).
      eapply (cov_det_gen _ ms mo (Z_to_bv 64 65)
                (mkEffectU (len_word bs) (scatterw iovs bs) [] [] [] (import_iovecs_accesses (ms_read_byte ms) (areg ms 11) (Z_to_bv 64 (Z.of_nat (length dsts)))))
                (mkEffect (len_word bs) (scatterw iovs bs) [])
                (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) mo) []);
        [exact Hsvc|exact Hh| |reflexivity| |exact Hh|eapply minv_update_file; eassumption|cov_tac].
      * intros o. rewrite Hsp.
        pose proof (readv_file_outcome (Z_to_bv 64 fd) (areg ms 11) _ (sys_input segs ms (Z_to_bv 64 65)) mo o p off data iovs Hlk Hfs Hcnt32 Hcnt Himp Htotr Hpos Hwr) as W.
        cbv zeta in W. fold bs in W. rewrite in_mem_si in W. exact W.
      * intros eff mo' evs. cbn [nstep]. rewrite Hlk, Hfs. cbv zeta. fold iovs bs. tauto.
      * apply Forall_app. split; [exact HCarr| apply HCw].
    + (* [comment removed for export] *)
      eapply (cov_det0 _ ms mo (Z_to_bv 64 65) (efferr EBADF) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv|cov_tac].
      * intros o. rewrite Hsp. apply (readv_filew_outcome _ _ _ _ _ _ p off Hlk).
      * intros eff mo' evs. cbn [nstep]. rewrite Hlk. unfold efferr, eff0. tauto.
    + destruct Hok.
    + destruct Hok.
    + (* [comment removed for export] *)
      eapply (cov_det_gen _ ms mo (Z_to_bv 64 65)
                (mkEffectU (errno_ret EISDIR) [] [] [] [] (import_iovecs_accesses (ms_read_byte ms) (areg ms 11) (Z_to_bv 64 (Z.of_nat (length dsts)))))
                (efferr EISDIR) mo []);
        [exact Hsvc|exact Hh| |reflexivity| |exact Hh|exact Hminv|cov_tac].
      * intros o. rewrite Hsp.
        pose proof (readv_dir_outcome (Z_to_bv 64 fd) (areg ms 11) _ (sys_input segs ms (Z_to_bv 64 65)) mo o iovs Hlk Hcnt32 Hcnt Himp Htotr) as W.
        rewrite in_mem_si in W. exact W.
      * intros eff mo' evs. cbn [nstep]. rewrite Hlk. unfold efferr, eff0. tauto.
      * rewrite ?app_nil_r. exact HCarr.
    + destruct Hok.
    + destruct Hok.
    + (* [comment removed for export] *)
      destruct Hok as [-> ->].
      eapply (cov_det0 _ ms mo (Z_to_bv 64 65) (efferr EBADF) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv|cov_tac].
      * intros o. rewrite Hsp. apply (readv_null_outcome _ _ _ _ _ _ Hlk).
      * intros eff mo' evs. cbn [nstep]. rewrite Hlk. unfold efferr, eff0. tauto.
    + destruct Hok.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    eapply (cov_det0 _ ms mo (Z_to_bv 64 65) (efferr EBADF) mo []); [exact Hsvc|exact Hh| | |exact Hh|exact Hminv|cov_tac].
    * intros o. rewrite Hsp. apply (readv_badfd_outcome _ _ _ _ _ _ Hlk).
    * intros eff mo' evs. cbn [nstep]. rewrite Hlk. unfold efferr, eff0. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


End Cov.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem fs_cov_holds : forall segs, fs_cov segs.
Proof.
  intros segs n RNG ms mo x8 eff mo' evs Hfs Hat Hx Hminv Hh Hsafe Hsp.
  pose proof (at_nodeA_at_node _ _ _ _ Hat) as Hat0.
  destruct n; try contradiction.
  - exact (write_cov segs RNG ms mo _ _ Hat Hminv Hh x8 eff mo' evs Hx Hsp).
  - exact (writev_cov segs RNG ms mo _ _ Hat Hminv Hh x8 eff mo' evs Hx Hsp).
  - exact (open_cov segs RNG ms mo _ Hat Hminv Hh x8 eff mo' evs Hx Hsp).
  - exact (read_cov segs RNG ms mo _ _ _ Hat Hminv Hh x8 eff mo' evs Hx Hsp).
  - exact (close_cov segs RNG ms mo _ Hat0 Hminv Hh x8 eff mo' evs Hx Hsp).
  - exact (ioctl_cov segs RNG ms mo _ _ Hat0 Hminv Hh x8 eff mo' evs Hx Hsp).
  - exact (openw_cov segs RNG ms mo _ _ Hat Hminv Hh x8 eff mo' evs Hx Hsp).
  - exact (writevf_cov segs RNG ms mo _ _ Hat Hminv Hh Hsafe x8 eff mo' evs Hx Hsp).
  - exact (readv_cov segs RNG ms mo _ _ Hat Hminv Hh Hsafe x8 eff mo' evs Hx Hsp).
  - exact (unlink_cov segs RNG ms mo _ _ Hat Hminv Hh Hsafe x8 eff mo' evs Hx Hsp).
  - exact (lseek_cov segs RNG ms mo _ _ _ Hat0 Hminv Hh Hsafe x8 eff mo' evs Hx Hsp).
Qed.

(* [comment removed for export] *)
Theorem nodesA_sound_closed : forall segs NMAX SHM,
  node_soundA node segs (at_nodeA segs) (npeekA segs) nstepA nexitA (minvA SHM) (nsafeA NMAX SHM) NMAX.
Proof. intros segs NMAX SHM. apply nodesA_sound. apply fs_cov_holds. Qed.
