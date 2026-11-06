(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec CatSim PropExec ShapeAlg Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AgentLib RefNodes.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefNodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Lazyiq4.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma srz_close_hull : forall ms model x8 (fd : word) e (K : TSet),
  m_halted model = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 57%Z ->
  ms_gpr ms 0 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) (with_fds (fd_remove (m_fds model) fd) model)) K ->
  srealizes segs (mkCfg ms model) K.
Proof.
  intros ms model x8 fd e K Hh Hsvc Hno H0 Hfd32 Hlk Hc.
  eapply srz_ret_only_silent_nil; [exact Hh | exact Hsvc | | | exact Hc].
  - intros o. rewrite (syscall_spec_57 _ model o) by (rewrite in_sysno_si; exact Hno).
    rewrite in_arg0_si, H0, (fd32_id fd Hfd32). exact (close_outcome fd _ model e o Hlk).
  - rewrite with_fds_halted. exact Hh.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma srz_ioctl_winsz_hull : forall ms model x8 (fd : word) (c : word) (K : TSet),
  m_halted model = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 29%Z ->
  ms_gpr ms 0 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdChannel c) ->
  ms_gpr ms 1 = Z_to_bv 64 0x5413 ->
  srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret ENOTTY))) model) K ->
  srealizes segs (mkCfg ms model) K.
Proof.
  intros ms model x8 fd c K Hh Hsvc Hno H0 Hfd32 Hlk H1 Hc.
  eapply srz_ret_only_silent_nil; [exact Hh | exact Hsvc | | exact Hh | exact Hc].
  intros o. rewrite (syscall_spec_29 _ model o) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, H0, (fd32_id fd Hfd32), H1.
  apply (ioctl_tty_outcome fd _ _ model c o Hlk). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma srz_read_dir_hull : forall ms model x8 (fd : word) (cnt : Z) (K : TSet),
  m_halted model = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 63%Z ->
  ms_gpr ms 0 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  ms_gpr ms 2 = Z_to_bv 64 cnt -> (1 <= cnt <= MAX_RW_COUNT)%Z ->
  (bv_unsigned (ms_gpr ms 1) + cnt <= TASK_SIZE)%Z ->
  store_ok segs (ms_mem ms) (ms_gpr ms 1) (Z.to_nat cnt) = true ->
  srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret EISDIR))) model) K ->
  srealizes segs (mkCfg ms model) K.
Proof.
  intros ms model x8 fd cnt K Hh Hsvc Hno H0 Hfd32 Hlk H2 Hcnt Hover Hok Hc.
  eapply srz_ret_only_silent_nil; [exact Hh | exact Hsvc | | exact Hh | exact Hc].
  intros o. rewrite (syscall_spec_63 _ model o) by (rewrite in_sysno_si; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, (fd32_id fd Hfd32).
  apply (read_dir_outcome fd _ _ _ model o Hlk). apply access_okb_intro.
  rewrite H2, u64_lit by (unfold MAX_RW_COUNT in Hcnt; lia). exact Hover.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma srz_read_file_hull : forall A AL E ms model x8 (fd : word) p off data (cnt : Z) (K : TSet),
  m_halted model = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 63%Z ->
  ms_gpr ms 0 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  ms_gpr ms 2 = Z_to_bv 64 cnt -> (1 <= cnt <= MAX_RW_COUNT)%Z ->
  (bv_unsigned (ms_gpr ms 1) + cnt <= TASK_SIZE)%Z ->
  store_ok segs (ms_mem ms) (ms_gpr ms 1) (Z.to_nat cnt) = true ->
  MInv A AL E model -> bytes_in_hull A (ms_gpr ms 1) (Z.to_nat cnt) ->
  let bs := file_read data off (ms_gpr ms 2) in
  let model' := with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model in
  (forall model2, MInv A AL E model2 -> same_but_materialized model' model2 ->
     srealizes segs (mkCfg (advance_past_svc (apply_effect ms (mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) []))) model2) K) ->
  srealizes segs (mkCfg ms model) K.
Proof.
  intros A AL E ms model x8 fd p off data cnt K Hh Hsvc Hno H0 Hfd32 Hlk Hfs H2 Hcnt Hover Hok HI Hhull. cbv zeta. intros Hc.
  destruct (read_bytes_map_of_store_ok segs (ms_mem ms) (ms_gpr ms 1) (Z.to_nat cnt) Hok ltac:(unfold MAX_RW_COUNT in Hcnt; lia)) as [wv Hw].
  rewrite Z2Nat.id in Hw by lia. rewrite <- H2 in Hw.
  assert (Hu2 : bv_unsigned (ms_gpr ms 2) = cnt) by (rewrite H2; apply u64_lit'; unfold MAX_RW_COUNT in *; lia).
  pose proof (read_file_outcome_si segs ms x8 model fd p off data wv Hno H0 Hfd32 Hlk Hfs
              ltac:(change (ms_writable_byte segs ms) with (wview segs (ms_mem ms)); exact Hw)
              ltac:(rewrite Hu2; lia) ltac:(rewrite Hu2; exact Hover)) as Hchk.
  cbv zeta in Hchk.
  assert (HI1 : MInv A AL E (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word (file_read data off (ms_gpr ms 2))))) model)).
  { apply MInv_with_fds. exact HI. }
  assert (Hacc : accs_in_hull A (syscall_effect_accesses (mkEffect (len_word (file_read data off (ms_gpr ms 2)))
                                                                   (delivered_writes (ms_gpr ms 1) (file_read data off (ms_gpr ms 2))) []))).
  { unfold syscall_effect_accesses. cbn [eff_copyins eff_writes app].
    pose proof (length_file_read data off (ms_gpr ms 2)) as HL. unfold word_to_nat in HL. rewrite Hu2 in HL.
    destruct (file_read data off (ms_gpr ms 2)) as [|b0 bs0] eqn:EB; cbn [delivered_writes write_accesses]; intros a n Hin; [destruct Hin|].
    destruct Hin as [E0|[]]. injection E0 as <- <-.
    eapply bytes_in_hull_shrink; [|exact Hhull]. cbn [length] in HL. lia. }
  eapply (srz_det_hull segs A AL E ms model x8 _ _ K Hh Hsvc Hchk); [rewrite with_fds_halted; exact Hh | exact HI1 | exact Hacc |].
  intros HI2. apply (Hc _ HI2). apply model_after_same.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_S : forall mem a n,
  rdn segs mem a (S n) = match mrb segs mem a with
                         | Some b => match rdn segs mem (a + 1) n with Some rest => Some (b :: rest) | None => None end
                         | None => None end.
Proof. intros. reflexivity. Qed.
Lemma cstr_S : forall mp a f,
  cstr_access_len_aux mp a (S f) = match mp a with
                                   | Some b => if bv_eqb b (Z_to_bv 8 0) then 1%nat else S (cstr_access_len_aux mp (a + 1) f)
                                   | None => 1%nat end.
Proof. intros. reflexivity. Qed.
Lemma cstr_access_len_aux_of_rdn : forall mem p a fuel,
  ~ In (Z_to_bv 8 0) p -> (length p < fuel)%nat ->
  rdn segs mem a (S (length p)) = Some (p ++ [Z_to_bv 8 0]) ->
  cstr_access_len_aux (mrb segs mem) a fuel = S (length p).
Proof.
  intros mem p. induction p as [|c p IH]; intros a fuel Hnz Hf Hr.
  - destruct fuel as [|f]; [lia|]. rewrite rdn_S in Hr. rewrite cstr_S. cbn [length app] in Hr |- *.
    destruct (mrb segs mem a) as [b|]; [|discriminate].
    change (rdn segs mem (a + 1) 0) with (Some (@nil byte)) in Hr. injection Hr as ->. rewrite bv_eqb_refl. reflexivity.
  - destruct fuel as [|f]; [lia|]. cbn [length] in Hf. rewrite rdn_S in Hr. rewrite cstr_S. cbn [length app] in Hr |- *.
    assert (Hc : c <> Z_to_bv 8 0) by (intros E; apply Hnz; left; exact E).
    destruct (mrb segs mem a) as [b|]; [|discriminate].
    destruct (rdn segs mem (a + 1) (S (length p))) as [rest|] eqn:Hr'; [|discriminate].
    injection Hr as Hb Hrest. subst rest. subst b.
    replace (bv_eqb c (Z_to_bv 8 0)) with false by (symmetry; apply bv_eqb_neq; exact Hc).
    rewrite (IH (a + 1) f ltac:(intros X; apply Hnz; right; exact X) ltac:(lia) Hr'). reflexivity.
Qed.

Lemma cstr_access_len_aux_le : forall mp a fuel, (cstr_access_len_aux mp a fuel <= fuel)%nat.
Proof.
  intros mp a fuel. revert a. induction fuel as [|f IH]; intros a; cbn; [lia|].
  destruct (mp a) as [b|]; [|lia]. destruct (bv_eqb b (Z_to_bv 8 0)); [lia|]. specialize (IH (a + 1)). lia.
Qed.

Section OpenatHull.
  Variables (A AL : hull) (E : Z) (ms : machine_state) (model : Model) (x8 : word).
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hsvc : ms_svc_pending ms = Some x8.
  Hypothesis Hno : bv_unsigned x8 = 56%Z.
  Hypothesis H10 : ms_gpr ms 0 = AT_FDCWD.
  Hypothesis Hfl : Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z.
  Hypothesis HI : MInv A AL E model.
  Hypothesis Hrom : ms_rom ms = seg_rom segs.

  Let pathp := ms_gpr ms 1.

  #[using="H10 Hno"] Lemma openat_spec_head' : forall o,
    syscall_spec (sys_input segs ms x8) model o <->
    openat_spec AT_FDCWD32 pathp (ms_gpr ms 2) (sys_input segs ms x8) model o.
  Proof.
    intros o. rewrite (syscall_spec_56 _ model o) by (rewrite in_sysno_si; exact Hno).
    rewrite in_arg0_si, in_arg1_si, in_arg2_si, H10. reflexivity.
  Qed.

  #[using="Hfl"] Lemma open_flags_modeled' : modeled_open_flags (ms_gpr ms 2) = true.
  Proof. exact (modeled_open_flags_rd _ Hfl). Qed.

  #[using="Hrom"] Lemma in_mem_mrb : in_mem (sys_input segs ms x8) = mrb segs (ms_mem ms).
  Proof. rewrite in_mem_si. unfold ms_read_byte, mrb. rewrite Hrom. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition path_at' (p : list byte) : Prop :=
    (length p <= 4095)%nat /\ ~ In (Z_to_bv 8 0) p /\ rdn segs (ms_mem ms) pathp (length p + 1) = Some (p ++ [Z_to_bv 8 0]).

  #[using="Hrom"] Lemma open_reads_len : forall p, path_at' p -> open_reads (sys_input segs ms x8) pathp = [(pathp, S (length p))].
  Proof.
    intros p (H1 & H2 & H3). unfold open_reads. rewrite in_mem_mrb. f_equal. f_equal.
    apply (cstr_access_len_aux_of_rdn (ms_mem ms) p pathp path_max H2); [unfold path_max; lia|].
    rewrite <- Nat.add_1_r. exact H3.
  Qed.

  (* [comment removed for export] *)
  #[using="Hrom HI Hfl H10 Hno Hsvc Hh x8"] Lemma srz_openat_enoent_hull : forall p (K : TSet),
    path_at' p -> bytes_in_hull A pathp (S (length p)) ->
    (p = [] \/ (p <> [] /\ p <> dot_path /\ path_eqb p dotdot_path = false /\ path_has_slash p = false /\
                 fs_lookup (m_fs model) p = None)) ->
    (forall model2, MInv A AL E model2 -> same_but_materialized model model2 ->
       srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret ENOENT))) model2) K) ->
    srealizes segs (mkCfg ms model) K.
  Proof.
    intros p K Hp Hhull Hcase Hc.
    destruct (node_ret_only_copyins_hull segs A AL E ms model x8 [(pathp, S (length p))] (errno_ret ENOENT) model [] Hh Hsvc) as [Hn HI2];
      [| exact Hh | exact HI | | eapply srz_silent1; [exact Hn | apply (Hc _ HI2); apply model_after_same]].
    - intros o. rewrite openat_spec_head', <- (open_reads_len p Hp).
      destruct Hcase as [-> | (Hne & Hnd & Hndd & Hsl & Hfs)].
      + apply (openat_empty_outcome _ _ _ _ model open_flags_modeled'). rewrite in_mem_mrb.
        destruct Hp as (H1 & H2 & H3). apply read_cstr_of_rdn; assumption.
      + apply (openat_absent_outcome _ _ _ _ model open_flags_modeled' eq_refl Hfl p); try assumption.
        rewrite in_mem_mrb. destruct Hp as (H1 & H2 & H3). apply read_cstr_of_rdn; assumption.
    - intros a n Hin. destruct Hin as [E0|[]]. injection E0 as <- <-. exact Hhull.
  Qed.

  (* [comment removed for export] *)
  #[using="Hrom HI Hfl H10 Hno Hsvc Hh x8"] Lemma srz_openat_toolong_hull : forall bs (K : TSet),
    rdn segs (ms_mem ms) pathp 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs -> bytes_in_hull A pathp 4096 ->
    (forall model2, MInv A AL E model2 -> same_but_materialized model model2 ->
       srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret ENAMETOOLONG))) model2) K) ->
    srealizes segs (mkCfg ms model) K.
  Proof.
    intros bs K Hrd Hnz Hhull Hc.
    pose proof (read_cstr_toolong_of_rdn segs (ms_mem ms) pathp bs (rdn_length _ _ _ _ _ Hrd) Hnz Hrd) as Hp.
    destruct (node_ret_only_copyins_hull segs A AL E ms model x8 (open_reads (sys_input segs ms x8) pathp) (errno_ret ENAMETOOLONG) model [] Hh Hsvc) as [Hn HI2];
      [| exact Hh | exact HI | | eapply srz_silent1; [exact Hn | apply (Hc _ HI2); apply model_after_same]].
    - intros o. rewrite openat_spec_head'.
      apply (openat_toolong_outcome _ _ _ _ model open_flags_modeled'). rewrite in_mem_mrb. exact Hp.
    - unfold open_reads.
      pose proof (cstr_access_len_aux_le (in_mem (sys_input segs ms x8)) pathp path_max) as LE.
      remember (cstr_access_len_aux (in_mem (sys_input segs ms x8)) pathp path_max) as N eqn:EN. clear EN.
      intros a n Hin. destruct Hin as [E0|[]]. injection E0 as <- <-.
      eapply bytes_in_hull_shrink; [exact LE|exact Hhull].
  Qed.

  (* [comment removed for export] *)
  #[using="Hrom HI Hfl H10 Hno Hsvc Hh x8"] Lemma srz_openat_open_hull : forall p e (KA KB : TSet),
    path_at' p -> bytes_in_hull A pathp (S (length p)) ->
    fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
    ((p = dot_path /\ e = FdDir) \/ (p <> [] /\ p <> dot_path /\ path_eqb p dotdot_path = false /\ path_has_slash p = false /\
                                      (exists d, fs_lookup (m_fs model) p = Some d) /\ e = FdFile p (Z_to_bv 64 0))) ->
    (forall er model2, In er openat_errnos -> MInv A AL E model2 -> same_but_materialized model model2 ->
       srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret er))) model2) KA) ->
    (forall model2, MInv A AL E model2 ->
       same_but_materialized (with_fds (fd_insert (m_fds model) (alloc_fd (m_fds model)) e) model) model2 ->
       srealizes segs (mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model)))) model2) KB) ->
    srealizes segs (mkCfg ms model) (t_alt2 KA KB).
  Proof.
    intros p e KA KB Hp Hhull Hfree Hcase HA HB.
    set (reads := [(pathp, S (length p))]).
    set (mk := fun fd : word => with_fds (fd_insert (m_fds model) fd e) model).
    pose (effs := fun i : open_I model => match i with
            | inl (exist _ er _) => with_copyins reads (mkEffect (errno_ret er) [] [])
            | inr _ => with_copyins reads (mkEffect (alloc_fd (m_fds model)) [] []) end).
    pose (ms' := fun i : open_I model => match i with inl _ => model | inr _ => mk (alloc_fd (m_fds model)) end).
    assert (Hchk : forall o, syscall_spec_acfg (sys_input segs ms x8) model o <-> open_out reads model mk o).
    { intros o. rewrite acfg_si_nonalloc by (rewrite Hno; reflexivity).
      cbv delta [reads]. rewrite openat_spec_head', <- (open_reads_len p Hp). destruct Hp as (H1 & H2 & H3).
      destruct Hcase as [[-> ->] | (Hne & Hnd & Hndd & Hsl & [d Hfs] & ->)].
      - apply (openat_dot_outcome _ _ _ _ model open_flags_modeled' eq_refl Hfl). rewrite in_mem_mrb. apply read_cstr_of_rdn; assumption.
      - apply (openat_file_outcome _ _ _ _ model open_flags_modeled' eq_refl Hfl p d); try assumption.
        rewrite in_mem_mrb. apply read_cstr_of_rdn; assumption. }
    assert (Hacc : forall i, accs_in_hull A (syscall_effect_accesses (effs i))).
    { intros i. assert (X : accs_in_hull A reads).
      { intros a n Hin. destruct Hin as [E0|[]]. injection E0 as <- <-. exact Hhull. }
      destruct i as [[er Her]|[]]; cbv delta [effs] beta iota; rewrite syscall_effect_accesses_copyins; exact X. }
    destruct (node_family_hull segs A AL E ms model x8 (open_I model) effs ms' (fun _ => []) _ Hh Hsvc Hchk) as [Hnode HI'].
    - intros [[er Her] | []]; [left; exists er; auto | right; auto].
    - intros o [(er & Her & ->) | (Hlk & ->)]; [exists (inl (exist _ er Her)) | exists (inr tt)]; reflexivity.
    - intros [[er Her] | []]; [exact Hh | cbv delta [ms' mk] beta iota; rewrite with_fds_halted; exact Hh].
    - intros [[er Her] | []]; [exact HI | cbv delta [ms' mk] beta iota; apply MInv_with_fds; exact HI].
    - exact Hacc.
    - apply (srz_alt2 segs (mkCfg ms model) {er : Z | In er openat_errnos} unit _ KA KB (exist _ ENOMEM ENOMEM_in_openat_errnos) tt Hnode).
      + intros [er Her]. cbv delta [effs ms'] beta iota. rewrite apply_effect_copyins_no_write.
        apply (HA er _ Her (HI' (inl (exist _ er Her)))). apply model_after_same.
      + intros []. cbv delta [effs ms' mk] beta iota. rewrite apply_effect_copyins_no_write.
        apply (HB _ (HI' (inr tt))). apply model_after_same.
  Qed.
End OpenatHull.

End WithSegs.
