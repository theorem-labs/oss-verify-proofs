(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import CheckLite.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk AgentLib AgentNodes AsanCeil RefNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma check_syscall_29 : forall ms x8 eff m,
  bv_unsigned x8 = 29%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_ioctl (fd32 (ms_gpr ms 0)) (cmd32 (ms_gpr ms 1)) eff m.
Proof.
  intros ms x8 eff m Hno.
  unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.

Lemma sysno_lit : forall regs (n : Z), (0 <= n < 2 ^ 64)%Z ->
  getr regs 17 = Z_to_bv 64 n -> bv_unsigned (getr regs 17) = n.
Proof. intros regs n Hn H. rewrite H. apply u64_lit. exact Hn. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_close : forall regs (pc : word) mem model w fd e K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 57 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem (seg_rom segs))
                       (with_fds (fd_remove (m_fds model) fd) model)) K ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd e K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_ret_only_silent; [exact Hh | reflexivity | | | | rewrite adv_set_epend; exact Hc].
  - intros eff. rewrite (check_syscall_57 segs _ _ eff model) by (apply (sysno_lit regs 57); [lia | exact H17]).
    rewrite ms_gpr_epend0, Hfd, (fd32_id fd Hfd32). unfold check_close. rewrite Hlk. reflexivity.
  - rewrite with_fds_halted'. exact Hh.
  - rewrite with_fds_lazy. exact Hlazy.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_ioctl_winsz : forall regs (pc : word) mem model w fd c K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 29 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdChannel c) ->
  getr regs 11 = Z_to_bv 64 0x5413 ->
  realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem (seg_rom segs))
                       model) K ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd c K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk H11 Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_ret_only_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
  intros eff. rewrite (check_syscall_29 _ _ eff model) by (apply (sysno_lit regs 29); [lia | exact H17]).
  rewrite ms_gpr_epend0, ms_gpr_epend1, Hfd, (fd32_id fd Hfd32), H11. unfold check_ioctl. rewrite Hlk.
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_read_dir : forall regs (pc : word) mem model w fd K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
  realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hok Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_ret_only_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
  intros eff. rewrite (check_syscall_63 segs _ _ eff model) by (apply (sysno_lit regs 63); [lia | exact H17]).
  rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32). unfold check_read. rewrite Hlk, Hok.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rz_read_dir_mapped : forall regs (pc : word) mem model w fd (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  getr regs 12 = Z_to_bv 64 cnt ->
  (1 <= cnt)%Z -> (cnt <= 2 ^ 24)%Z ->
  (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
  store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
  realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd cnt K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk H12 Hc1 H64 Hover _ Hc.
  apply (rz_read_dir regs pc mem model w fd K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk); [|exact Hc].
  apply access_okb_intro. rewrite H12, u64_lit by lia. exact Hover.
Qed.

(* [comment removed for export] *)
Lemma rz_read_file : forall regs (pc : word) mem model w fd p off data (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  getr regs 12 = Z_to_bv 64 cnt ->
  (1 <= cnt)%Z -> (cnt <= rw_bytes_max)%Z ->
  (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
  store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
  let bs := file_read data off (getr regs 12) in
  realizes segs (mkCfg (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4)
                              (wbytes mem (getr regs 11) bs) (seg_rom segs))
                       (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model)) K ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd p off data cnt K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax Hover Hok bs Hc.
  assert (Hrw : (rw_bytes_max < 2 ^ 64)%Z) by (unfold rw_bytes_max; lia).
  assert (Hno : bv_unsigned (getr regs 17) = 63%Z) by (apply (sysno_lit regs 63); [lia | exact H17]).
  assert (Hu2 : bv_unsigned (getr regs 12) = cnt) by (rewrite H12; apply u64_lit; lia).
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  destruct (read_bytes_map_of_store_ok segs mem (getr regs 11) (Z.to_nat cnt) Hok ltac:(lia)) as [wv Hw].
  rewrite Z2Nat.id in Hw by lia. rewrite <- H12 in Hw.
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (HL : (bv_unsigned (len_word bs) <= bv_unsigned (getr regs 12))%Z).
  { unfold bs, len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
    pose proof (u64_range (getr regs 12)) as Hcw.
    rewrite length_file_read, Nat2Z.inj_min. unfold word_to_nat.
    rewrite Z.mod_small; lia. }
  assert (Haok : access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true).
  { apply access_okb_intro. rewrite Hu2. exact Hover. }
  assert (Hchk : forall eff m' evs,
    check_syscall (sys_input segs ms (getr regs 17)) eff model = CheckOk m' evs <->
    (eff = mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) []
     /\ m' = with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model
     /\ evs = [])).
  { intros eff m' evs.
    rewrite (check_syscall_63 segs ms _ eff model Hno). unfold check_read.
    unfold ms. rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32), Hlk.
    cbv beta iota.
    rewrite Haok. cbn [negb]. cbv beta iota.
    rewrite (rw_count_clamp_of_rw _ ltac:(rewrite Hu2; exact Hmax)), Z_to_bv_bv_unsigned.
    rewrite Hfs. cbv beta iota zeta.
    rewrite in_wmem_si, ms_writable_byte_epend. fold bs.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw). cbv beta iota.
    destruct bs as [|b bsr] eqn:Ebs.
    - (* [comment removed for export] *)
      cbv beta iota.
      rewrite check_ret_only_ok_iff. cbn [delivered_writes length].
      tauto.
    - destruct eff as [ret ws zs us cs copyins]. split.
      + intro H.
        destruct ws as [|[a bs'] [|? ?]]; try discriminate.
        destruct zs as [|? ?]; [|discriminate].
        destruct us as [|? ?]; [|discriminate].
        destruct cs as [|? ?]; [|discriminate].
        destruct copyins as [|? ?]; [|discriminate].
        destruct (bv_eqb a (getr regs 11) && listN_eqb bs' (b :: bsr)
                  && bv_eqb ret (len_word (b :: bsr)))
          eqn:Hb; try rewrite Hb in H; [|discriminate].
        apply andb_true_iff in Hb as [Hb Hr].
        apply andb_true_iff in Hb as [Ha Hbs].
        apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hr. apply listN_eqb_eq in Hbs.
        inversion H; subst. cbn [delivered_writes].
        repeat split; congruence.
      + intros (Heff & -> & ->). cbn [delivered_writes] in Heff.
        inversion Heff; subst.
        rewrite bv_eqb_refl.
        rewrite (proj2 (listN_eqb_eq _ _) eq_refl).
        rewrite bv_eqb_refl. cbn [andb]. reflexivity. }
  eapply (rz_det segs ms model _ (mkEffect (len_word bs) (delivered_writes (getr regs 11) bs) [])
            (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model));
    [exact Hh | reflexivity | exact Hchk | | rewrite with_fds_halted'; exact Hh | rewrite with_fds_lazy; exact Hlazy | ].
  - intros eff Hs.
    rewrite (check_syscall_63 segs ms _ eff model Hno) in Hs. unfold check_read in Hs.
    unfold ms in Hs. rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32), Hlk in Hs.
    cbv beta iota in Hs.
    rewrite Haok in Hs. cbn [negb] in Hs. cbv beta iota in Hs.
    rewrite (rw_count_clamp_of_rw _ ltac:(rewrite Hu2; exact Hmax)), Z_to_bv_bv_unsigned in Hs.
    rewrite Hfs in Hs. cbv beta iota zeta in Hs.
    rewrite in_wmem_si, ms_writable_byte_epend in Hs. fold bs in Hs.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw) in Hs. cbv beta iota in Hs.
    revert Hs. destruct bs as [|b0 bsr]; intro Hs.
    + exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
    + destruct eff as [ret ws zs us cs copyins].
      destruct ws as [|[a bs'] [|? ?]]; try discriminate.
      destruct zs as [|? ?]; try discriminate.
      destruct us as [|? ?]; try discriminate.
      destruct cs as [|? ?]; try discriminate.
      destruct copyins as [|? ?]; try discriminate.
      destruct (bv_eqb a (getr regs 11) && listN_eqb bs' (b0 :: bsr) && bv_eqb ret (len_word (b0 :: bsr)));
        discriminate.
  - destruct bs as [|b bsr] eqn:Ebs; cbn [delivered_writes].
    + unfold ms. rewrite adv_ret_epend. cbn [wbytes] in Hc. exact Hc.
    + unfold ms. rewrite adv_write1_epend. exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Openat.
  Variables (regs : bvmap 5 word) (pc : word) (mem : word -> option byte) (model : Model).
  Variable w : bv 32.
  Hypothesis HF : fetch_word segs pc = Some w.
  Hypothesis HE : is_ecall w = true.
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].
  Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
  Hypothesis H10 : getr regs 10 = AT_FDCWD.
  (* [comment removed for export] *)
  Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.

  Let ms := epend regs pc mem (seg_rom segs) (getr regs 17).
  Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom segs).
  Let fds := m_fds model.

  Lemma Hno56 : bv_unsigned (getr regs 17) = 56%Z.
  Proof. apply (sysno_lit regs 56); [lia | exact H17]. Qed.

  Lemma open_in_mem : in_mem (sys_input segs ms (getr regs 17)) = mrb segs mem.
  Proof. cbv delta [ms]. rewrite in_mem_si, ms_read_byte_epend. reflexivity. Qed.

  Lemma open_flags_modeled : modeled_open_flags (getr regs 12) = true.
  Proof. exact (modeled_open_flags_rd _ Hfl). Qed.

  (* [comment removed for export] *)
  Lemma openat_check_head : forall eff,
    check_syscall (sys_input segs ms (getr regs 17)) eff model
    = Prelude.check_copyins_after (open_copyins ms) eff
        (Open.check_openat_body (sys_input segs ms (getr regs 17)) AT_FDCWD32 (getr regs 11) (getr regs 12)
           (clear_copyins eff) model).
  Proof.
    intros eff. rewrite (check_syscall_56 segs ms _ eff model Hno56). unfold check_openat.
    cbv delta [ms]. rewrite ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, H10, open_flags_modeled.
    norm_fd32. cbn [negb]. cbv beta iota zeta. unfold open_copyins.
    rewrite in_mem_si, ms_gpr_epend1. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_toolong : forall bs K,
    rdn segs mem (getr regs 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
    realizes segs (mkCfg (post (errno_ret ENAMETOOLONG)) model) K ->
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros bs K Hrd Hnz Hc. cbv delta [post] in *.
    pose proof (read_cstr_toolong_of_rdn segs mem (getr regs 11) bs (rdn_length _ _ _ _ _ Hrd) Hnz Hrd) as Hp.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite openat_check_head. unfold Open.check_openat_body. rewrite open_in_mem, Hp.
    apply check_copyins_after_ret_only.
  Qed.

  (* [comment removed for export] *)
  Definition path_at (p : list byte) : Prop :=
    (length p <= 4095)%nat /\ ~ In (Z_to_bv 8 0) p
    /\ rdn segs mem (getr regs 11) (length p + 1) = Some (p ++ [Z_to_bv 8 0]).

  Lemma path_at_cstr : forall p, path_at p -> read_cstr (mrb segs mem) (getr regs 11) = CstrOk p.
  Proof. intros p (H1 & H2 & H3). apply read_cstr_of_rdn; assumption. Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_empty : forall K,
    path_at [] ->
    realizes segs (mkCfg (post (errno_ret ENOENT)) model) K ->
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros K Hp Hc. cbv delta [post] in *.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite openat_check_head. unfold Open.check_openat_body.
    rewrite open_in_mem, (path_at_cstr [] Hp). cbn [path_eqb]. cbv beta iota.
    apply check_copyins_after_ret_only.
  Qed.

  (* [comment removed for export] *)
  Lemma openat_check_resolved : forall p eff,
    path_at p -> path_eqb p [] = false -> path_has_slash p = false ->
    check_syscall (sys_input segs ms (getr regs 17)) eff model
    = Prelude.check_copyins_after (open_copyins ms) eff (Open.check_openat_read p (clear_copyins eff) model).
  Proof.
    intros p eff Hp Hne Hsl. rewrite openat_check_head. unfold Open.check_openat_body.
    rewrite open_in_mem, (path_at_cstr p Hp), Hne. cbv beta iota.
    rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
    unfold Open.check_openat_resolved. rewrite Hsl. cbv beta iota zeta. rewrite Hfl, Z.eqb_refl. reflexivity.
  Qed.

  Lemma path_eqb_nil_neq : forall p, p <> [] -> path_eqb p [] = false.
  Proof. intros [|b p] H; [congruence | reflexivity]. Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_absent : forall p K,
    path_at p -> p <> [] -> p <> dot_path -> p <> dotdot_path -> path_has_slash p = false ->
    fs_lookup (m_fs model) p = None ->
    realizes segs (mkCfg (post (errno_ret ENOENT)) model) K ->
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
  Proof.
    intros p K Hp Hne Hnd Hndd Hsl Hfs Hc. cbv delta [post] in *.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply rz_ret_only_copyins_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
    intros eff. fold ms. rewrite (openat_check_resolved p eff Hp (path_eqb_nil_neq p Hne) Hsl).
    unfold Open.check_openat_read, path_is_dirref.
    rewrite (path_eqb_neq p dot_path Hnd), (path_eqb_neq p dotdot_path Hndd). cbn [orb]. rewrite Hfs.
    apply check_copyins_after_ret_only.
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

  Lemma open_result_copyins_after : forall eff mk,
    Prelude.check_copyins_after (open_copyins ms) eff (check_open_result (clear_copyins eff) model mk)
    = check_open_result_copyins (open_copyins ms) eff model mk.
  Proof.
    intros eff mk. unfold Prelude.check_copyins_after, check_open_result_copyins.
    destruct (check_open_result (clear_copyins eff) model mk) eqn:Hresult; [reflexivity | reflexivity |].
    exfalso. now apply check_open_result_never_unmodeled in Hresult.
  Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_dot : forall KA KB,
    path_at dot_path ->
    (forall e, In e openat_errnos -> realizes segs (mkCfg (post (errno_ret e)) model) KA) ->
    realizes segs (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) KB ->
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros KA KB Hp HA HB. cbv delta [post] in *.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply (rz_open segs _ model _ (open_copyins ms) (fun fd => with_fds (fd_insert fds fd FdDir) model));
      [exact Hh | exact Hlazy | reflexivity | | | | exact Hfree | |].
    - intros eff. fold ms. rewrite (openat_check_resolved dot_path eff Hp eq_refl eq_refl).
      unfold Open.check_openat_read. cbn [path_is_dirref path_eqb dot_path]. cbv beta iota.
      apply open_result_copyins_after.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_lazy. exact Hlazy.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.

  (* [comment removed for export] *)
  Lemma rz_openat_file : forall p d KA KB,
    path_at p -> p <> [] -> p <> dot_path -> p <> dotdot_path -> path_has_slash p = false ->
    fs_lookup (m_fs model) p = Some d ->
    (forall e, In e openat_errnos -> realizes segs (mkCfg (post (errno_ret e)) model) KA) ->
    realizes segs (mkCfg (post (alloc_fd fds))
                         (with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) model)) KB ->
    realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
  Proof.
    intros p d KA KB Hp Hne Hnd Hndd Hsl Hfs HA HB. cbv delta [post] in *.
    eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
    eapply (rz_open segs _ model _ (open_copyins ms) (fun fd => with_fds (fd_insert fds fd (FdFile p (Z_to_bv 64 0))) model));
      [exact Hh | exact Hlazy | reflexivity | | | | exact Hfree | |].
    - intros eff. fold ms. rewrite (openat_check_resolved p eff Hp (path_eqb_nil_neq p Hne) Hsl).
      unfold Open.check_openat_read, path_is_dirref.
      rewrite (path_eqb_neq p dot_path Hnd), (path_eqb_neq p dotdot_path Hndd). cbn [orb]. rewrite Hfs.
      apply open_result_copyins_after.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_halted'. exact Hh.
    - intros fd. cbv beta delta [fds]. rewrite with_fds_lazy. exact Hlazy.
    - intros e He. rewrite adv_set_epend. apply HA. exact He.
    - rewrite adv_set_epend. exact HB.
  Qed.
End Openat.

(* [comment removed for export] *)
Lemma alloc_fd_init : forall e0 e1 e2,
  alloc_fd [(Z_to_bv 64 0, e0); (Z_to_bv 64 1, e1); (Z_to_bv 64 2, e2)] = Z_to_bv 64 3.
Proof. intros. reflexivity. Qed.

Lemma fd_lookup_init_3 : forall e0 e1 e2,
  fd_lookup [(Z_to_bv 64 0, e0); (Z_to_bv 64 1, e1); (Z_to_bv 64 2, e2)] (Z_to_bv 64 3) = None.
Proof. intros. reflexivity. Qed.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegsMM.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma rz_mmap_anon : forall regs (pc : word) mem model w (len : Z) KA KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := page_round_up_Z len in
  (exists a, grant_ok (getr regs 10) model a n = true) ->
  (forall e, In e mmap_errnos ->
     realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model) KA) ->
  (forall a, grant_ok (getr regs 10) model a n = true ->
     realizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4)
                                (zfill a (Z_to_bv 64 n) mem) (seg_rom segs))
                         (mmap_model a (Z_to_bv 64 n) model)) KB) ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
Proof.
  intros regs pc mem model w len KA KB HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 n Hex HA HB.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. lia. }
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 n).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (Hargs : mmap_args_ok ms).
  { unfold mmap_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  assert (H0 : ms_gpr ms 0 = getr regs 10) by (unfold ms; rewrite ms_gpr_epend0; reflexivity).
  eapply (rz_mmap segs ms model (getr regs 17) KA KB Hh Hlazy eq_refl
            ltac:(rewrite H17; apply u64_lit; lia) Hargs).
  - intros e He. unfold ms. rewrite adv_set_epend. apply HA. exact He.
  - intros a Ha. rewrite Hpr. rewrite H0, Hu1 in Ha. unfold ms, epend. rewrite adv_mmap_grant. apply HB. exact Ha.
  - rewrite H0, Hu1. exact Hex.
Qed.

(* [comment removed for export] *)
Lemma rz_mmap_anon_nogrant : forall regs (pc : word) mem model w (len : Z) KA,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  (forall a, grant_ok (getr regs 10) model a (page_round_up_Z len) = false) ->
  (forall e, In e mmap_errnos ->
     realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model) KA) ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) KA.
Proof.
  intros regs pc mem model w len KA HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 Hng HA.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. lia. }
  assert (Hargs : mmap_args_ok ms).
  { unfold mmap_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  set (I := {e : Z | In e mmap_errnos}).
  apply (rz_conseq segs _ (t_alt (fun _ : I => KA)));
    [| intros tr; split; [intros [_ Ht]; exact Ht
                         | intros Ht; exists (exist _ ENOMEM ENOMEM_in_mmap_errnos); exact Ht]].
  apply (rz_cases segs _ I (fun i => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret (proj1_sig i)))) model)
           (fun _ => KA) (exist _ ENOMEM ENOMEM_in_mmap_errnos)).
  - split.
    + intros [e He]. cbn [proj1_sig].
      rewrite <- (apply_effect_no_write ms (errno_ret e)).
      apply (sstep_syscall segs ms model (getr regs 17) (mkEffect (errno_ret e) [] []) model model []);
        [exact Hh | reflexivity | apply mmap_fail_ok; assumption | exact Hh
        | apply materialize_model_accesses_no_lazy; exact Hlazy].
    + intros e st Hss.
      destruct (sstep_mmap_inv segs ms model (getr regs 17) e st Hh Hlazy eq_refl Hno Hargs Hss)
        as [-> [(er & Her & ->) | (a & Ha & ->)]].
      * exists (exist _ er Her). split; reflexivity.
      * exfalso. unfold ms in Ha. rewrite ms_gpr_epend0 in Ha. fold ms in Ha. rewrite Hu1, Hng in Ha. discriminate.
  - intros [e He]. cbn [proj1_sig]. unfold ms. rewrite adv_set_epend. apply HA. exact He.
Qed.

(* [comment removed for export] *)
Lemma rz_munmap : forall regs (pc : word) mem model w (a : word) (len : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 215 ->
  getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned a + page_round_up_Z len <= TASK_SIZE)%Z ->  (* [comment removed for export] *)
  map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
  realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
                             (unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) (seg_rom segs))
                      (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)) K ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w a len K HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw Hhas Hc.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE, two_pow_64 in *. lia. }
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hargs : munmap_args_ok ms model).
  { unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; try assumption.
    intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
  eapply (ShapeAlg.rz_munmap segs ms model (getr regs 17));
    [exact Hh | exact Hlazy | reflexivity | rewrite H17; apply u64_lit; lia | exact Hargs |].
  unfold munmap_eff. rewrite H0, Hpr. unfold ms. rewrite adv_unmaps1_epend. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma rz_brk_query : forall regs (pc : word) mem model w K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  getr regs 10 = Z_to_bv 64 0 ->
  realizes segs (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem (seg_rom segs))
                       model) K ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w K HF HE Hh Hlazy H17 H10 Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps model)).
  { intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
    unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
  assert (Hq : brk_resolution_ok model (ms_gpr ms 0) (vm_brk (m_vmmaps model))) by (apply Hcases; reflexivity).
  apply (rz_conseq segs _ (t_alt (fun _ : {r : word | brk_resolution_ok model (ms_gpr ms 0) r} => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hq); exact Ht]].
  eapply rz_cases; [exact (exist _ _ Hq) | eapply node_brk; [exact Hh | exact Hlazy | reflexivity | exact Hno] |].
  intros [r Hr]. cbn [proj1_sig].
  pose proof (proj1 (Hcases r) Hr) as Er. subst r.
  rewrite H0, brk_zeros_query, brk_unmaps_keep.
  rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
  unfold ms. rewrite adv_ret_epend. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma rz_brk_grow : forall regs (pc : word) mem model w (d : Z) KA KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
  getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
  Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->
  (* [comment removed for export] *)
  realizes segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem (seg_rom segs)) model) KA ->
  (* [comment removed for export] *)
  realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
                             (zfill b (Z_to_bv 64 d) mem) (seg_rom segs))
                       (with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                                      (vm_noaccess h) (vm_start_brk h)
                                      (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) KB ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
Proof.
  intros regs pc mem model w d KA KB HF HE Hh Hlazy H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HA HB.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> (r = b \/ (r = req /\ Mmap.brk_grow_ok model req req = true))).
  { intros r. rewrite H0. apply brk_r_ok_grow_cases; fold h; fold b; rewrite ?Hureq; lia. }
  assert (Hkeep : brk_resolution_ok model (ms_gpr ms 0) b) by (apply Hcases; left; reflexivity).
  assert (Hgrow : brk_resolution_ok model (ms_gpr ms 0) req) by (apply Hcases; right; split; [reflexivity | exact Hadm]).
  assert (Hneq : req <> b).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. unfold b in E. lia. }
  apply (rz_conseq segs _ (t_alt (fun i : {r : word | brk_resolution_ok model (ms_gpr ms 0) r} =>
                               if bv_eqb (proj1_sig i) b then KA else KB))).
  2:{ intros tr. unfold t_alt2, t_alt. split.
      - intros [[r Hr] Ht]. cbn [proj1_sig] in Ht. destruct (bv_eqb r b); tauto.
      - intros [Ht | Ht].
        + exists (exist _ b Hkeep). cbn [proj1_sig]. rewrite bv_eqb_refl. exact Ht.
        + exists (exist _ req Hgrow). cbn [proj1_sig]. rewrite (bv_eqb_neq _ _ Hneq). exact Ht. }
  eapply rz_cases; [exact (exist _ b Hkeep) | eapply node_brk; [exact Hh | exact Hlazy | reflexivity | exact Hno] |].
  intros [r Hr]. cbn [proj1_sig]. fold h.
  destruct (proj1 (Hcases r) Hr) as [-> | [-> Hg]].
  - (* [comment removed for export] *)
    rewrite bv_eqb_refl. fold b. rewrite brk_zeros_keep, brk_unmaps_keep.
    unfold b, h. rewrite brk_model_keep.
    unfold ms. rewrite adv_ret_epend. exact HA.
  - (* [comment removed for export] *)
    rewrite (bv_eqb_neq _ _ Hneq).
    assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
    assert (Hreq0 : req <> Z_to_bv 64 0).
    { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
    rewrite H0. fold b. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
    unfold brk_page_range.
    rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
    rewrite (page_round_up_Z_aligned (bv_unsigned req))
      by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
    rewrite (proj2 (Z.ltb_lt _ _) Hlt).
    replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
    rewrite Hureq. replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
    unfold req, b, h. rewrite (brk_model_grow_eq model d) by assumption.
    unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

(* [comment removed for export] *)
Lemma rz_brk_grow_blocked : forall regs (pc : word) mem model w (req : word) KA,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 214 ->
  let h := m_vmmaps model in
  let b := vm_brk h in
  getr regs 10 = req ->
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned b <= bv_unsigned req)%Z ->
  Mmap.brk_grow_ok model req req = false ->
  realizes segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem (seg_rom segs)) model) KA ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) KA.
Proof.
  intros regs pc mem model w req KA HF HE Hh Hlazy H17 h b H10 Hpos Hs Hb Hblk HA.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = b).
  { intros r. rewrite H0, (brk_r_ok_grow_cases model req r Hpos Hs Hb). fold h. fold b. split.
    - intros [-> | [-> Hg]]; [reflexivity | rewrite Hblk in Hg; discriminate].
    - intros ->. left. reflexivity. }
  assert (Hkeep : brk_resolution_ok model (ms_gpr ms 0) b) by (apply Hcases; reflexivity).
  apply (rz_conseq segs _ (t_alt (fun _ : {r : word | brk_resolution_ok model (ms_gpr ms 0) r} => KA)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hkeep); exact Ht]].
  eapply rz_cases; [exact (exist _ b Hkeep) | eapply node_brk; [exact Hh | exact Hlazy | reflexivity | exact Hno] |].
  intros [r Hr]. cbn [proj1_sig]. fold h.
  pose proof (proj1 (Hcases r) Hr) as Er. subst r. fold b.
  rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep.
  unfold ms. rewrite adv_ret_epend. exact HA.
Qed.

(* [comment removed for export] *)
Lemma grant_ok_grant_ok_na_pin : forall hint m a n, grant_ok hint m a n = true -> grant_ok_na_pin m a n = true.
Proof. exact grant_ok_na_pin_of_grant_ok. Qed.

(* [comment removed for export] *)
Lemma rz_mmap_noaccess : forall regs (pc : word) mem model w (len : Z) KA KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len < 2 ^ 64)%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 34 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := page_round_up_Z len in
  (exists a, grant_ok_na_pin model a n = true) ->
  (forall e, In e mmap_errnos ->
     realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model) KA) ->
  (forall a, grant_ok_na_pin model a n = true ->
     realizes segs (mkCfg (mkst (regupd regs 10 a) (v_addi pc 4)
                                (unfill a (Z_to_bv 64 n) mem) (seg_rom segs))
                         (noaccess_model a (Z_to_bv 64 n) model)) KB) ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
Proof.
  intros regs pc mem model w len KA KB HF HE Hh Hlazy H17 H11 Hlen H12 H13 H14 H15 n [a0 Ha0] HA HB.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. lia. }
  assert (Hargs : mmap_noaccess_args_ok ms).
  { unfold mmap_noaccess_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  assert (Hn0 : (0 <= n)%Z) by (unfold n; apply page_round_up_Z_nonneg; lia).
  pose proof (fun eff => mmap_noaccess_check segs ms (getr regs 17) model eff Hno Hargs) as Hchk.
  rewrite Hu1 in Hchk. cbv zeta in Hchk. fold n in Hchk.
  pose (IA := {e : Z | In e mmap_errnos}).
  pose (IB := {a : word | grant_ok_na_pin model a n = true}).
  pose (effs := fun i : IA + IB => match i with
                           | inl (exist _ e _) => mkEffectU (errno_ret e) [] [] [] [] []
                           | inr (exist _ a _) => mkEffectU a [] [] [(a, Z_to_bv 64 n)] [] [] end).
  pose (ms' := fun i : IA + IB => match i with
                          | inl _ => model
                          | inr (exist _ a _) => noaccess_model a (Z_to_bv 64 n) model end).
  eapply (rz_alt2 segs (mkCfg ms model) IA IB
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KA KB
            (exist _ ENOMEM ENOMEM_in_mmap_errnos) (exist _ a0 Ha0)).
  - apply (node_chk segs ms model (getr regs 17) (IA + IB) effs ms' Hh eq_refl).
    + intros [[e He] | [a Ha]]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ e He). reflexivity.
      * rewrite (grant_na_pin_not_errno model a n Hn0 Ha), Ha.
        rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros eff m' evs Hc. rewrite Hchk in Hc.
      destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Her.
      * destruct us; [|discriminate]. injection Hc as <- <-.
        apply errno_ret_in_true in Her. destruct Her as (e & He & ->).
        exists (inl (exist _ e He)). auto.
      * destruct (grant_ok_na_pin model r n) eqn:Hg; [|discriminate].
        destruct (listNN_eqb us [(r, Z_to_bv 64 n)]) eqn:Hus; [|discriminate].
        apply listNN_eqb_eq in Hus. subst us. injection Hc as <- <-.
        exists (inr (exist _ r Hg)). auto.
    + intros eff Hc. rewrite Hchk in Hc.
      destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
      destruct (grant_ok_na_pin model r n && listNN_eqb us [(r, Z_to_bv 64 n)]); discriminate.
    + intros [[e He] | [a Ha]]; cbn [ms']; [exact Hh | unfold noaccess_model; rewrite with_vmmaps_halted; exact Hh].
    + intros [[e He] | [a Ha]]; cbn [ms']; [exact Hlazy | unfold noaccess_model; rewrite with_vmmaps_lazy'; exact Hlazy].
  - intros [e He]. cbn [effs ms']. unfold ms. rewrite adv_ret_epend. apply HA. exact He.
  - intros [a Ha]. cbn [effs ms']. unfold ms. rewrite adv_unmaps1_epend. apply HB. exact Ha.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_mprotect : forall regs (pc : word) mem model w (addr : word) (len : Z) KA KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 226 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  getr regs 12 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = true ->
  (forall e, In e mprotect_errnos ->
     realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model) KA) ->
  realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) (zfill addr n mem) (seg_rom segs))
                       (mprotect_model addr n model)) KB ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 KA KB).
Proof.
  intros regs pc mem model w addr len KA KB HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw H12 n Hna Hma Hbud HA HB.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 226%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mprotect_check segs ms (getr regs 17) model eff addr len Hno
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hnw
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12) Hna Hma) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  pose (IA := {e : Z | In e mprotect_errnos}).
  pose (effs := fun i : IA + unit => match i with
                           | inl (exist _ e _) => mkEffectU (errno_ret e) [] [] [] [] []
                           | inr _ => mkEffectU (Z_to_bv 64 0) [] [(addr, n)] [] [] [] end).
  pose (ms' := fun i : IA + unit => match i with inl _ => model | inr _ => mprotect_model addr n model end).
  assert (Hz : errno_ret_in mprotect_errnos (Z_to_bv 64 0) = false) by (vm_compute; reflexivity).
  eapply (rz_alt2 segs (mkCfg ms model) IA unit
            (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)) KA KB
            (exist _ ENOMEM ENOMEM_in_mprotect_errnos) tt).
  - apply (node_chk segs ms model (getr regs 17) (IA + unit) effs ms' Hh eq_refl).
    + intros [[e He] | []]; cbn [effs ms']; rewrite Hchk.
      * rewrite (errno_ret_in_intro _ e He). reflexivity.
      * rewrite Hz, Hbud. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros eff m' evs Hc. rewrite Hchk in Hc.
      destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
      destruct (errno_ret_in mprotect_errnos r) eqn:Her.
      * destruct zs; [|discriminate]. injection Hc as <- <-.
        apply errno_ret_in_true in Her. destruct Her as (e & He & ->).
        exists (inl (exist _ e He)). auto.
      * rewrite Hbud in Hc. cbn [andb] in Hc.
        destruct (w_is0 r) eqn:Hr0; [|discriminate].
        destruct (listNN_eqb zs [(addr, n)]) eqn:Hzs; [|discriminate].
        apply listNN_eqb_eq in Hzs. subst zs. injection Hc as <- <-.
        unfold w_is0 in Hr0. apply bv_eqb_eq in Hr0. subst r.
        exists (inr tt). auto.
    + intros eff Hc. rewrite Hchk in Hc.
      destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
      destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate|].
      destruct (mprotect_budget_ok model addr n && w_is0 r && listNN_eqb zs [(addr, n)]); discriminate.
    + intros [[e He] | []]; cbn [ms']; [exact Hh | unfold mprotect_model; rewrite with_vmmaps_halted; exact Hh].
    + intros [[e He] | []]; cbn [ms']; [exact Hlazy | unfold mprotect_model; rewrite with_vmmaps_lazy'; exact Hlazy].
  - intros [e He]. cbn [effs ms']. unfold ms. rewrite adv_ret_epend. apply HA. exact He.
  - intros []. cbn [effs ms']. unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

(* [comment removed for export] *)
Lemma rz_mprotect_blocked : forall regs (pc : word) mem model w (addr : word) (len : Z) KA,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 226 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  getr regs 12 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  mprotect_budget_ok model addr n = false ->
  (forall e, In e mprotect_errnos ->
     realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model) KA) ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) KA.
Proof.
  intros regs pc mem model w addr len KA HF HE Hh Hlazy H17 H10 Hal H11 Hlen Hnw H12 n Hna Hma Hbud HA.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 226%Z) by (rewrite H17; apply u64_lit; lia).
  pose proof (fun eff => mprotect_check segs ms (getr regs 17) model eff addr len Hno
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Hnw
                ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12) Hna Hma) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  pose (IA := {e : Z | In e mprotect_errnos}).
  apply (rz_conseq segs _ (t_alt (fun _ : IA => KA)));
    [| intros tr; split; [intros [_ Ht]; exact Ht
                         | intros Ht; exists (exist _ ENOMEM ENOMEM_in_mprotect_errnos); exact Ht]].
  apply (rz_cases segs _ IA (fun i => mkCfg (advance_past_svc (apply_effect ms (mkEffectU (errno_ret (proj1_sig i)) [] [] [] [] []))) model)
           (fun _ => KA) (exist _ ENOMEM ENOMEM_in_mprotect_errnos)).
  - apply (node_chk segs ms model (getr regs 17) IA (fun i => mkEffectU (errno_ret (proj1_sig i)) [] [] [] [] []) (fun _ => model) Hh eq_refl).
    + intros [e He]. cbn [proj1_sig]. rewrite Hchk. rewrite (errno_ret_in_intro _ e He). reflexivity.
    + intros eff m' evs Hc. rewrite Hchk in Hc.
      destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
      destruct (errno_ret_in mprotect_errnos r) eqn:Her.
      * destruct zs; [|discriminate]. injection Hc as <- <-.
        apply errno_ret_in_true in Her. destruct Her as (e & He & ->).
        exists (exist _ e He). auto.
      * rewrite Hbud in Hc. discriminate.
    + intros eff Hc. rewrite Hchk in Hc.
      destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|destruct zs; discriminate]. destruct ci; [|destruct zs; discriminate].
      destruct (errno_ret_in mprotect_errnos r); [destruct zs; discriminate|].
      rewrite Hbud in Hc. discriminate.
    + intros _. exact Hh.
    + intros _. exact Hlazy.
  - intros [e He]. cbn [proj1_sig]. unfold ms. rewrite adv_ret_epend. apply HA. exact He.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mmap_fixed_check : forall ms x8 model eff (addr : word) (len : Z),
  bv_unsigned x8 = 222%Z -> mmap_fixed_args_ok ms ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] [] us [] [] =>
        if errno_ret_in mmap_errnos r
        then match us with
             | [] => CheckOk model []
             | _ => if listNN_eqb us [(addr, n)] then CheckOk (fixed_destroyed_model addr n model) [] else CheckReject
             end
        else if bv_eqb r addr && listNN_eqb us [(addr, n)]
             then CheckOk (fixed_noaccess_model addr n model) []
             else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff addr len Hno (H1 & H2 & H3 & H4 & H5) H0 Hal Hpos H11 Hlen Htop n Hrf Hmc.
  pose proof (page_round_up_Z_ge_all len) as Hge. pose proof (u64_range addr) as Har.
  assert (Hlen' : (len < 2 ^ 64)%Z) by (alloc_top_bounds; unfold two_pow_64 in *; lia).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H11; apply u64_lit; lia).
  rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
  assert (E1 : w_is0 (ms_gpr ms 1) = false) by (unfold w_is0; apply bv_eqb_neq; exact H1).
  rewrite E1, H2, H3, H5, H0.
  replace (mmap_off_aligned_b (Z_to_bv 64 0)) with true by (vm_compute; reflexivity).
  replace (mmap_anon_b (Z_to_bv 64 50)) with true by (vm_compute; reflexivity).
  replace (mmap_modeled_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with false
    by (vm_compute; reflexivity).
  replace (mmap_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with false
    by (vm_compute; reflexivity).
  replace (mmap_fixed_noaccess_b (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 0)) with true
    by (vm_compute; reflexivity).
  cbn [negb]. cbv beta iota zeta. rewrite Hu1.
  rewrite (proj2 (Z.leb_gt _ _)) by (alloc_top_bounds; unfold two_pow_64 in *; lia).
  rewrite (proj2 (Z.leb_le _ _) Htop). cbn [negb].
  rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
  rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. cbv beta iota.
  fold n. rewrite Hrf, Hmc. cbn [andb]. cbv beta iota.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity]. destruct zs; [|reflexivity].
  destruct cs; [|destruct us; reflexivity]. destruct ci; [|destruct us; reflexivity].
  destruct (errno_ret_in mmap_errnos r); [destruct us; reflexivity|].
  unfold fixed_noaccess_model, with_mmap_replacement, with_mmap_backing.
  replace (mmap_noreserve_b (Z_to_bv 64 50)) with false by (vm_compute; reflexivity). reflexivity.
Qed.

Lemma rz_mmap_fixed_noaccess : forall regs (pc : word) mem model w (addr : word) (len : Z) KA KB KC,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 222 ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 50 ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (forall e, In e mmap_errnos ->
     realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model) KA) ->
  realizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4) (unfill addr n mem) (seg_rom segs))
                       (fixed_noaccess_model addr n model)) KB ->
  (forall e, In e mmap_errnos ->
     realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) (unfill addr n mem) (seg_rom segs))
                          (fixed_destroyed_model addr n model)) KC) ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt3 KA KB KC).
Proof.
  intros regs pc mem model w addr len KA KB KC HF HE Hh Hlazy H17 H10 Hal Hpos H11 Hlen Htop H12 H13 H14 H15 n Hrf Hmc HA HB HC.
  pose proof (u64_range addr) as Har. pose proof (page_round_up_Z_ge_all len) as Hge.
  assert (Hlen' : (len < 2 ^ 64)%Z) by (alloc_top_bounds; unfold two_pow_64 in *; lia).
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := epend regs pc mem (seg_rom segs) (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hargs : mmap_fixed_args_ok ms).
  { unfold mmap_fixed_args_ok, ms.
    rewrite ms_gpr_epend1, ms_gpr_epend2, ms_gpr_epend3, ms_gpr_epend4, ms_gpr_epend5.
    rewrite H11, H12, H13, H14, H15. repeat split; try reflexivity.
    intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia. }
  pose proof (fun eff => mmap_fixed_check ms (getr regs 17) model eff addr len Hno Hargs
                ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen Htop Hrf Hmc) as Hchk.
  cbv zeta in Hchk. fold n in Hchk.
  pose (effs := fun i : three => match i with
                           | T1 => mkEffectU (errno_ret ENOMEM) [] [] [] [] []
                           | T2 => mkEffectU addr [] [] [(addr, n)] [] []
                           | T3 => mkEffectU (errno_ret ENOMEM) [] [] [(addr, n)] [] [] end).
  pose (ms' := fun i : three => match i with
                          | T1 => model
                          | T2 => fixed_noaccess_model addr n model
                          | T3 => fixed_destroyed_model addr n model end).
  (* [comment removed for export] *)
  assert (Herr : forall e, In e mmap_errnos -> e = ENOMEM).
  { intros e [<-|[]]. reflexivity. }
  assert (Hne : errno_ret_in mmap_errnos addr = false).
  { apply errno_ret_in_below; [reflexivity|]. alloc_top_bounds. unfold two_pow_64 in *. lia. }
  assert (Hee : errno_ret_in mmap_errnos (errno_ret ENOMEM) = true) by (vm_compute; reflexivity).
  apply (rz_alt3 segs (mkCfg ms model) (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))).
  - apply (node_chk segs ms model (getr regs 17) three effs ms' Hh eq_refl).
    + intros [| |]; cbn [effs ms']; rewrite Hchk.
      * rewrite Hee. reflexivity.
      * rewrite Hne, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
      * rewrite Hee, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
    + intros eff m' evs Hc. rewrite Hchk in Hc.
      destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r) eqn:Her.
      * apply errno_ret_in_true in Her. destruct Her as (e & He & ->). rewrite (Herr e He).
        destruct us as [|u us].
        -- injection Hc as <- <-. exists T1. auto.
        -- destruct (listNN_eqb (u :: us) [(addr, n)]) eqn:Hus; [|discriminate].
           apply listNN_eqb_eq in Hus. rewrite Hus. injection Hc as <- <-. exists T3. auto.
      * destruct (bv_eqb r addr) eqn:Hra; [|discriminate].
        destruct (listNN_eqb us [(addr, n)]) eqn:Hus; [|discriminate].
        apply bv_eqb_eq in Hra. apply listNN_eqb_eq in Hus. subst r us. injection Hc as <- <-.
        exists T2. auto.
    + intros eff Hc. rewrite Hchk in Hc.
      destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
      destruct cs; [|destruct us; discriminate]. destruct ci; [|destruct us; discriminate].
      destruct (errno_ret_in mmap_errnos r).
      * destruct us; [discriminate|]. destruct (listNN_eqb _ [(addr, n)]); discriminate.
      * destruct (bv_eqb r addr && listNN_eqb us [(addr, n)]); discriminate.
    + intros [| |]; cbn [ms']; [exact Hh | unfold fixed_noaccess_model | unfold fixed_destroyed_model];
        rewrite vm_forget_range_halted, with_vmmaps_halted; exact Hh.
    + intros [| |]; cbn [ms']; [exact Hlazy | unfold fixed_noaccess_model | unfold fixed_destroyed_model];
        apply vm_forget_range_lazy_nil; rewrite with_vmmaps_lazy'; exact Hlazy.
  - cbn [effs ms']. unfold ms. rewrite adv_ret_epend. apply HA. apply ENOMEM_in_mmap_errnos.
  - cbn [effs ms']. unfold ms. rewrite adv_unmaps1_epend. exact HB.
  - cbn [effs ms']. unfold ms. rewrite adv_unmaps1_epend. apply HC. apply ENOMEM_in_mmap_errnos.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rz_set_tid : forall regs (pc : word) mem rom model K w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 96 ->
  m_tid model = None ->
  (forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
     realizes segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model K w HF HE Hh Hlazy H17 Htid Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  assert (Hno : bv_unsigned (getr regs 17) = 96%Z) by (rewrite H17; apply u64_lit; lia).
  set (t1 := exist (fun t : word => (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z) (Z_to_bv 64 1) one_tid_ok : tid_I).
  apply (rz_conseq segs _ (t_alt (fun _ : tid_I => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists t1; exact Ht]].
  apply (rz_cases segs _ tid_I
           (fun i => mkCfg (advance_past_svc (set_gpr0 (epend regs pc mem rom (getr regs 17)) (proj1_sig i)))
                           (with_tid (proj1_sig i) model)) (fun _ => K) t1).
  - apply (node_set_tid segs (epend regs pc mem rom (getr regs 17)) model (getr regs 17) Hh Hlazy eq_refl Hno Htid).
  - intros [t Ht]. cbn [proj1_sig]. rewrite adv_set_epend. apply Hc. exact Ht.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma grant_ok_over_budget : forall hint (m : Model) (a : word) (n : Z),
  (vm_limit (m_vmmaps m) < vm_backing_used m + n)%Z ->
  grant_ok hint m a n = false.
Proof.
  intros hint m a n H. unfold grant_ok.
  rewrite (proj2 (Z.leb_gt _ _) H). apply andb_false_r.
Qed.

(* [comment removed for export] *)
Lemma grant_exists_na_gen : forall (m : Model) (N n C : Z),
  init_sp_ok (m_vmmaps m) ->
  (0 < N)%Z -> (N mod page_size = 0)%Z -> (0 <= n <= N)%Z ->
  Forall (fun p => bv_unsigned (snd p) <= N)%Z (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  (Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= C)%Z ->
  (bottomup_floor + C * (2 * N) + N <= alloc_ceiling)%Z ->
  exists a, grant_ok_na_pin m a n = true.
Proof.
  intros m N n C Hisp HN HNal Hn Hsz Hcnt Hband.
  pose proof (alloc_ceiling_le_alloc_top _ Hisp) as Htop.
  set (l := vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) in *.
  destruct (pick_candidate N n l (seq 0 (S (length l))) Hn Hsz (List.seq_NoDup _ _) ltac:(rewrite length_seq; lia))
    as (j & Hj & Hfree).
  apply in_seq in Hj.
  exists (Z_to_bv 64 (cand N j)).
  pose proof alloc_ceiling_val as Hcv. pose proof bottomup_floor_val as Hfv.
  assert (Hc : (bottomup_floor <= cand N j <= bottomup_floor + C * (2 * N))%Z) by (unfold cand; nia).
  unfold grant_ok_na_pin. rewrite !u64_lit by lia.
  assert (E1 : (cand N j mod page_size = 0)%Z).
  { unfold cand. rewrite Hfv. unfold page_size in *. rewrite Z.add_mod, Z.mul_assoc, Z.mul_mod, HNal by lia.
    rewrite Z.mul_0_r. reflexivity. }
  rewrite (proj2 (Z.eqb_eq _ _) E1), (proj2 (Z.ltb_lt 0 _)) by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia.
  fold l. rewrite (region_free_of_noconflict l (cand N j) n) by (first [lia | exact Hfree]).
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grant_exists_gen : forall hint (m : Model) (N n C : Z),
  init_sp_ok (m_vmmaps m) ->
  (0 < N)%Z -> (N mod page_size = 0)%Z -> (0 <= n <= N)%Z ->
  Forall (fun p => bv_unsigned (snd p) <= N)%Z (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  (Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= C)%Z ->
  (bottomup_floor + C * (2 * N) + N <= alloc_ceiling)%Z ->
  (vm_backing_used m + n <= vm_limit (m_vmmaps m))%Z ->
  exists a, grant_ok hint m a n = true.
Proof.
  intros hint m N n C Hisp HN HNal Hn Hsz Hcnt Hband Hlive.
  destruct (grant_exists_na_gen m N n C Hisp HN HNal Hn Hsz Hcnt Hband) as [a Ha].
  exists a. unfold grant_ok. unfold grant_ok_na_pin in Ha.
  rewrite Ha. rewrite (proj2 (Z.leb_le _ _) Hlive). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma grant_exists : forall hint (m : Model) (n : Z),
  init_sp_ok (m_vmmaps m) ->
  (0 <= n <= 2 ^ 30)%Z ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30)%Z (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  (Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 40000)%Z ->
  (vm_backing_used m + n <= vm_limit (m_vmmaps m))%Z ->
  exists a, grant_ok hint m a n = true.
Proof.
  intros hint m n Hisp Hn Hsz Hcnt Hlive.
  apply (grant_exists_gen hint m (2 ^ 30) n 40000); try assumption; try lia.
  - reflexivity.
  - rewrite alloc_ceiling_val, bottomup_floor_val. cbn. discriminate.
Qed.

Lemma grant_exists_na : forall (m : Model) (n : Z),
  init_sp_ok (m_vmmaps m) ->
  (0 <= n <= 2 ^ 30)%Z ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30)%Z (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  (Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 40000)%Z ->
  exists a, grant_ok_na_pin m a n = true.
Proof.
  intros m n Hisp Hn Hsz Hcnt.
  apply (grant_exists_na_gen m (2 ^ 30) n 40000); try assumption; try lia.
  - reflexivity.
  - rewrite alloc_ceiling_val, bottomup_floor_val. cbn. discriminate.
Qed.

(* [comment removed for export] *)
Lemma grant_exists_big : forall hint (m : Model) (n : Z),
  init_sp_ok (m_vmmaps m) ->
  (0 <= n <= 2 ^ 35)%Z ->
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 35)%Z (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) ->
  (Z.of_nat (length (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m))) <= 1000)%Z ->
  (vm_backing_used m + n <= vm_limit (m_vmmaps m))%Z ->
  exists a, grant_ok hint m a n = true.
Proof.
  intros hint m n Hisp Hn Hsz Hcnt Hlive.
  apply (grant_exists_gen hint m (2 ^ 35) n 1000); try assumption; try lia.
  - reflexivity.
  - rewrite alloc_ceiling_val, bottomup_floor_val. cbn. discriminate.
Qed.

End WithSegsMM.
