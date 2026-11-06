(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude Fs.Open Fs.ReadWrite Fs.Ioctl.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec FileSim
  ShapeAlg ShapeNodes Nodes StoreOk AgentLib SpecConsts RefNodes PureModel CfgStep.
Import ListNotations.
Open Scope bv_scope.

Lemma check_syscall_29 : forall segs ms x8 eff m,
  bv_unsigned x8 = 29%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_ioctl (fd32 (ms_gpr ms 0)) (cmd32 (ms_gpr ms 1)) eff m.
Proof. intros segs ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.

Section At.
Context {fx : FPState}.
Variable segs : list Segment.

Lemma md_pure_with_fds : forall f md, md_pure md -> md_pure (with_fds f md).
Proof. intros f md [H1 H2 H3]. constructor; [exact H1 | exact H2 | exact H3]. Qed.

Lemma fd_small_32 : forall fd : word, (bv_unsigned fd < 2 ^ 31)%Z -> fd32 fd = fd.
Proof. intros fd H. apply fd32_small. lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_close_at : forall regs (pc : word) mem rom model w (fd : word) e K,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 57%Z ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 31)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom)
                       (with_fds (fd_remove (m_fds model) fd) model)) K ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w fd e K Hp HF HE H17 H10 Hfd Hlk Hc.
  pose proof (mp_halted _ Hp) as Hh. pose proof (mp_lazy _ Hp) as Hlazy.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (rz_ret_only_silent segs (ecall_st regs pc mem rom) model (getr regs 17) (Z_to_bv 64 0)
           (with_fds (fd_remove (m_fds model) fd) model));
    [exact Hh | reflexivity | | exact Hh | exact Hlazy | reflexivity | rewrite adv_setgpr0_st; exact Hc].
  intros eff. rewrite (check_syscall_57 segs _ _ eff model H17). unfold check_close.
  rewrite ecall_st_gpr0, H10, (fd_small_32 fd Hfd), Hlk. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma tty_winsz : forall r : word, bv_unsigned r = 0x5413%Z -> tty_only_request (cmd32 r) = true.
Proof.
  intros r Hr. unfold cmd32, abi_low32. rewrite Hr. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Definition fd_not_devnull (e : FdEntry) : bool :=
  match e with FdDevNull _ _ => false | FdUrandom => false | _ => true end.

Lemma rz_ioctl_winsz_at : forall regs (pc : word) mem rom model w (fd : word) e K,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 29%Z ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 31)%Z ->
  fd_lookup (m_fds model) fd = Some e ->
  fd_not_devnull e = true ->
  bv_unsigned (getr regs 11) = 0x5413%Z ->
  realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOTTY)) (v_addi pc 4) mem rom) model) K ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w fd e K Hp HF HE H17 H10 Hfd Hlk Hnd H11 Hc.
  pose proof (mp_halted _ Hp) as Hh. pose proof (mp_lazy _ Hp) as Hlazy.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (rz_ret_only_silent segs (ecall_st regs pc mem rom) model (getr regs 17) (errno_ret ENOTTY) model);
    [exact Hh | reflexivity | | exact Hh | exact Hlazy | reflexivity | rewrite adv_setgpr0_st; exact Hc].
  intros eff. rewrite (check_syscall_29 segs _ _ eff model H17). unfold check_ioctl.
  rewrite ecall_st_gpr0, ecall_st_gpr1, H10, (fd_small_32 fd Hfd), Hlk, (tty_winsz _ H11).
  destruct e; try reflexivity; discriminate Hnd.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_read_dir_at : forall regs (pc : word) mem rom model w (fd : word) K,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 63%Z ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 31)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  access_okb (getr regs 11) (bv_unsigned (getr regs 12)) = true ->
  realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem rom) model) K ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
  intros regs pc mem rom model w fd K Hp HF HE H17 H10 Hfd Hlk Haok Hc.
  pose proof (mp_halted _ Hp) as Hh. pose proof (mp_lazy _ Hp) as Hlazy.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (rz_ret_only_silent segs (ecall_st regs pc mem rom) model (getr regs 17) (errno_ret EISDIR) model);
    [exact Hh | reflexivity | | exact Hh | exact Hlazy | reflexivity | rewrite adv_setgpr0_st; exact Hc].
  intros eff. rewrite (check_syscall_63 segs _ _ eff model H17). unfold check_read.
  rewrite ecall_st_gpr0, ecall_st_gpr1, ecall_st_gpr2, H10, (fd_small_32 fd Hfd), Hlk, Haok. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_read_file_at : forall regs (pc : word) mem model w (fd buf cnt : word) p off data wv K,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 63%Z ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 31)%Z ->
  getr regs 11 = buf -> getr regs 12 = cnt ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  read_bytes_map (wview segs mem) buf cnt = Some wv ->
  (0 < bv_unsigned cnt <= rw_bytes_max)%Z ->
  access_okb buf (bv_unsigned cnt) = true ->
  realizes segs (mkCfg (mkst (regupd regs 10 (len_word (file_read data off cnt))) (v_addi pc 4)
                             (wbytes mem buf (file_read data off cnt)) (seg_rom segs))
                       (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word (file_read data off cnt)))) model)) K ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd buf cnt p off data wv K Hp HF HE H17 H10 Hfd H11 H12 Hlk Hfs Hw Hcnt Haok Hc.
  set (bs := file_read data off cnt) in *.
  pose proof (mp_halted _ Hp) as Hh. pose proof (mp_lazy _ Hp) as Hlazy.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  set (ms := ecall_st regs pc mem (seg_rom segs)).
  assert (G0 : ms_gpr ms 0 = fd) by (unfold ms; rewrite ecall_st_gpr0; exact H10).
  assert (G1 : ms_gpr ms 1 = buf) by (unfold ms; rewrite ecall_st_gpr1; exact H11).
  assert (G2 : ms_gpr ms 2 = cnt) by (unfold ms; rewrite ecall_st_gpr2; exact H12).
  assert (HL : (bv_unsigned (len_word bs) <= bv_unsigned cnt)%Z).
  { unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
    pose proof (u64_range cnt) as Hcr. unfold bs. rewrite length_file_read, Nat2Z.inj_min.
    unfold word_to_nat. rewrite Z.mod_small; lia. }
  assert (Hchk : forall eff m' evs,
    check_syscall (sys_input segs ms (getr regs 17)) eff model = CheckOk m' evs <->
    (eff = mkEffect (len_word bs) (delivered_writes buf bs) []
     /\ m' = with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model
     /\ evs = [])).
  { intros eff m' evs.
    rewrite (check_syscall_63 segs ms _ eff model H17). unfold check_read.
    rewrite G0, G1, G2, (fd_small_32 fd Hfd), Hlk. cbv beta iota.
    rewrite Haok. cbn [negb]. cbv beta iota.
    rewrite (rw_count_clamp_of_rw _ (proj2 Hcnt)), Z_to_bv_bv_unsigned.
    rewrite Hfs. cbv beta iota zeta.
    unfold ms. rewrite in_wmem_si, ecall_st_writable. fold ms.
    fold bs.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw). cbv beta iota.
    unfold bs.
    destruct (file_read data off cnt) as [|b bsr].
    - cbv beta iota. rewrite check_ret_only_ok_iff. cbn [delivered_writes length]. tauto.
    - destruct eff as [ret ws zs us cs copyins]. split.
      + intro H.
        destruct ws as [|[a bs'] [|? ?]]; try discriminate.
        destruct zs as [|? ?]; [|discriminate].
        destruct us as [|? ?]; [|discriminate].
        destruct cs as [|? ?]; [|discriminate].
        destruct copyins as [|? ?]; [|discriminate].
        destruct (bv_eqb a buf && listN_eqb bs' (b :: bsr) && bv_eqb ret (len_word (b :: bsr)))
          eqn:Hb; try rewrite Hb in H; [|discriminate].
        apply andb_true_iff in Hb as [Hb Hr]. apply andb_true_iff in Hb as [Ha Hbs].
        apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hr. apply listN_eqb_eq in Hbs.
        inversion H; subst. cbn [delivered_writes]. repeat split; congruence.
      + intros (Heff & -> & ->). cbn [delivered_writes] in Heff. inversion Heff; subst.
        rewrite bv_eqb_refl, (proj2 (listN_eqb_eq _ _) eq_refl), bv_eqb_refl. cbn [andb]. reflexivity. }
  apply (rz_det segs ms model (getr regs 17)
           (mkEffect (len_word bs) (delivered_writes buf bs) [])
           (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model));
    [exact Hh | reflexivity | exact Hchk | | exact Hh | exact Hlazy | reflexivity |].
  - intros eff Hs.
    rewrite (check_syscall_63 segs ms _ _ model H17) in Hs. unfold check_read in Hs.
    rewrite G0, G1, G2, (fd_small_32 fd Hfd), Hlk in Hs. cbv beta iota in Hs.
    rewrite Haok in Hs. cbn [negb] in Hs. cbv beta iota in Hs.
    rewrite (rw_count_clamp_of_rw _ (proj2 Hcnt)), Z_to_bv_bv_unsigned in Hs.
    rewrite Hfs in Hs. cbv beta iota zeta in Hs.
    unfold ms in Hs. rewrite in_wmem_si, ecall_st_writable in Hs. fold bs in Hs.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw) in Hs. cbv beta iota in Hs.
    revert Hs. unfold bs. destruct (file_read data off cnt) as [|b0 bsr]; intro Hs.
    + exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
    + destruct eff as [ret [|[a bs'] [|? ?]] [|? ?] [|? ?] [|? ?] [|? ?]]; cbv beta iota in Hs; try discriminate.
      destruct (bv_eqb a buf && listN_eqb bs' (b0 :: bsr) && bv_eqb ret (len_word (b0 :: bsr))); discriminate.
  - unfold ms. rewrite adv_delivered_st, write_to_mem_wbytes. exact Hc.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma openat_empty_check : forall ms x8 model,
  bv_unsigned x8 = 56%Z ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk [] ->
  Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z ->
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_ret_only_copyins (open_copyins ms) eff (errno_ret ENOENT) model [].
Proof.
  intros ms x8 model Hno Hpath Hfl eff.
  rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
  rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, Hpath. cbv beta iota zeta.
  unfold check_ret_only_copyins, open_copyins.
  destruct (check_ret_only (clear_copyins eff) (errno_ret ENOENT) model []) eqn:Hresult.
  - reflexivity.
  - unfold check_copyins.
    destruct (access_ranges_eqb (eff_copyins eff)
      [(ms_gpr ms 1, cstr_access_len_aux (ms_read_byte ms) (ms_gpr ms 1) path_max)]); reflexivity.
  - exfalso. now apply check_ret_only_no_unmodeled in Hresult.
Qed.

Lemma openat_absent_check : forall ms x8 model p,
  bv_unsigned x8 = 56%Z ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = false ->
  Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z ->
  openat_plain_name p = true ->
  fs_lookup (m_fs model) p = None ->
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_ret_only_copyins (open_copyins ms) eff (errno_ret ENOENT) model [].
Proof.
  intros ms x8 model p Hno Hdirfd Hpath Hpe Hfl Hdot Hfs eff.
  pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
  apply openat_plain_name_nodirref in Hdot.
  rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
  rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, Hpath. cbv beta iota zeta.
  rewrite Hpe. cbv beta iota.
  rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
  unfold Open.check_openat_resolved.
  rewrite Hunw. cbv beta iota.
  rewrite Hfl, Z.eqb_refl. cbv beta iota.
  unfold Open.check_openat_read.
  rewrite ?Hdot, ?Hfs.
  unfold check_ret_only_copyins, open_copyins.
  destruct (check_ret_only (clear_copyins eff) (errno_ret ENOENT) model []) eqn:Hresult.
  - reflexivity.
  - unfold check_copyins.
    destruct (access_ranges_eqb (eff_copyins eff)
      [(ms_gpr ms 1, cstr_access_len_aux (ms_read_byte ms) (ms_gpr ms 1) path_max)]); reflexivity.
  - exfalso. now apply check_ret_only_no_unmodeled in Hresult.
Qed.

Lemma openat_dir_check : forall ms x8 model,
  bv_unsigned x8 = 56%Z ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk dot_path ->
  Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z ->
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_open_result_copyins (open_copyins ms) eff model
        (fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model).
Proof.
  intros ms x8 model Hno Hdirfd Hpath Hfl eff.
  rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
  rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, Hpath. cbv beta iota zeta.
  rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
  unfold Open.check_openat_resolved. cbv beta iota.
  rewrite Hfl, Z.eqb_refl. cbv beta iota.
  unfold Open.check_openat_read. cbv beta iota.
  unfold check_open_result_copyins, open_copyins.
  destruct (check_open_result (clear_copyins eff) model
    (fun fd : word => with_fds (fd_insert (m_fds model) fd FdDir) model)) eqn:Hresult.
  - reflexivity.
  - reflexivity.
  - exfalso. now apply check_open_result_never_unmodeled in Hresult.
Qed.

(* [comment removed for export] *)

Lemma rz_openat_toolong_at : forall regs (pc : word) mem model w K,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 56%Z ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  read_cstr (mrb segs mem) (getr regs 11) = CstrTooLong ->
  realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENAMETOOLONG)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w K Hp HF HE H17 Hfl Hpath Hc.
  pose proof (mp_halted _ Hp) as Hh. pose proof (mp_lazy _ Hp) as Hlazy.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (rz_ret_only_copyins_silent segs (ecall_st regs pc mem (seg_rom segs)) model (getr regs 17)
           (open_copyins (ecall_st regs pc mem (seg_rom segs))) (errno_ret ENAMETOOLONG) model);
    [exact Hh | reflexivity | | exact Hh | exact Hlazy | reflexivity | rewrite adv_setgpr0_st; exact Hc].
  intros eff. apply openat_toolong_check; [exact H17 | | ].
  - rewrite ecall_st_gpr2. apply modeled_open_flags_rd. exact Hfl.
  - rewrite ecall_st_read_byte, ecall_st_gpr1. exact Hpath.
Qed.

Lemma rz_openat_empty_at : forall regs (pc : word) mem model w K,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 56%Z ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  read_cstr (mrb segs mem) (getr regs 11) = CstrOk [] ->
  realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w K Hp HF HE H17 Hfl Hpath Hc.
  pose proof (mp_halted _ Hp) as Hh. pose proof (mp_lazy _ Hp) as Hlazy.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (rz_ret_only_copyins_silent segs (ecall_st regs pc mem (seg_rom segs)) model (getr regs 17)
           (open_copyins (ecall_st regs pc mem (seg_rom segs))) (errno_ret ENOENT) model);
    [exact Hh | reflexivity | | exact Hh | exact Hlazy | reflexivity | rewrite adv_setgpr0_st; exact Hc].
  intros eff. apply openat_empty_check; [exact H17 | | rewrite ecall_st_gpr2; exact Hfl].
  rewrite ecall_st_read_byte, ecall_st_gpr1. exact Hpath.
Qed.

Lemma rz_openat_absent_at : forall regs (pc : word) mem model w p K,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 56%Z ->
  getr regs 10 = AT_FDCWD ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  read_cstr (mrb segs mem) (getr regs 11) = CstrOk p ->
  p <> [] -> openat_plain_name p = true -> fs_lookup (m_fs model) p = None ->
  realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w p K Hp HF HE H17 H10 Hfl Hpath Hne Hplain Hfs Hc.
  pose proof (mp_halted _ Hp) as Hh. pose proof (mp_lazy _ Hp) as Hlazy.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (rz_ret_only_copyins_silent segs (ecall_st regs pc mem (seg_rom segs)) model (getr regs 17)
           (open_copyins (ecall_st regs pc mem (seg_rom segs))) (errno_ret ENOENT) model);
    [exact Hh | reflexivity | | exact Hh | exact Hlazy | reflexivity | rewrite adv_setgpr0_st; exact Hc].
  intros eff. apply (openat_absent_check _ _ model p H17).
  - rewrite ecall_st_gpr0. exact H10.
  - rewrite ecall_st_read_byte, ecall_st_gpr1. exact Hpath.
  - apply path_eqb_neq. exact Hne.
  - rewrite ecall_st_gpr2. exact Hfl.
  - exact Hplain.
  - exact Hfs.
Qed.

(* [comment removed for export] *)
Lemma rz_openat_file_at : forall regs (pc : word) mem model w p d A B,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 56%Z ->
  getr regs 10 = AT_FDCWD ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  read_cstr (mrb segs mem) (getr regs 11) = CstrOk p ->
  p <> [] -> openat_plain_name p = true -> fs_lookup (m_fs model) p = Some d ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  (forall e, In e openat_errnos ->
     realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model) A) ->
  realizes segs (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem (seg_rom segs))
                       (with_fds (fd_insert (m_fds model) (alloc_fd (m_fds model)) (FdFile p (Z_to_bv 64 0))) model)) B ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 A B).
Proof.
  intros regs pc mem model w p d A B Hp HF HE H17 H10 Hfl Hpath Hne Hplain Hfs Hfree HA HB.
  pose proof (mp_halted _ Hp) as Hh. pose proof (mp_lazy _ Hp) as Hlazy.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (rz_open segs (ecall_st regs pc mem (seg_rom segs)) model (getr regs 17)
           (open_copyins (ecall_st regs pc mem (seg_rom segs)))
           (fun fd => with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model));
    [exact Hh | exact Hlazy | reflexivity | kit_pending_on | | intros; exact Hh | intros; exact Hlazy | intros; reflexivity | exact Hfree | | ].
  - intros eff. apply (openat_rd_check segs _ _ model p d H17).
    + rewrite ecall_st_gpr0. exact H10.
    + rewrite ecall_st_read_byte, ecall_st_gpr1. exact Hpath.
    + apply path_eqb_neq. exact Hne.
    + rewrite ecall_st_gpr2. exact Hfl.
    + exact Hplain.
    + exact Hfs.
  - intros e He. rewrite adv_setgpr0_st. apply HA. exact He.
  - rewrite adv_setgpr0_st. exact HB.
Qed.

(* [comment removed for export] *)
Lemma rz_openat_dir_at : forall regs (pc : word) mem model w A B,
  md_pure model -> fetch_word segs pc = Some w -> is_ecall w = true ->
  bv_unsigned (getr regs 17) = 56%Z ->
  getr regs 10 = AT_FDCWD ->
  Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z ->
  read_cstr (mrb segs mem) (getr regs 11) = CstrOk dot_path ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  (forall e, In e openat_errnos ->
     realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4) mem (seg_rom segs)) model) A) ->
  realizes segs (mkCfg (mkst (regupd regs 10 (alloc_fd (m_fds model))) (v_addi pc 4) mem (seg_rom segs))
                       (with_fds (fd_insert (m_fds model) (alloc_fd (m_fds model)) FdDir) model)) B ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) (t_alt2 A B).
Proof.
  intros regs pc mem model w A B Hp HF HE H17 H10 Hfl Hpath Hfree HA HB.
  pose proof (mp_halted _ Hp) as Hh. pose proof (mp_lazy _ Hp) as Hlazy.
  eapply rz_ecall; [exact Hh | exact Hlazy | exact HF | exact HE |].
  apply (rz_open segs (ecall_st regs pc mem (seg_rom segs)) model (getr regs 17)
           (open_copyins (ecall_st regs pc mem (seg_rom segs)))
           (fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model));
    [exact Hh | exact Hlazy | reflexivity | kit_pending_on | | intros; exact Hh | intros; exact Hlazy | intros; reflexivity | exact Hfree | | ].
  - intros eff. apply (openat_dir_check _ _ model H17).
    + rewrite ecall_st_gpr0. exact H10.
    + rewrite ecall_st_read_byte, ecall_st_gpr1. exact Hpath.
    + rewrite ecall_st_gpr2. exact Hfl.
  - intros e He. rewrite adv_setgpr0_st. apply HA. exact He.
  - rewrite adv_setgpr0_st. exact HB.
Qed.

End At.
