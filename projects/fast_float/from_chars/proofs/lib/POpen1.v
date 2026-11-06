(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi Syscall.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec CatSim SeqExec StepTac StoreOk DriverCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require RefLayout.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require SysNodesCfg FileLib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefLayout.ArgvEnv OSSVerify.Proofs.fast_float.from_chars.lib.Common.SysNodesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FileLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Arr.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvData PDrvMain.
From OSSVerify.Proofs.fast_float.from_chars.lib Require POpenCert.
From OSSVerify.Proofs.fast_float.from_chars.lib Require PDrvCall PDrvExit PDrvSys RefStartup RefStartupDefs PUsageCert POpenCert Spec.
Import OSSVerify.Proofs.fast_float.from_chars.lib.PDrvData OSSVerify.Proofs.fast_float.from_chars.lib.PDrvMain OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert.PDrvMain2 OSSVerify.Proofs.fast_float.from_chars.lib.PDrvCall OSSVerify.Proofs.fast_float.from_chars.lib.PDrvExit OSSVerify.Proofs.fast_float.from_chars.lib.PDrvSys OSSVerify.Proofs.fast_float.from_chars.lib.RefStartup OSSVerify.Proofs.fast_float.from_chars.lib.RefStartupDefs OSSVerify.Proofs.fast_float.from_chars.lib.PUsageCert OSSVerify.Proofs.fast_float.from_chars.lib.POpenCert OSSVerify.Proofs.fast_float.from_chars.lib.Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition FDS0 : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].

(* [comment removed for export] *)
Definition OPEN_SPEC (path : list byte) (fs0 : Fs.Fs) : TSet :=
  if (4096 <=? length path)%nat then t_die (msg_cannot_open path) fs0
  else if path_eqb path [] then t_die (msg_cannot_open path) fs0
  else if path_is_dirref path then t_alt2 (t_die (msg_cannot_open path) fs0) (t_die (msg_read_error path) fs0)
  else match fs_lookup fs0 path with
       | None => t_die (msg_cannot_open path) fs0
       | Some data => t_alt2 (t_die (msg_cannot_open path) fs0) (t_body data fs0)
       end.

Lemma spec_argc2 : forall av fs0, length av = 2%nat -> spec av fs0 = OPEN_SPEC (nth 1 av []) fs0.
Proof. intros av fs0 H. destruct av as [|a0 [|a1 [|? ?]]]; cbn in H; try discriminate. reflexivity. Qed.

Lemma u_errno : forall e, 1 <= e <= 4095 -> bv_unsigned (errno_ret e) = 18446744073709551616 - e.
Proof.
  intros e He. unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  replace (- e) with ((18446744073709551616 - e) + (-1) * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Section UO.
Variable sp0 : word.
Variables av ev : list (list byte).
Variables uid tid hw : word.
Variable rdraw : EntryDraw.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Hypothesis Hsp : valid_sp sp0.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
Hypothesis ME : main_entry sp0 av ev uid tid hw rdraw regs mem.
Hypothesis Hargc2 : length av = 2%nat.
Variable model : Model.
Hypothesis Hh : m_halted model = None.
Hypothesis Hl : m_vm_lazy model = [].
Hypothesis Hfds : m_fds model = FDS0.

Let E := E_main sp0 av ev tid (canary rdraw) regs.
Local Notation p1 := (cat_argv_ptr sp0 av ev 1).
Local Notation a1s := (nth 1 av []).

#[using="Hva Hargc2"] Lemma a1s_nonul : ~ In (Z_to_bv 8 0) a1s.
Proof. LiaFast.lf_pins (fun (Hva Hargc2 : LiaFast.U) => LiaFast.u0).
  destruct Hva as (_ & _ & _ & Hz & _). rewrite Forall_forall in Hz. apply Hz. apply nth_In. lia.
Qed.

#[using="sp0 ev uid tid hw rdraw regs mem Hva Htid ME Hargc2"] Lemma a1s_noslash : path_has_slash a1s = false.
Proof. LiaFast.lf_pins (fun (sp0 ev uid tid hw rdraw regs mem Hva Htid ME Hargc2 : LiaFast.U) => LiaFast.u0).
  destruct Hva as (_ & _ & _ & _ & Hs). rewrite Forall_forall in Hs.
  destruct av as [|a0 [|a1 [|? ?]]]; cbn in Hargc2; try discriminate. cbn [nth].
  exact (proj1 (Hs a1 ltac:(cbn; tauto))).
Qed.

(* [comment removed for export] *)
#[using="uid hw Hsp Hva Hve ME Hargc2"] Lemma path_bytes : forall E1 ms1, agree 200 E E1 -> sden PSEGS E1 L_O ms1 ->
  (forall x, outside E (s_rgs P_main2) x -> ms_mem ms1 x = mem x) ->
  bytes_at PSEGS (ms_mem ms1) (bv_unsigned p1) (a1s ++ [Z_to_bv 8 0]).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve ME Hargc2 : LiaFast.U) => LiaFast.u0).
  intros E1 ms1 Ha1 Hd1 Hmf1.
  pose proof (p1_bounds sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as (B1 & B2 & B3).
  pose proof (sp0_lo sp0 Hsp) as L. pose proof (sp0_hi sp0 Hsp) as H.
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as SL1.
  assert (HE1 : forall x, (x < 200)%positive -> E1 x = E x) by (intros x Hx; symmetry; exact (Ha1 x Hx)).
  pose proof (rdn_argv1 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as R.
  pose proof (bytes_at_of_rdn mem (bv_unsigned p1) (a1s ++ [Z_to_bv 8 0]) ltac:(lia) ltac:(rewrite length_app; cbn; unfold two64; lia)
                ltac:(rewrite Z_to_bv_bv_unsigned, length_app; exact R)) as BM.
  apply bytes_at_app in BM as [BS _]. apply bytes_at_app. split.
  - apply (bytes_at_ext_m mem); [exact BS|]. intros x Hx. apply Hmf1.
    apply (outside_main2_hi sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2); lia.
  - apply bytes_at_of_rdn; [lia | cbn; unfold two64; lia|].
    assert (HA2 : bv_unsigned (lden E1 (rg_base (rgn L_O 2))) = bv_unsigned p1 + Z.of_nat (length a1s)).
    { replace (rg_base (rgn L_O 2)) with (ladd P1 X1) by (vm_compute; reflexivity).
      rewrite <- (lden_agree 200 E E1 (ladd P1 X1) ltac:(vm_compute; reflexivity) Ha1).
      exact (u_P1X1 sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2). }
    pose proof (sden_rg _ _ _ _ _ _ Hd1 (rgn_eq L_O 2 ltac:(vm_compute; lia))) as HR2.
    pose proof (rg_rdn_gb PSEGS E1 _ _ 0 1 [BK 0] HR2 ltac:(lia) ltac:(vm_compute; reflexivity)) as X.
    rewrite HA2, Z.add_0_r in X. exact X.
Qed.

#[using="Hargc2"] Lemma agree_200 : forall E1 E2 (n : positive), agree 200 E E1 -> (200 <= n)%positive -> agree n E1 E2 -> agree 200 E E2.
Proof. LiaFast.lf_pins (fun (Hargc2 : LiaFast.U) => LiaFast.u0). intros E1 E2 n H1 Hn H2 x Hx. rewrite (H1 x Hx). apply H2. lia. Qed.

(* [comment removed for export] *)
#[using="Hargc2"] Lemma cont_errno : forall E1 ms1 (e : Z) T, 1 <= e <= 4095 -> agree 200 E E1 -> sden PSEGS E1 L_O ms1 ->
  (forall E2 ms2, agree 200 E E2 -> sden PSEGS E2 U_oe ms2 -> ms_mem ms2 = ms_mem ms1 -> ms_rom ms2 = ms_rom ms1 ->
      realizes PSEGS (mkCfg ms2 model) T) ->
  realizes PSEGS (mkCfg (@mkst (mkFP (ms_fregs ms1) (ms_fcsr ms1)) (regupd (ms_regs ms1) 10 (errno_ret e))
                           (v_addi (Z_to_bv 64 (s_pc L_O)) 4) (ms_mem ms1) (ms_rom ms1)) model) T.
Proof. LiaFast.lf_pins (fun (Hargc2 : LiaFast.U) => LiaFast.u0).
  intros E1 ms1 e T He Ha1 Hd1 Hk.
  apply (fx_sys_ret E1 L_O ms1 model (errno_ret e) None T Hd1 hok_oe ltac:(intros l Hc; discriminate Hc)
           ltac:(vm_compute; congruence) ltac:(vm_compute; congruence)).
  intros E' ms' Ha' Hd' Hm' Hr' H10.
  refine (Hk E' ms' (agree_200 E1 E' (s_next L_O) Ha1 ltac:(vm_compute; congruence) Ha') _ Hm' Hr').
  rewrite <- U_oe_eq. apply fx_add_fact; [exact Hd' | exact fwf_oe |].
  cbn [fact_ok]. rewrite <- (getr_leaf PSEGS E' _ ms' 10 (lvar (NXO + 10)) Hd') by (vm_compute; reflexivity).
  rewrite H10, u_errno by lia. lia.
Qed.

(* [comment removed for export] *)
#[using="Hargc2"] Lemma cont_fd : forall E1 ms1 model' T, agree 200 E E1 -> sden PSEGS E1 L_O ms1 ->
  (forall E2 ms2, agree 200 E E2 -> sden PSEGS E2 U_ofd ms2 -> ms_mem ms2 = ms_mem ms1 -> ms_rom ms2 = ms_rom ms1 ->
      realizes PSEGS (mkCfg ms2 model') T) ->
  realizes PSEGS (mkCfg (@mkst (mkFP (ms_fregs ms1) (ms_fcsr ms1)) (regupd (ms_regs ms1) 10 (Z_to_bv 64 3))
                           (v_addi (Z_to_bv 64 (s_pc L_O)) 4) (ms_mem ms1) (ms_rom ms1)) model') T.
Proof. LiaFast.lf_pins (fun (Hargc2 : LiaFast.U) => LiaFast.u0).
  intros E1 ms1 model' T Ha1 Hd1 Hk.
  apply (fx_sys_ret E1 L_O ms1 model' (Z_to_bv 64 3) (Some (lconst 3)) T Hd1 hok_ofd
           ltac:(intros l Hc; injection Hc as <-; apply lden_lconst) ltac:(vm_compute; congruence) ltac:(vm_compute; congruence)).
  intros E' ms' Ha' Hd' Hm' Hr' H10.
  refine (Hk E' ms' (agree_200 E1 E' (s_next L_O) Ha1 ltac:(vm_compute; congruence) Ha') _ Hm' Hr').
  rewrite <- U_ofd_eq. exact Hd'.
Qed.

#[using="uid hw Hsp Hva Hve Htid ME Hargc2 Hh Hl Hfds"] Theorem open_node : forall E1 ms1, agree 200 E E1 -> sden PSEGS E1 L_O ms1 -> ms_rom ms1 = seg_rom PSEGS ->
  (forall x, outside E (s_rgs P_main2) x -> ms_mem ms1 x = mem x) ->
  (forall E2 ms2, agree 200 E E2 -> sden PSEGS E2 U_oe ms2 -> ms_rom ms2 = seg_rom PSEGS ->
     (forall x, outside E (s_rgs P_main2) x -> ms_mem ms2 x = mem x) -> ms_mem ms2 = ms_mem ms1 ->
     realizes PSEGS (mkCfg ms2 model) (t_die (msg_cannot_open a1s) (m_fs model))) ->
  (path_is_dirref a1s = true -> forall E2 ms2, agree 200 E E2 -> sden PSEGS E2 U_ofd ms2 -> ms_rom ms2 = seg_rom PSEGS ->
     (forall x, outside E (s_rgs P_main2) x -> ms_mem ms2 x = mem x) -> ms_mem ms2 = ms_mem ms1 ->
     realizes PSEGS (mkCfg ms2 (with_fds (fd_insert FDS0 (Z_to_bv 64 3) FdDir) model)) (t_die (msg_read_error a1s) (m_fs model))) ->
  (forall data, path_is_dirref a1s = false -> fs_lookup (m_fs model) a1s = Some data ->
     forall E2 ms2, agree 200 E E2 -> sden PSEGS E2 U_ofd ms2 -> ms_rom ms2 = seg_rom PSEGS ->
     (forall x, outside E (s_rgs P_main2) x -> ms_mem ms2 x = mem x) -> ms_mem ms2 = ms_mem ms1 ->
     realizes PSEGS (mkCfg ms2 (with_fds (fd_insert FDS0 (Z_to_bv 64 3) (FdFile a1s (Z_to_bv 64 0))) model)) (t_body data (m_fs model))) ->
  realizes PSEGS (mkCfg ms1 model) (spec av (m_fs model)).
Proof. LiaFast.lf_pins (fun (uid hw Hsp Hva Hve Htid ME Hargc2 Hh Hl Hfds : LiaFast.U) => LiaFast.u0).
  intros E1 ms1 Ha1 Hd1 Hrom1 Hmf1 KE KD KF.
  rewrite (spec_argc2 av _ Hargc2).
  pose proof (path_bytes E1 ms1 Ha1 Hd1 Hmf1) as BP.
  pose proof (p1_bounds sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve ME Hargc2) as (B1 & B2 & B3).
  pose proof (valid_argv_str_len av 1 Hva ltac:(lia)) as SL1.
  assert (HE1 : forall x, (x < 200)%positive -> E1 x = E x) by (intros x Hx; symmetry; exact (Ha1 x Hx)).
  assert (R17 : getr (ms_regs ms1) 17 = Z_to_bv 64 56) by (apply (getr_leaf_c PSEGS E1 L_O); [exact Hd1 | vm_compute; reflexivity]).
  assert (R10 : getr (ms_regs ms1) 10 = Z_to_bv 64 18446744073709551516) by (apply (getr_leaf_c PSEGS E1 L_O); [exact Hd1 | vm_compute; reflexivity]).
  assert (R11 : getr (ms_regs ms1) 11 = p1).
  { rewrite (getr_leaf PSEGS E1 L_O ms1 11 (lvar 4) Hd1) by (vm_compute; reflexivity). rewrite lden_lvar, HE1 by lia.
    exact (E_P1 sp0 av ev tid rdraw regs Hargc2). }
  assert (R12 : getr (ms_regs ms1) 12 = Z_to_bv 64 32768) by (apply (getr_leaf_c PSEGS E1 L_O); [exact Hd1 | vm_compute; reflexivity]).
  assert (HFD : fd32 (getr (ms_regs ms1) 10) = AT_FDCWD32) by (rewrite R10; vm_compute; reflexivity).
  assert (HFL : Z.ldiff (bv_unsigned (getr (ms_regs ms1) 12)) open_ignored_flags = 0) by (rewrite R12; vm_compute; reflexivity).
  assert (HFREE : fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None) by (rewrite Hfds; vm_compute; reflexivity).
  assert (HA3 : alloc_fd (m_fds model) = Z_to_bv 64 3) by (rewrite Hfds; vm_compute; reflexivity).
  (* [comment removed for export] *)
  destruct (mk_tbl_ranges_ecall PSEGS RS_P 0x5ee74 ltac:(rewrite <- TBL_P_eq; vm_compute; reflexivity)) as (w & Hw & Hec).
  rewrite (sden_mkst PSEGS E1 L_O ms1 Hd1 eq_refl).
  apply (rzc_ecall PSEGS DCFG (ms_regs ms1) _ (ms_mem ms1) (ms_rom ms1) model w _ Hh Hl Hw Hec).
  rewrite Hrom1.
  assert (KE' : forall e, 1 <= e <= 4095 ->
            realizes PSEGS (mkCfg (@mkst (mkFP (ms_fregs ms1) (ms_fcsr ms1)) (regupd (ms_regs ms1) 10 (errno_ret e))
                                    (v_addi (Z_to_bv 64 0x5ee74) 4) (ms_mem ms1) (seg_rom PSEGS)) model) (t_die (msg_cannot_open a1s) (m_fs model))).
  { intros e He. rewrite <- Hrom1. apply (cont_errno E1 ms1 e _ He Ha1 Hd1).
    intros E2 ms2 Ha2 Hd2 Hm2 Hr2. apply (KE E2 ms2 Ha2 Hd2); [rewrite Hr2; exact Hrom1 | intros x Hx; rewrite Hm2; exact (Hmf1 x Hx) | exact Hm2]. }
  assert (KO : forall e, In e openat_errnos -> 1 <= e <= 4095) by (intros e He; cbn in He; unfold ENOMEM, EACCES, EMFILE, ENFILE in He; lia).
  assert (RD : forall model' T, (forall E2 ms2, agree 200 E E2 -> sden PSEGS E2 U_ofd ms2 -> ms_rom ms2 = seg_rom PSEGS ->
                    (forall x, outside E (s_rgs P_main2) x -> ms_mem ms2 x = mem x) -> ms_mem ms2 = ms_mem ms1 -> realizes PSEGS (mkCfg ms2 model') T) ->
            realizes PSEGS (mkCfg (@mkst (mkFP (ms_fregs ms1) (ms_fcsr ms1)) (regupd (ms_regs ms1) 10 (Z_to_bv 64 3))
                                    (v_addi (Z_to_bv 64 0x5ee74) 4) (ms_mem ms1) (seg_rom PSEGS)) model') T).
  { intros model' T HK. rewrite <- Hrom1. apply (cont_fd E1 ms1 model' T Ha1 Hd1).
    intros E2 ms2 Ha2 Hd2 Hm2 Hr2. apply (HK E2 ms2 Ha2 Hd2); [rewrite Hr2; exact Hrom1 | intros x Hx; rewrite Hm2; exact (Hmf1 x Hx) | exact Hm2]. }
  unfold OPEN_SPEC. destruct (4096 <=? length a1s)%nat eqn:HTL.
  - (* [comment removed for export] *)
    apply Nat.leb_le in HTL.
    apply (@rzc_openat_toolong _ PSEGS DCFG eq_refl (ms_regs ms1) _ (ms_mem ms1) model _ Hh Hl R17 HFL).
    + rewrite R11. apply (read_cstr_toolong_of_rdn PSEGS (ms_mem ms1) p1 (firstn 4096 a1s)).
      * rewrite length_firstn. lia.
      * intros Hin. apply a1s_nonul. rewrite <- (firstn_skipn 4096 a1s). apply in_or_app. left. exact Hin.
      * pose proof (bytes_at_rdn PSEGS (ms_mem ms1) (bv_unsigned p1) (a1s ++ [Z_to_bv 8 0]) 0 4096 BP ltac:(rewrite length_app; cbn; lia)) as X.
        rewrite Z.add_0_r, skipn_O, firstn_app in X.
        replace (4096 - length a1s)%nat with 0%nat in X by lia. cbn [firstn] in X. rewrite app_nil_r in X. unfold wa in X.
        rewrite Z_to_bv_bv_unsigned in X. exact X.
    + apply KE'. unfold ENAMETOOLONG. lia.
  - apply Nat.leb_gt in HTL.
    assert (HC : read_cstr (mrb PSEGS (ms_mem ms1)) (getr (ms_regs ms1) 11) = CstrOk a1s).
    { rewrite R11. apply read_cstr_of_rdn; [lia | exact a1s_nonul |].
      pose proof (rdn_of_bytes_at _ _ _ BP) as X. rewrite Z_to_bv_bv_unsigned, length_app in X. exact X. }
    destruct (path_eqb a1s []) eqn:HE0.
    + (* [comment removed for export] *)
      apply path_eqb_eq in HE0. rewrite HE0 in HC.
      apply (@rzc_openat_empty _ PSEGS DCFG eq_refl (ms_regs ms1) _ (ms_mem ms1) model _ Hh Hl R17 HFL HC).
      apply KE'. unfold ENOENT. lia.
    + destruct (path_is_dirref a1s) eqn:HDR.
      * (* [comment removed for export] *)
        apply (@rzc_openat_dirref _ PSEGS DCFG eq_refl (ms_regs ms1) _ (ms_mem ms1) model a1s _ _ Hh Hl R17 HFD HFL HC HE0 a1s_noslash HDR HFREE).
        -- intros e He. apply KE'. exact (KO e He).
        -- rewrite HA3, Hfds. apply RD. exact (KD eq_refl).
      * destruct (fs_lookup (m_fs model) a1s) as [data|] eqn:HLK.
        -- (* [comment removed for export] *)
           apply (@rzc_openat_file _ PSEGS DCFG eq_refl (ms_regs ms1) _ (ms_mem ms1) model a1s data _ _ Hh Hl R17 HFD HFL HC HE0 a1s_noslash HDR HLK HFREE).
           ++ intros e He. apply KE'. exact (KO e He).
           ++ rewrite HA3, Hfds. apply RD. exact (KF data eq_refl eq_refl).
        -- (* [comment removed for export] *)
           apply (@rzc_openat_enoent _ PSEGS DCFG eq_refl (ms_regs ms1) _ (ms_mem ms1) model a1s _ Hh Hl R17 HFD HFL HC HE0 a1s_noslash HDR HLK).
           apply KE'. unfold ENOENT. lia.
Qed.
End UO.
