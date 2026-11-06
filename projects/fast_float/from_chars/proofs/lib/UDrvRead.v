(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec StepTac StoreOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require MemSplit DriverCfg SysNodesCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.StreamSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.MemSplit OSSVerify.Proofs.fast_float.from_chars.lib.Common.DriverCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.SysNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxSubst FxStep FxDrv FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UDrvData UDrvCall UDrvSys.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition RS_LO : Z := 0x66e19.

(* [comment removed for export] *)
Lemma rs_wseg : wseg_ok PSEGS (Z_to_bv 64 RS_LO) 65536 = true.
Proof. Time vm_compute. Time reflexivity. Time Qed.

Lemma z64k : Z.of_nat 65536 = 65536. Proof. vm_compute. reflexivity. Qed.

Lemma rs_wview : forall m (x : word), RS_LO <= bv_unsigned x < RS_LO + 65536 -> wview PSEGS m x <> None.
Proof.
  intros m x Hx. apply (store_ok_all PSEGS m 65536 (Z_to_bv 64 RS_LO)).
  - rewrite z64k. rewrite u_small64 by (unfold two64, RS_LO; lia). unfold RS_LO. lia.
  - apply store_ok_wseg. exact rs_wseg.
  - rewrite z64k. rewrite u_small64 by (unfold two64, RS_LO; lia). unfold RS_LO in *. lia.
Qed.

Lemma read_bytes_map_of_store_ok : forall segs mem (a : word) (n : nat),
  store_ok segs mem a n = true -> (Z.of_nat n < 2 ^ 64)%Z ->
  exists w, read_bytes_map (wview segs mem) a (Z_to_bv 64 (Z.of_nat n)) = Some w.
Proof.
  intros segs mem a n H Hn. rewrite read_bytes_map_eq. unfold word_to_nat.
  rewrite Z_to_bv_small by (unfold bv_modulus; lia). rewrite Nat2Z.id.
  apply store_ok_read_aux. exact H.
Qed.

Lemma rs_rbm : forall m (n : Z), 0 <= n <= 65536 ->
  read_bytes_map (wview PSEGS m) (Z_to_bv 64 RS_LO) (Z_to_bv 64 n) <> None.
Proof.
  intros m n Hn. replace n with (Z.of_nat (Z.to_nat n)) by lia.
  destruct (read_bytes_map_of_store_ok PSEGS m (Z_to_bv 64 RS_LO) (Z.to_nat n)) as (w & Hw).
  - apply store_ok_of_all.
    + rewrite u_small64 by (unfold two64, RS_LO; lia). unfold RS_LO. lia.
    + intros x Hx. apply rs_wview. rewrite u_small64 in Hx by (unfold two64, RS_LO; lia). lia.
  - lia.
  - rewrite Hw. discriminate.
Qed.

(* [comment removed for export] *)
Theorem fx_sys_ret_w : forall E L ms model (v : word) (res : option lin) (m' : word -> option byte) T,
  sden PSEGS E L ms -> havoc_ok L [] res = true ->
  (forall l, res = Some l -> lden E l = v) -> 0 <= s_pc L -> s_pc L + 4 < 2 ^ 64 ->
  (forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> m' x = ms_mem ms x) ->
  mem_grows (ms_mem ms) m' ->
  (forall E' ms', agree (s_next L) E E' -> sden PSEGS E' (havoc_call L (s_pc L + 4) KEEPALL [] res) ms' ->
      ms_mem ms' = m' -> ms_rom ms' = ms_rom ms -> getr (ms_regs ms') 10 = v ->
      realizes PSEGS (mkCfg ms' model) T) ->
  realizes PSEGS (mkCfg (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (regupd (ms_regs ms) 10 v)
                           (v_addi (Z_to_bv 64 (s_pc L)) 4) m' (ms_rom ms)) model) T.
Proof.
  intros E L ms model v res m' T Hd Hok Hres Hp1 Hp2 Hrg Hgr Hk.
  set (ms' := @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (regupd (ms_regs ms) 10 v) (v_addi (Z_to_bv 64 (s_pc L)) 4) m' (ms_rom ms)).
  destruct (havoc_call_sound2 PSEGS E L ms ms' (s_pc L + 4) KEEPALL [] res Hok Hd) as (E' & Ha & Hd').
  - unfold ms', mkst, v_addi. cbn [ms_pc_val]. rewrite u_small64 by (unfold two64; lia). reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & _ & _ & _ & Hf). exact Hf.
  - intros r Hr _. unfold ms', mkst; cbn [ms_regs]. apply getr_other. exact (keepall_ne r Hr).
  - intros l Hl. unfold ms', mkst; cbn [ms_regs]. replace (Z_to_bv 5 10) with (10%bv : reg) by (apply bv_eq; reflexivity).
    rewrite getr_same by (intros Hc; discriminate Hc). symmetry. exact (Hres l Hl).
  - intros i R x Hi Hin _. unfold ms', mkst; cbn [ms_mem]. exact (Hrg i R x Hi Hin).
  - intros i R x Hi Hin. unfold ms', mkst; cbn [ms_mem]. split.
    + unfold rd1. intros H. destruct (ms_mem ms x) as [b|] eqn:E0.
      * specialize (Hgr x ltac:(rewrite E0; discriminate)). destruct (m' x); [discriminate | exfalso; exact (Hgr eq_refl)].
      * destruct (m' x); [discriminate | exact H].
    + intros H. exact (wview_grows PSEGS (ms_mem ms) m' x Hgr H).
  - apply (Hk E' ms' Ha Hd' eq_refl eq_refl). unfold ms', mkst; cbn [ms_regs]. apply getr_same. intros Hc; discriminate Hc.
Qed.

(* [comment removed for export] *)
Theorem fx_read : forall E L ms model (p : list byte) off data (want : Z) T,
  sden PSEGS E L ms -> s_pc L = 0x60c2c -> s_resv L = RNone -> ms_rom ms = seg_rom PSEGS ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr (ms_regs ms) 17 = Z_to_bv 64 63 ->
  fd_lookup (m_fds model) (fd32 (getr (ms_regs ms) 10)) = Some (FdFile p off) -> fs_lookup (m_fs model) p = Some data ->
  getr (ms_regs ms) 11 = Z_to_bv 64 RS_LO -> getr (ms_regs ms) 12 = Z_to_bv 64 want -> 0 <= want <= 65536 ->
  havoc_ok L [] None = true ->
  (forall i R x, nth_error (s_rgs L) i = Some R -> in_rg E R x -> ~ (RS_LO <= bv_unsigned x < RS_LO + 65536)) ->
  (forall E' ms', agree (s_next L) E E' -> sden PSEGS E' (havoc_call L 0x60c30 KEEPALL [] None) ms' -> ms_rom ms' = seg_rom PSEGS ->
     ms_mem ms' = wbytes (ms_mem ms) (Z_to_bv 64 RS_LO) (file_read data off (Z_to_bv 64 want)) ->
     getr (ms_regs ms') 10 = len_word (file_read data off (Z_to_bv 64 want)) ->
     realizes PSEGS (mkCfg ms' (with_fds (fd_insert (m_fds model) (fd32 (getr (ms_regs ms) 10))
                                    (FdFile p (off + len_word (file_read data off (Z_to_bv 64 want))))) model)) T) ->
  realizes PSEGS (mkCfg ms model) T.
Proof.
  intros E L ms model p off data want T Hd Hpc Hrv Hrom Hh Hl H17 Hfd Hlk H11 H12 Hwant Hok Hrs Hk.
  set (bs := file_read data off (Z_to_bv 64 want)) in *.
  assert (Hcl : Z_to_bv 64 (rw_count_clamp (getr (ms_regs ms) 12)) = Z_to_bv 64 want).
  { rewrite H12. rewrite rw_count_clamp_small; rewrite u_small64 by (unfold two64; lia); [reflexivity|]. unfold MAX_RW_COUNT. lia. }
  assert (Hlen : Z.of_nat (length bs) <= want).
  { unfold bs. rewrite file_read_unguarded. rewrite length_firstn. unfold word_to_nat. rewrite u_small64 by (unfold two64; lia). lia. }
  pose proof (sden_mkst PSEGS E L ms Hd Hrv) as Hms.
  destruct (mk_tbl_ranges_ecall PSEGS RS_P 0x60c2c ltac:(rewrite <- TBL_P_eq; vm_compute; reflexivity)) as (w & Hw & Hec).
  rewrite Hms. rewrite Hpc, Hrom.
  apply (rzc_ecall PSEGS DCFG (ms_regs ms) _ (ms_mem ms) (seg_rom PSEGS) model w _ Hh Hl Hw Hec).
  apply (@rzc_read_file _ PSEGS DCFG (ms_regs ms) _ (ms_mem ms) model p off data _ Hh Hl H17 Hfd Hlk).
  - rewrite H11, H12. unfold RS_LO. apply access_okb_of_le; rewrite ?u_small64 by (unfold two64; lia); [lia|]. unfold TASK_SIZE. lia.
  - rewrite H11, Hcl. fold bs. unfold len_word. apply rs_rbm. lia.
  - rewrite Hcl, H11. fold bs.
    rewrite <- Hrom.
    replace (Z_to_bv 64 0x60c2c) with (Z_to_bv 64 (s_pc L)) by (rewrite Hpc; reflexivity).
    apply (fx_sys_ret_w E L ms _ (len_word bs) None (wbytes (ms_mem ms) (Z_to_bv 64 RS_LO) bs) _ Hd Hok
             ltac:(intros l Hc; discriminate Hc) ltac:(rewrite Hpc; lia) ltac:(rewrite Hpc; lia)).
    + intros i R x Hi Hin. apply wbytes_outside; [rewrite u_small64 by (unfold two64, RS_LO; lia); unfold RS_LO; lia|].
      pose proof (Hrs i R x Hi Hin) as Hx. rewrite u_small64 by (unfold two64, RS_LO; lia). lia.
    + apply wbytes_grows.
    + intros E' ms' Ha Hd' Hm' Hr' H10'. rewrite Hpc in Hd'. replace (0x60c2c + 4) with 0x60c30 in Hd' by reflexivity.
      apply (Hk E' ms' Ha Hd'); [rewrite Hr'; exact Hrom | exact Hm' | exact H10'].
Qed.

(* [comment removed for export] *)
Theorem fx_close : forall E L ms model (ent : FdEntry) T,
  sden PSEGS E L ms -> s_pc L = 0x60c2c -> s_resv L = RNone -> ms_rom ms = seg_rom PSEGS ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr (ms_regs ms) 17 = Z_to_bv 64 57 -> fd_lookup (m_fds model) (fd32 (getr (ms_regs ms) 10)) = Some ent ->
  havoc_ok L [] (Some (lconst 0)) = true ->
  (forall E' ms', agree (s_next L) E E' -> sden PSEGS E' (havoc_call L 0x60c30 KEEPALL [] (Some (lconst 0))) ms' ->
     ms_rom ms' = seg_rom PSEGS -> ms_mem ms' = ms_mem ms ->
     realizes PSEGS (mkCfg ms' (with_fds (fd_remove (m_fds model) (fd32 (getr (ms_regs ms) 10))) model)) T) ->
  realizes PSEGS (mkCfg ms model) T.
Proof.
  intros E L ms model ent T Hd Hpc Hrv Hrom Hh Hl H17 Hfd Hok Hk.
  pose proof (sden_mkst PSEGS E L ms Hd Hrv) as Hms.
  destruct (mk_tbl_ranges_ecall PSEGS RS_P 0x60c2c ltac:(rewrite <- TBL_P_eq; vm_compute; reflexivity)) as (w & Hw & Hec).
  rewrite Hms. rewrite Hpc, Hrom.
  apply (rzc_ecall PSEGS DCFG (ms_regs ms) _ (ms_mem ms) (seg_rom PSEGS) model w _ Hh Hl Hw Hec).
  apply (@rzc_close _ PSEGS DCFG (ms_regs ms) _ (ms_mem ms) model ent _ Hh Hl H17 Hfd).
  rewrite <- Hrom. replace (Z_to_bv 64 0x60c2c) with (Z_to_bv 64 (s_pc L)) by (rewrite Hpc; reflexivity).
  apply (fx_sys_ret_w E L ms _ (Z_to_bv 64 0) (Some (lconst 0)) (ms_mem ms) _ Hd Hok
           ltac:(intros l Hc; injection Hc as <-; apply lden_lconst) ltac:(rewrite Hpc; lia) ltac:(rewrite Hpc; lia)).
  - intros i R x _ _. reflexivity.
  - intros x Hx. exact Hx.
  - intros E' ms' Ha Hd' Hm' Hr' _. rewrite Hpc in Hd'. replace (0x60c2c + 4) with 0x60c30 in Hd' by reflexivity.
    apply (Hk E' ms' Ha Hd'); [rewrite Hr'; exact Hrom | exact Hm'].
Qed.

(* [comment removed for export] *)
Theorem fx_ioctl : forall E L ms model (ch : word) T,
  sden PSEGS E L ms -> s_pc L = 0x55ffc -> s_resv L = RNone -> ms_rom ms = seg_rom PSEGS ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr (ms_regs ms) 17 = Z_to_bv 64 29 -> fd_lookup (m_fds model) (fd32 (getr (ms_regs ms) 10)) = Some (FdChannel ch) ->
  tty_only_request (cmd32 (getr (ms_regs ms) 11)) = true ->
  havoc_ok L [] (Some (lconst 18446744073709551591)) = true ->
  (forall E' ms', agree (s_next L) E E' -> sden PSEGS E' (havoc_call L 0x56000 KEEPALL [] (Some (lconst 18446744073709551591))) ms' ->
     ms_rom ms' = seg_rom PSEGS -> ms_mem ms' = ms_mem ms -> realizes PSEGS (mkCfg ms' model) T) ->
  realizes PSEGS (mkCfg ms model) T.
Proof.
  intros E L ms model ch T Hd Hpc Hrv Hrom Hh Hl H17 Hfd Htty Hok Hk.
  pose proof (sden_mkst PSEGS E L ms Hd Hrv) as Hms.
  destruct (mk_tbl_ranges_ecall PSEGS RS_P 0x55ffc ltac:(rewrite <- TBL_P_eq; vm_compute; reflexivity)) as (w & Hw & Hec).
  rewrite Hms. rewrite Hpc, Hrom.
  apply (rzc_ecall PSEGS DCFG (ms_regs ms) _ (ms_mem ms) (seg_rom PSEGS) model w _ Hh Hl Hw Hec).
  apply (@rzc_ioctl_notty _ PSEGS DCFG (ms_regs ms) _ (ms_mem ms) model ch _ Hh Hl H17 Hfd Htty).
  rewrite <- Hrom. replace (Z_to_bv 64 0x55ffc) with (Z_to_bv 64 (s_pc L)) by (rewrite Hpc; reflexivity).
  apply (fx_sys_ret_w E L ms _ (errno_ret ENOTTY) (Some (lconst 18446744073709551591)) (ms_mem ms) _ Hd Hok
           ltac:(intros l Hc; injection Hc as <-; rewrite lden_lconst; apply bv_eq; reflexivity) ltac:(rewrite Hpc; lia) ltac:(rewrite Hpc; lia)).
  - intros i R x _ _. reflexivity.
  - intros x Hx. exact Hx.
  - intros E' ms' Ha Hd' Hm' Hr' _. rewrite Hpc in Hd'. replace (0x55ffc + 4) with 0x56000 in Hd' by reflexivity.
    apply (Hk E' ms' Ha Hd'); [rewrite Hr'; exact Hrom | exact Hm'].
Qed.
