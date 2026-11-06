(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Import EdAlloc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QWxq_c1 QsRG QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude.

Import QsRG.Mq0 QSpR.Mq1.
Import ListNotations.
Open Scope Z_scope.

Section Bridge.
Variable segs : list Segment.

#[using="Type"] Lemma rdn_same : forall m a n, QsjA.rdn segs m a n = QsRG.Mq0.rdn segs m a n.
Proof. reflexivity. Qed.
#[using="Type"] Lemma seg_rom_same : QsjA.seg_rom segs = QsRG.Mq0.seg_rom segs.
Proof. reflexivity. Qed.

#[using="Type"] Lemma MS_mkst : forall R F pc fc m ro,
QEpW.MS R F pc fc None m ro = @QsRG.Mq0.mkst F fc R pc m ro.
Proof. reflexivity. Qed.
#[using="Type"] Lemma MS_MSdefs : forall R F pc fc rv m ro,
QEpW.MS R F pc fc rv m ro = QSpR.Mq1.MS R F pc fc rv m ro.
Proof. reflexivity. Qed.

#[using="Type"] Lemma bytes_at_rdn0 : forall m a bs,
QZDE.bytes_at segs m a bs -> QsRG.Mq0.rdn segs m (Z_to_bv 64 a) (length bs) = Some bs.
Proof.
intros m a bs H. rewrite <- rdn_same.
pose proof (QZDE.bytes_at_rdn segs m a bs 0 (length bs) H ltac:(lia)) as R.
rewrite Z.add_0_r in R. unfold QZDE.wa in R. rewrite R. rewrite firstn_all. reflexivity.
Qed.

#[using="Type"] Lemma rdn_mrd : forall m a n bs i,
QsRG.Mq0.rdn segs m a n = Some bs -> (i < n)%nat ->
(bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
QZDE.mrd segs m (Z_to_bv 64 (bv_unsigned a + Z.of_nat i)) = nth_error bs i.
Proof.
intros m a n. revert a. induction n as [|n IH]; intros a bs i H Hi Hnw; [lia|].
cbn [QsRG.Mq0.rdn] in H. unfold QZDE.mrd.
destruct (match m a with Some b => Some b | None => QsRG.Mq0.seg_rom segs a end) as [b|] eqn:Hb; [|discriminate].
destruct (QsRG.Mq0.rdn segs m (a + 1)%bv n) as [rest|] eqn:Hr; [|discriminate].
injection H as <-.
destruct i as [|i].
- rewrite Z.add_0_r, Z_to_bv_bv_unsigned. cbn [nth_error].
change (QsjA.seg_rom segs) with (QsRG.Mq0.seg_rom segs).
destruct (m a); [congruence|]. exact Hb.
- cbn [nth_error].
assert (Hu : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply QsRG.Mq0.u_add1; lia).
replace (bv_unsigned a + Z.of_nat (S i)) with (bv_unsigned (a + 1)%bv + Z.of_nat i) by lia.
apply (IH (a + 1)%bv rest i Hr ltac:(lia)). lia.
Qed.

#[using="Type"] Lemma rdn_bytes_at : forall m a bs,
0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
QsRG.Mq0.rdn segs m (Z_to_bv 64 a) (length bs) = Some bs -> QZDE.bytes_at segs m a bs.
Proof.
intros m a bs Ha Hnw H. split; [exact Ha|]. split; [exact Hnw|].
intros i Hi. unfold QZDE.wa.
pose proof (rdn_mrd m (Z_to_bv 64 a) (length bs) bs i H Hi) as R.
rewrite Z_to_bv_small in R by (unfold bv_modulus; lia).
apply R. lia.
Qed.

#[using="Type"] Lemma wr_at_store_ok : forall m a n,
QZDE.wr_at segs m a (Z.of_nat n) -> store_ok segs m (Z_to_bv 64 a) n = true.
Proof.
intros m a n H.
pose proof (QZDE.wr_at_store_ok segs m a (Z.of_nat n) 0 n H ltac:(lia) ltac:(lia)) as W.
unfold QZDE.wa in W. rewrite Z.add_0_r in W. exact W.
Qed.

End Bridge.
End Mq0.
From Stdlib Require NArith Bool FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Instr Decode DecodeC.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJyS QwNp Qnhz Qpox QsV0 Qrxj QSjk Qn1e QiVh QRjH QBxa Q9ox QMz4 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QJyS QwNp Qnhz.Mq1 Qpox QsV0 QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QSjk Qn1e.Mq1 QiVh Qn1e QRjH QBxa.Mq4 QRjH.Mq3 QBxa.Mq0 Q9ox.Mq0 QSpR.Mq2 QMz4 QSpR.Mq0 QSpR.Mq1.
Import ListNotations.
Open Scope bv_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section WithSegs.

#[using="Type"] Lemma mmap_outcome_si (segs : list Segment) : forall ms x8 model o,
bv_unsigned x8 = 222%Z ->
mmap_args_ok ms ->
syscall_spec (sys_input segs ms x8) model o <->
(exists e, In e mmap_errnos /\ o = Ok (mkEffect (errno_ret e) [] []) model [])
\/ (exists a, grant_ok (ms_gpr ms 0) model a (page_round_up_Z (bv_unsigned (ms_gpr ms 1))) = true
/\ o = Ok (mkEffect a [] [(a, page_round_up (ms_gpr ms 1))])
(mmap_model a (page_round_up (ms_gpr ms 1)) model) []).
Proof.
intros ms x8 model o Hno Ha.
destruct (mmap_args_ok_gates ms Ha) as (Hoff & Hanon & Hl & Hmb).
destruct Ha as (_ & _ & Hflags & _ & _).
rewrite (syscall_spec_222 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
rewrite in_arg0_si, in_arg1_si, in_arg2_si,
in_arg3_sys_input, in_arg4_sys_input, in_arg5_sys_input.
rewrite (mmap_rw_outcome _ _ _ _ _ _ _ model o Hoff Hanon Hl Hmb). unfold mmap_err_out.
rewrite Hflags.
assert (Hnr : mmap_noreserve_b (Z_to_bv 64 34) = false) by (vm_compute; reflexivity).
unfold mmap_noreserve_backed_ok, with_mmap_backing. rewrite Hnr.
unfold grant_ok, mmap_model, page_round_up.
split; (intros [H | (a & Hg & ->)]; [left; exact H | right; exists a; split; [|reflexivity]]).
- destruct Hg as (H1 & H2 & H3 & H4 & H5).
rewrite (proj2 (Z.eqb_eq _ _) H1), (proj2 (Z.ltb_lt _ _) H2), (proj2 (Z.leb_le _ _) H3), H4, H5.
reflexivity.
- rewrite !andb_true_iff in Hg. destruct Hg as [[[[H1 H2] H3] H4] H5].
apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. auto 10.
Qed.

#[using="Type"] Lemma munmap_outcome_si (segs : list Segment) : forall ms x8 model o,
bv_unsigned x8 = 215%Z ->
munmap_args_ok ms model ->
syscall_spec (sys_input segs ms x8) model o <->
o = Ok (munmap_eff ms)
(munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model) [].
Proof.
intros ms x8 model o Hno (Hal & Hlen & Hnw & Hhas).
rewrite (syscall_spec_215 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
rewrite in_arg0_si, in_arg1_si.
unfold munmap_eff, munmap_model, page_round_up.
apply munmap_exact_outcome; [exact Hal | unfold w_is0; apply bv_eqb_neq; exact Hlen | exact Hnw |].
unfold page_round_up in Hhas. exact Hhas.
Qed.

Variable segs : list Segment.

#[local] Abbreviation NClosed := (QRjH.NClosed segs).

#[using="Type"] Lemma ncl_step : forall (J : config -> Prop) ms model ms',
NClosed J ->
m_halted model = None -> m_vm_lazy model = [] ->
ms_svc_pending ms = None ->
RiscvSemantics.step segs ms = MachineOk ms' ->
J (mkCfg ms' model) -> J (mkCfg ms model).
Proof.
intros J ms model ms' HJ Hh Hlazy Hsvc Hstep Hc.
eapply (nclosed_silent1 segs J); [exact HJ | apply node_instr; eassumption | exact Hc].
Qed.

#[using="Type"] Lemma ncl_msteps : forall (J : config -> Prop) ms ms' model,
NClosed J ->
m_halted model = None -> m_vm_lazy model = [] ->
msteps segs ms ms' ->
J (mkCfg ms' model) -> J (mkCfg ms model).
Proof.
intros J ms ms' model HJ Hh Hlazy Hms;
induction Hms as [ms | ms ms1 ms2 Hsvc Hstep Hms IH]; intro Hc; [exact Hc|].
eapply ncl_step; [exact HJ | exact Hh | exact Hlazy | exact Hsvc | exact Hstep | apply IH; exact Hc].
Qed.

#[using="Type"] Lemma ncl_ecall : forall (J : config -> Prop) R F pc fc rv m ro model w,
NClosed J ->
m_halted model = None -> m_vm_lazy model = [] ->
fetch_word segs pc = Some w -> is_ecall w = true ->
J (mkCfg (MSsvc R F pc (getr R 17) fc rv m ro) model) ->
J (mkCfg (MS R F pc fc rv m ro) model).
Proof.
intros J R F pc fc rv m ro model w HJ Hh Hlazy HF HE Hc.
eapply ncl_step; [exact HJ | exact Hh | exact Hlazy | reflexivity | eapply step_ecall_MS; eassumption | exact Hc].
Qed.

#[using="Type"] Lemma ncl_det : forall (J : config -> Prop) ms model x8 eff0 m0,
NClosed J ->
m_halted model = None -> ms_svc_pending ms = Some x8 ->
(forall o, syscall_spec (sys_input segs ms x8) model o <-> o = Ok eff0 m0 []) ->
m_halted m0 = None -> m_vm_lazy m0 = [] ->
J (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) ->
J (mkCfg ms model).
Proof.
intros J ms model x8 eff0 m0 HJ Hh Hsvc Hchk Hh0 Hlazy0 Hc.
eapply (nclosed_silent1 segs J); [exact HJ | eapply node_det; eassumption | exact Hc].
Qed.

#[using="Type"] Lemma ncl_family : forall (J : config -> Prop) ms model x8 (I : Type)
(effs : I -> SyscallEffect) (ms' : I -> Model) (i0 : I),
NClosed J ->
m_halted model = None -> ms_svc_pending ms = Some x8 ->
(forall o, syscall_spec (sys_input segs ms x8) model o <-> exists i, o = Ok (effs i) (ms' i) []) ->
(forall i, m_halted (ms' i) = None) ->
(forall i, m_vm_lazy (ms' i) = []) ->
(forall i, J (mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i))) ->
J (mkCfg ms model).
Proof.
intros J ms model x8 I effs ms' i0 HJ Hh Hsvc Hchk Hh' Hlazy' Hc.
assert (Hj : exists j, ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model (effs j)).
{ destruct (Classical_Prop.classic (exists j, refusal_b (sys_input segs ms x8) model (eff_ret (effs j)) = false))
as [(j & Hr)|Hn].
- exists j. exact (spurious_refusal_not_refusal _ _ _ _ Hr).
- exists i0. intros (_ & _ & (eff' & m' & evs' & Hs & Hr')).
apply Hchk in Hs as (j & Hs). apply Ok_inj in Hs as (-> & _ & _). apply Hn. exists j. exact Hr'. }
destruct Hj as (j & Hj).
apply (HJ _ _ _ (exist _ j Hj) (node_family_ns segs ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hchk Hh' Hlazy')).
intros [i Hi]. apply Hc.
Qed.

#[using="Type"] Lemma node_of_family : forall ms model x8 (I : Type)
(effs : I -> SyscallEffect) (ms' : I -> Model),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
(forall o, syscall_spec (sys_input segs ms x8) model o <-> exists i, o = Ok (effs i) (ms' i) []) ->
(forall i, m_halted (ms' i) = None) ->
(forall i, m_vm_lazy (ms' i) = []) ->
(forall i, ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model (effs i)) ->
node_ok segs (mkCfg ms model) I (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' Hh Hsvc Hchk Hh' Hlazy' Hns.
apply (node_family segs ms model x8 I effs ms' (fun _ => []) _ Hh Hsvc Hchk).
- intros i. exists i. reflexivity.
- intros o (i & ->). exists i. reflexivity.
- exact Hh'.
- exact Hlazy'.
- exact Hns.
Qed.

#[using="Type"] Lemma node_ok_ext : forall c (I : Type) (evs : I -> list event) (nx nx' : I -> config),
(forall i, nx i = nx' i) -> node_ok segs c I evs nx -> node_ok segs c I evs nx'.
Proof.
intros c I evs nx nx' E [H1 H2]. split.
- intros i. rewrite <- E. apply H1.
- intros e st Hss. destruct (H2 e st Hss) as (i & -> & ->). exists i. rewrite E. split; reflexivity.
Qed.

Section MSNodes.
Variables (R F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
(m : word -> option byte) (model : Model) (w : bv 32).
Hypothesis HF : fetch_word segs pc = Some w.
Hypothesis HE : is_ecall w = true.
Hypothesis Hh : m_halted model = None.
Hypothesis Hlazy : m_vm_lazy model = [].

Let pre : machine_state := MS R F pc fc rv m (seg_rom segs).
Let ms : machine_state := MSsvc R F pc (getr R 17) fc rv m (seg_rom segs).
Let post (r : word) : machine_state := MS (regupd R 10 r) F (v_addi pc 4) fc rv m (seg_rom segs).
Let postm (r : word) (m' : word -> option byte) : machine_state :=
MS (regupd R 10 r) F (v_addi pc 4) fc rv m' (seg_rom segs).

#[using="Type"] Lemma sysno_lit : forall z, getr R 17 = Z_to_bv 64 z -> (0 <= z < 2 ^ 64)%Z ->
bv_unsigned (in_sysno (sys_input segs ms (getr R 17))) = z.
Proof. intros z H Hz. rewrite in_sysno_si, H. apply u64_lit. exact Hz. Qed.

#[using="Type"] Lemma not_alloc_lit : forall z, getr R 17 = Z_to_bv 64 z ->
((0 <=? z) && (z <? 2 ^ 64))%Z = true -> existsb (Z.eqb z) alloc_mark_sysnos = false ->
~ In (bv_unsigned (getr R 17)) alloc_mark_sysnos.
Proof.
intros z H Hz Hn. apply andb_true_iff in Hz as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2.
rewrite H, u64_lit by (split; assumption). intros Hin.
rewrite <- not_true_iff_false, existsb_exists in Hn. apply Hn. exists z. split; [exact Hin | apply Z.eqb_refl].
Qed.

#[using="Type"] Lemma not_spurious_lit : forall z eff, getr R 17 = Z_to_bv 64 z ->
((0 <=? z) && (z <? 2 ^ 64))%Z = true -> existsb (Z.eqb z) alloc_mark_sysnos = false ->
~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms (getr R 17)) model eff.
Proof.
intros z eff H Hz Hn. apply not_spurious_sysno. rewrite in_sysno_si. exact (not_alloc_lit z H Hz Hn).
Qed.

#[using="w HF HE Hh Hlazy ms"] Lemma ncl_close : forall (J : config -> Prop) fd e,
NClosed J ->
getr R 17 = Z_to_bv 64 57 ->
getr R 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
fd_lookup (m_fds model) fd = Some e ->
J (mkCfg (post (Z_to_bv 64 0)) (with_fds (fd_remove (m_fds model) fd) model)) ->
J (mkCfg pre model).
Proof.
intros J fd e HJ H17 Hfd Hfd32 Hlk Hc.
eapply ncl_ecall; [exact HJ | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
eapply (ncl_det J ms model _ (mkEffect (Z_to_bv 64 0) [] []) (with_fds (fd_remove (m_fds model) fd) model));
[exact HJ | exact Hh | reflexivity | | rewrite with_fds_halted'; exact Hh | rewrite with_fds_lazy; exact Hlazy |].
- intros o. rewrite (syscall_spec_57 _ model o) by (apply (sysno_lit 57 H17); lia).
rewrite in_arg0_si. unfold ms. rewrite ms_gpr_MSsvc0, Hfd, (fd32_id fd Hfd32).
exact (close_outcome fd _ model e o Hlk).
- unfold ms. rewrite adv_MSsvc. exact Hc.
Qed.

#[using="w HF HE Hh Hlazy ms"] Lemma ncl_ioctl_winsz : forall (J : config -> Prop) fd c,
NClosed J ->
getr R 17 = Z_to_bv 64 29 ->
getr R 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
fd_lookup (m_fds model) fd = Some (FdChannel c) ->
getr R 11 = Z_to_bv 64 0x5413 ->
J (mkCfg (post (errno_ret ENOTTY)) model) ->
J (mkCfg pre model).
Proof.
intros J fd c HJ H17 Hfd Hfd32 Hlk H11 Hc.
eapply ncl_ecall; [exact HJ | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
eapply (ncl_det J ms model _ (mkEffect (errno_ret ENOTTY) [] []) model);
[exact HJ | exact Hh | reflexivity | | exact Hh | exact Hlazy |].
- intros o. rewrite (syscall_spec_29 _ model o) by (apply (sysno_lit 29 H17); lia).
rewrite in_arg0_si, in_arg1_si. unfold ms. rewrite ms_gpr_MSsvc0, ms_gpr_MSsvc1, Hfd, (fd32_id fd Hfd32), H11.
apply (ioctl_tty_outcome_chan fd _ _ model c o Hlk). reflexivity.
- unfold ms. rewrite adv_MSsvc. exact Hc.
Qed.

#[using="w HF HE Hh Hlazy ms"] Lemma ncl_read_dir : forall (J : config -> Prop) fd (cnt : Z),
NClosed J ->
getr R 17 = Z_to_bv 64 63 ->
getr R 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
fd_lookup (m_fds model) fd = Some FdDir ->
getr R 12 = Z_to_bv 64 cnt ->
(1 <= cnt)%Z -> (cnt <= 2 ^ 24)%Z ->
(bv_unsigned (getr R 11) + cnt <= task_size_max)%Z ->
store_ok segs m (getr R 11) (Z.to_nat cnt) = true ->
J (mkCfg (post (errno_ret EISDIR)) model) ->
J (mkCfg pre model).
Proof.
intros J fd cnt HJ H17 Hfd Hfd32 Hlk H12 Hc1 H24 Hover Hok Hc.
eapply ncl_ecall; [exact HJ | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
eapply (ncl_det J ms model _ (mkEffect (errno_ret EISDIR) [] []) model);
[exact HJ | exact Hh | reflexivity | | exact Hh | exact Hlazy |].
- intros o. rewrite (syscall_spec_63 _ model o) by (apply (sysno_lit 63 H17); lia).
rewrite in_arg0_si, in_arg1_si, in_arg2_si. unfold ms.
rewrite ms_gpr_MSsvc0, ms_gpr_MSsvc1, ms_gpr_MSsvc2, Hfd, (fd32_id fd Hfd32).
apply (read_dir_outcome fd _ _ _ model o Hlk).
destruct (read_bytes_map_of_store_ok segs m (getr R 11) (Z.to_nat cnt) Hok ltac:(lia)) as [wv Hw].
rewrite Z2Nat.id in Hw by lia.
apply access_okb_of_bound. rewrite <- task_size_max_eq, H12, u64_lit by lia. exact Hover.
- unfold ms. rewrite adv_MSsvc. exact Hc.
Qed.

#[using="w HF HE Hh Hlazy ms"] Lemma ncl_read_file : forall (J : config -> Prop) fd p off data (cnt : Z),
NClosed J ->
getr R 17 = Z_to_bv 64 63 ->
getr R 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
fd_lookup (m_fds model) fd = Some (FdFile p off) ->
fs_lookup (m_fs model) p = Some data ->
getr R 12 = Z_to_bv 64 cnt ->
(1 <= cnt)%Z -> (cnt <= access_ok_walk_max)%Z -> (cnt < 2 ^ 64)%Z ->
(bv_unsigned (getr R 11) + cnt <= task_size_max)%Z ->
store_ok segs m (getr R 11) (Z.to_nat cnt) = true ->
let bs := file_read data off (getr R 12) in
J (mkCfg (postm (len_word bs) (wbytes m (getr R 11) bs))
(with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model)) ->
J (mkCfg pre model).
Proof.
intros J fd p off data cnt HJ H17 Hfd Hfd32 Hlk Hfs H12 Hc1 Hmax H64 Hover Hok bs Hc.
assert (Hno : bv_unsigned (getr R 17) = 63%Z) by (rewrite H17; apply u64_lit; lia).
eapply ncl_ecall; [exact HJ | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
destruct (read_bytes_map_of_store_ok segs m (getr R 11) (Z.to_nat cnt) Hok ltac:(lia)) as [wv Hw].
rewrite Z2Nat.id in Hw by lia.
assert (Hu2 : bv_unsigned (ms_gpr ms 2) = cnt).
{ unfold ms. rewrite ms_gpr_MSsvc2, H12. apply u64_lit. lia. }
pose proof (read_file_outcome_si segs ms (getr R 17) model fd p off data wv Hno
ltac:(unfold ms; rewrite ms_gpr_MSsvc0; exact Hfd) Hfd32 Hlk Hfs
ltac:(unfold ms; rewrite ms_writable_byte_MSsvc, ms_gpr_MSsvc1, ms_gpr_MSsvc2, H12; exact Hw)
ltac:(rewrite Hu2; lia) ltac:(rewrite Hu2; exact Hmax)
ltac:(rewrite Hu2; unfold ms; rewrite ms_gpr_MSsvc1; exact Hover)) as Hchk.
unfold ms in Hchk. rewrite ms_gpr_MSsvc1, ms_gpr_MSsvc2 in Hchk. fold ms in Hchk.
subst bs. revert Hc Hchk.
generalize (file_read data off (getr R 12)) as bs. intros bs Hc Hchk.
eapply (ncl_det J ms model _ (mkEffect (len_word bs) (delivered_writes (getr R 11) bs) [])
(with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model));
[exact HJ | exact Hh | reflexivity | exact Hchk
| rewrite with_fds_halted'; exact Hh | rewrite with_fds_lazy; exact Hlazy | ].
unfold ms. rewrite adv_delivered_MSsvc. exact Hc.
Qed.

Definition path_at_MS (a : word) (p : list byte) : Prop :=
(length p <= 4095)%nat /\ ~ In (Z_to_bv 8 0) p
/\ rdn segs m a (length p + 1) = Some (p ++ [Z_to_bv 8 0]).

#[using="Type"] Lemma path_at_MS_cstr : forall a p, path_at_MS a p -> read_cstr (mrb segs m) a = CstrOk p.
Proof. intros a p (H1 & H2 & H3). apply read_cstr_of_rdn; assumption. Qed.

Section Openat.
Hypothesis H17 : getr R 17 = Z_to_bv 64 56.
Hypothesis H10 : getr R 10 = AT_FDCWD.
Hypothesis Hfl : Z.ldiff (bv_unsigned (getr R 12)) open_ignored_flags = 0%Z.
Let fds := m_fds model.

#[using="H17 H10"] Lemma openat_spec_head_MS : forall o,
syscall_spec (sys_input segs ms (getr R 17)) model o <->
openat_spec AT_FDCWD32 (getr R 11) (getr R 12) (sys_input segs ms (getr R 17)) model o.
Proof.
intros o. rewrite (syscall_spec_56 _ model o) by (apply (sysno_lit 56 H17); lia).
rewrite in_arg0_si, in_arg1_si, in_arg2_si. unfold ms. rewrite ms_gpr_MSsvc0, ms_gpr_MSsvc1, ms_gpr_MSsvc2, H10.
reflexivity.
Qed.

#[using="Type"] Lemma open_in_mem_MS : in_mem (sys_input segs ms (getr R 17)) = mrb segs m.
Proof. unfold ms. rewrite in_mem_si, ms_read_byte_MSsvc. reflexivity. Qed.

#[using="w HF HE Hh Hlazy ms H17 H10 Hfl"] Lemma ncl_openat_toolong : forall (J : config -> Prop) bs,
NClosed J ->
rdn segs m (getr R 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
J (mkCfg (post (errno_ret ENAMETOOLONG)) model) ->
J (mkCfg pre model).
Proof.
intros J bs HJ Hrd Hnz Hc.
pose proof (read_cstr_toolong_of_rdn segs m (getr R 11) bs (rdn_length _ _ _ _ _ Hrd) Hnz Hrd) as Hp.
eapply ncl_ecall; [exact HJ | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
eapply (ncl_det J ms model _ _ model); [exact HJ | exact Hh | reflexivity | | exact Hh | exact Hlazy |].
- intros o. rewrite openat_spec_head_MS.
apply (openat_toolong_outcome _ _ _ _ model (modeled_open_flags_rd _ Hfl)). rewrite open_in_mem_MS. exact Hp.
- unfold ms. rewrite adv_copyins_ret_MSsvc. exact Hc.
Qed.

#[using="w HF HE Hh Hlazy ms H17 H10 Hfl"] Lemma ncl_openat_empty : forall (J : config -> Prop),
NClosed J ->
path_at_MS (getr R 11) [] ->
J (mkCfg (post (errno_ret ENOENT)) model) ->
J (mkCfg pre model).
Proof.
intros J HJ Hp Hc.
eapply ncl_ecall; [exact HJ | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
eapply (ncl_det J ms model _ _ model); [exact HJ | exact Hh | reflexivity | | exact Hh | exact Hlazy |].
- intros o. rewrite openat_spec_head_MS.
apply (openat_empty_outcome _ _ _ _ model (modeled_open_flags_rd _ Hfl)). rewrite open_in_mem_MS.
exact (path_at_MS_cstr _ [] Hp).
- unfold ms. rewrite adv_copyins_ret_MSsvc. exact Hc.
Qed.

#[using="w HF HE Hh Hlazy ms H17 H10 Hfl"] Lemma ncl_openat_absent : forall (J : config -> Prop) p,
NClosed J ->
path_at_MS (getr R 11) p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
fs_lookup (m_fs model) p = None ->
J (mkCfg (post (errno_ret ENOENT)) model) ->
J (mkCfg pre model).
Proof.
intros J p HJ Hp Hne Hsl Hnd Hfs Hc.
eapply ncl_ecall; [exact HJ | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
eapply (ncl_det J ms model _ _ model); [exact HJ | exact Hh | reflexivity | | exact Hh | exact Hlazy |].
- intros o. rewrite openat_spec_head_MS.
apply (openat_absent_outcome _ _ _ _ model (modeled_open_flags_rd _ Hfl) eq_refl Hfl p);
[rewrite open_in_mem_MS; exact (path_at_MS_cstr _ p Hp) | exact Hne | exact Hsl | exact Hnd | exact Hfs].
- unfold ms. rewrite adv_copyins_ret_MSsvc. exact Hc.
Qed.

Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

#[using="Hh Hlazy Hfree"] Lemma ncl_open_out : forall (J : config -> Prop) reads (mk : word -> Model),
NClosed J ->
(forall o, syscall_spec (sys_input segs ms (getr R 17)) model o <-> open_out reads model mk o) ->
(forall fd, m_halted (mk fd) = None) -> (forall fd, m_vm_lazy (mk fd) = []) ->
(forall e, In e openat_errnos -> J (mkCfg (post (errno_ret e)) model)) ->
J (mkCfg (post (alloc_fd fds)) (mk (alloc_fd fds))) ->
J (mkCfg ms model).
Proof.
intros J reads mk HJ Hchk Hmk Hmklazy HA HB.
pose (effs := fun i : open_I model => match i with
| inl (exist _ e _) => with_copyins reads (mkEffect (errno_ret e) [] [])
| inr _ => with_copyins reads (mkEffect (alloc_fd fds) [] []) end).
pose (ms' := fun i : open_I model => match i with inl _ => model | inr _ => mk (alloc_fd fds) end).
apply (ncl_family J ms model (getr R 17) (open_I model) effs ms' (inr tt) HJ Hh eq_refl).
- intros o. rewrite Hchk. unfold open_out. split.
+ intros [(e & He & ->) | (_ & ->)]; [exists (inl (exist _ e He)) | exists (inr tt)]; reflexivity.
+ intros ([[e He]|[]] & ->); [left; exists e; auto | right; split; [exact Hfree | reflexivity]].
- intros [[e He]|[]]; [exact Hh | apply Hmk].
- intros [[e He]|[]]; [exact Hlazy | apply Hmklazy].
- intros [[e He]|[]]; cbn [effs ms']; unfold ms; rewrite adv_copyins_ret_MSsvc; [apply HA; exact He | exact HB].
Qed.

#[using="w HF HE Hh Hlazy ms H17 H10 Hfl Hfree"] Lemma ncl_openat_dot : forall (J : config -> Prop),
NClosed J ->
path_at_MS (getr R 11) dot_path ->
(forall e, In e openat_errnos -> J (mkCfg (post (errno_ret e)) model)) ->
J (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) ->
J (mkCfg pre model).
Proof.
intros J HJ Hp HA HB.
eapply ncl_ecall; [exact HJ | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
apply (ncl_open_out J (open_reads (sys_input segs ms (getr R 17)) (getr R 11))
(fun fd => with_fds (fd_insert fds fd FdDir) model) HJ).
- intros o. rewrite openat_spec_head_MS.
apply (openat_dot_outcome _ _ _ _ model (modeled_open_flags_rd _ Hfl) eq_refl Hfl).
rewrite open_in_mem_MS. exact (path_at_MS_cstr _ _ Hp).
- intros fd. rewrite with_fds_halted'. exact Hh.
- intros fd. rewrite with_fds_lazy. exact Hlazy.
- exact HA.
- exact HB.
Qed.

#[using="w HF HE Hh Hlazy ms H17 H10 Hfl Hfree"] Lemma ncl_openat_file : forall (J : config -> Prop) p d,
NClosed J ->
path_at_MS (getr R 11) p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
fs_lookup (m_fs model) p = Some d ->
(forall e, In e openat_errnos -> J (mkCfg (post (errno_ret e)) model)) ->
J (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) model)) ->
J (mkCfg pre model).
Proof.
intros J p d HJ Hp Hne Hsl Hnd Hfs HA HB.
eapply ncl_ecall; [exact HJ | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
apply (ncl_open_out J (open_reads (sys_input segs ms (getr R 17)) (getr R 11))
(fun fd => with_fds (fd_insert fds fd (FdFile p (Z_to_bv 64 0))) model) HJ).
- intros o. rewrite openat_spec_head_MS.
apply (openat_file_outcome _ _ _ _ model (modeled_open_flags_rd _ Hfl) eq_refl Hfl p d);
[rewrite open_in_mem_MS; exact (path_at_MS_cstr _ p Hp) | exact Hne | exact Hsl | exact Hnd | exact Hfs].
- intros fd. rewrite with_fds_halted'. exact Hh.
- intros fd. rewrite with_fds_lazy. exact Hlazy.
- exact HA.
- exact HB.
Qed.
End Openat.

#[using="w HF HE Hh Hlazy ms"] Lemma ncl_set_tid : forall (J : config -> Prop),
NClosed J ->
getr R 17 = Z_to_bv 64 96 ->
m_tid model = None ->
(forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
J (mkCfg (post tid) (with_tid tid model))) ->
J (mkCfg pre model).
Proof.
intros J HJ H17 Htid Hk.
eapply ncl_ecall; [exact HJ | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
apply (HJ _ tid_I _ (exist _ (Z_to_bv 64 1) (one_tid_ok))
(node_set_tid segs ms model (getr R 17) Hh Hlazy eq_refl ltac:(apply (sysno_lit 96 H17); lia) Htid)).
intros [t Ht]. cbn [proj1_sig]. unfold ms. rewrite adv_set_MSsvc. apply Hk. exact Ht.
Qed.

#[using="w HF HE Hh Hlazy ms"] Lemma rz_exit_MS : forall code,
(getr R 17 = Z_to_bv 64 94 \/ getr R 17 = Z_to_bv 64 93) ->
getr R 10 = code ->
realizes segs (mkCfg pre model) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros code H17 H10.
eapply ncl_ecall; [apply nclosed_realizes | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
rewrite <- H10. unfold ms. rewrite <- (ms_gpr_MSsvc0 R F pc (getr R 17) fc rv m (seg_rom segs)).
eapply rz_exit; [exact Hh | reflexivity |].
destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

#[using="w HF HE Hh Hlazy ms"] Lemma rz_exit_MS_lit : forall (code : Z),
(getr R 17 = Z_to_bv 64 94 \/ getr R 17 = Z_to_bv 64 93) ->
getr R 10 = Z_to_bv 64 code -> (0 <= code < 256)%Z ->
realizes segs (mkCfg pre model) (t_exit (Z_to_bv 64 code) (m_fs model)).
Proof.
intros code H17 H10 Hc. rewrite <- (bv_and_255_small code Hc). apply rz_exit_MS; assumption.
Qed.

Section OpenatRz.
Hypothesis H17 : getr R 17 = Z_to_bv 64 56.
Hypothesis H10 : getr R 10 = AT_FDCWD.
Hypothesis Hfl : Z.ldiff (bv_unsigned (getr R 12)) open_ignored_flags = 0%Z.
Let fds := m_fds model.
Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

Definition open_nx_MS (mk : word -> Model) (i : open_I model) : config :=
match i with
| inl (exist _ e _) => mkCfg (post (errno_ret e)) model
| inr _ => mkCfg (post (alloc_fd fds)) (mk (alloc_fd fds))
end.

#[using="Hh Hlazy Hfree"] Lemma node_open_MS : forall reads (mk : word -> Model),
~ In (bv_unsigned (getr R 17)) alloc_mark_sysnos ->
(forall o, syscall_spec (sys_input segs ms (getr R 17)) model o <-> open_out reads model mk o) ->
(forall fd, m_halted (mk fd) = None) -> (forall fd, m_vm_lazy (mk fd) = []) ->
node_ok segs (mkCfg ms model) (open_I model) (fun _ => []) (open_nx_MS mk).
Proof.
intros reads mk Hna Hchk Hmk Hmklazy.
eapply node_ok_ext; [| eapply (node_open segs ms model (getr R 17) reads mk Hh Hlazy eq_refl Hna Hchk Hmk Hmklazy Hfree)].
intros [[e He]|[]]; cbn [open_nx open_nx_MS]; unfold ms; rewrite adv_set_MSsvc; reflexivity.
Qed.

#[using="w HF HE Hh Hlazy ms H17 H10 Hfl Hfree"] Lemma rz_openat_dot_MS : forall KA KB,
path_at_MS (getr R 11) dot_path ->
(forall e, In e openat_errnos -> realizes segs (mkCfg (post (errno_ret e)) model) KA) ->
realizes segs (mkCfg (post (alloc_fd fds)) (with_fds (fd_insert fds (alloc_fd fds) FdDir) model)) KB ->
realizes segs (mkCfg pre model) (t_alt2 KA KB).
Proof.
intros KA KB Hp HA HB.
eapply ncl_ecall; [apply nclosed_realizes | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
apply (rz_alt2 segs (mkCfg ms model) {e : Z | In e openat_errnos} unit
(open_nx_MS (fun fd => with_fds (fd_insert fds fd FdDir) model)) KA KB
(exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
- eapply node_open_MS.
+ exact (not_alloc_lit 56 H17 eq_refl eq_refl).
+ intros o. rewrite (openat_spec_head_MS H17 H10).
apply (openat_dot_outcome _ _ _ _ model (modeled_open_flags_rd _ Hfl) eq_refl Hfl).
rewrite open_in_mem_MS. exact (path_at_MS_cstr _ _ Hp).
+ intros fd. rewrite with_fds_halted'. exact Hh.
+ intros fd. rewrite with_fds_lazy. exact Hlazy.
- intros [e He]. cbn [open_nx_MS]. apply HA. exact He.
- intros []. cbn [open_nx_MS]. exact HB.
Qed.

#[using="w HF HE Hh Hlazy ms H17 H10 Hfl Hfree"] Lemma rz_openat_file_MS : forall p d KA KB,
path_at_MS (getr R 11) p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
fs_lookup (m_fs model) p = Some d ->
(forall e, In e openat_errnos -> realizes segs (mkCfg (post (errno_ret e)) model) KA) ->
realizes segs (mkCfg (post (alloc_fd fds))
(with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) model)) KB ->
realizes segs (mkCfg pre model) (t_alt2 KA KB).
Proof.
intros p d KA KB Hp Hne Hsl Hnd Hfs HA HB.
eapply ncl_ecall; [apply nclosed_realizes | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
apply (rz_alt2 segs (mkCfg ms model) {e : Z | In e openat_errnos} unit
(open_nx_MS (fun fd => with_fds (fd_insert fds fd (FdFile p (Z_to_bv 64 0))) model)) KA KB
(exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
- eapply node_open_MS.
+ exact (not_alloc_lit 56 H17 eq_refl eq_refl).
+ intros o. rewrite (openat_spec_head_MS H17 H10).
apply (openat_file_outcome _ _ _ _ model (modeled_open_flags_rd _ Hfl) eq_refl Hfl p d);
[rewrite open_in_mem_MS; exact (path_at_MS_cstr _ p Hp) | exact Hne | exact Hsl | exact Hnd | exact Hfs].
+ intros fd. rewrite with_fds_halted'. exact Hh.
+ intros fd. rewrite with_fds_lazy. exact Hlazy.
- intros [e He]. cbn [open_nx_MS]. apply HA. exact He.
- intros []. cbn [open_nx_MS]. exact HB.
Qed.
End OpenatRz.

#[using="w HF HE Hh Hlazy ms"] Lemma ncl_munmap : forall (J : config -> Prop) (a : word) (len : Z),
NClosed J ->
getr R 17 = Z_to_bv 64 215 ->
getr R 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
getr R 11 = Z_to_bv 64 len -> (0 < len)%Z ->
(bv_unsigned a + page_round_up_Z len <= task_size_max)%Z ->
map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
J (mkCfg (postm (Z_to_bv 64 0) (unfill a (Z_to_bv 64 (page_round_up_Z len)) m))
(munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)) ->
J (mkCfg pre model).
Proof.
intros J a len HJ H17 H10 Hal H11 Hlen Hnw Hhas Hc.
rewrite task_size_max_eq in Hnw.
assert (Hlen' : (len < two_pow_64)%Z).
{ pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE, two_pow_64 in *. lia. }
eapply ncl_ecall; [exact HJ | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
{ unfold ms. rewrite ms_gpr_MSsvc1, H11. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
{ unfold page_round_up. rewrite Hu1. reflexivity. }
assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_MSsvc0; exact H10).
assert (Hargs : munmap_args_ok ms model).
{ unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; try assumption.
intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
eapply (ncl_det J ms model _ (munmap_eff ms) (munmap_model (ms_gpr ms 0) (page_round_up (ms_gpr ms 1)) model));
[exact HJ | exact Hh | reflexivity
| intros o; apply (munmap_outcome_si segs ms _ model o); [apply (sysno_lit 215 H17); lia | exact Hargs]
| rewrite munmap_model_halted; exact Hh
| exact (munmap_model_no_lazy _ _ _ Hlazy) |].
unfold munmap_eff. rewrite H0, Hpr. unfold ms. rewrite adv_unmaps1_MSsvc. exact Hc.
Qed.

Section Getrandom.
Variable buflen : Z.
Hypothesis H17 : getr R 17 = Z_to_bv 64 278.
Hypothesis H11 : getr R 11 = Z_to_bv 64 buflen.
Hypothesis Hbl : (1 <= buflen)%Z.
Hypothesis Hblmax : (buflen <= 256)%Z.
Hypothesis H12 : getr R 12 = Z_to_bv 64 0 \/ getr R 12 = Z_to_bv 64 GRND_NONBLOCK.

Hypothesis Hok : store_ok segs m (getr R 10) (Z.to_nat buflen) = true.

Definition getrandom_I : Type :=
{bs : list byte | Z.of_nat (length bs) = buflen}.

Definition getrandom_nx (i : getrandom_I) : config :=
match i with
| exist _ bs _ => mkCfg (postm (len_word bs) (wbytes m (getr R 10) bs)) model
end.

#[using="H17 H11 Hbl Hblmax H12 Hok"] Lemma getrandom_outcome_MS : forall o,
syscall_spec (sys_input segs ms (getr R 17)) model o <->
getrandom_out (getr R 10) (Z_to_bv 64 buflen) model o.
Proof.
intros o.
rewrite (syscall_spec_278 _ model o) by (apply (sysno_lit 278 H17); lia).
rewrite in_arg0_si, in_arg1_si, in_arg2_si. unfold ms. rewrite ms_gpr_MSsvc0, ms_gpr_MSsvc1, ms_gpr_MSsvc2, H11.
destruct (read_bytes_map_of_store_ok segs m (getr R 10) (Z.to_nat buflen) Hok ltac:(lia)) as [wv Hw].
rewrite Z2Nat.id in Hw by lia.
apply (getrandom_outcome (getr R 10) (Z_to_bv 64 buflen) (getr R 12) _ model o wv).
- destruct H12 as [E|E]; rewrite E; [left; reflexivity | right; apply u64_lit; unfold GRND_NONBLOCK; lia].
- unfold modeled_rw_count. rewrite u64_lit by lia. apply Z.leb_le.
pose proof rw_bytes_max_ge17. lia.
- unfold w_is0, bv_eqb. rewrite u64_lit by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia.
- rewrite u64_lit by lia. unfold getrandom_small_max. exact Hblmax.
- rewrite in_wmem_si, ms_writable_byte_MSsvc. exact Hw.
Qed.

#[using="Hh Hlazy H17 H11 Hbl Hblmax H12 Hok"] Lemma node_getrandom : node_ok segs (mkCfg ms model) getrandom_I (fun _ => []) getrandom_nx.
Proof.
pose (effs := fun i : getrandom_I => match i with
| exist _ bs _ => mkEffect (len_word bs) [(getr R 10, bs)] [] end).
eapply node_ok_ext; [| apply (node_family segs ms model (getr R 17) getrandom_I effs (fun _ => model) (fun _ => []) _
Hh eq_refl getrandom_outcome_MS)].
- intros [bs Hbs]; cbn [effs getrandom_nx]; unfold ms. rewrite adv_write1_MSsvc. reflexivity.
- intros [bs Hbs]; cbn [effs]. exists bs.
rewrite u64_lit by lia. auto.
- intros o (bs & Hb & ->).
rewrite u64_lit in Hb by lia. exists (exist _ bs Hb). reflexivity.
- intros _; exact Hh.
- intros _; exact Hlazy.
- intros i. exact (not_spurious_lit 278 _ H17 eq_refl eq_refl).
Qed.

#[using="w HF HE Hh Hlazy ms H17 H11 Hbl Hblmax H12 Hok"] Lemma ncl_getrandom : forall (J : config -> Prop),
NClosed J ->
(forall bs, Z.of_nat (length bs) = buflen ->
J (mkCfg (postm (len_word bs) (wbytes m (getr R 10) bs)) model)) ->
J (mkCfg pre model).
Proof.
intros J HJ HB.
eapply ncl_ecall; [exact HJ | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
assert (Hbs0 : Z.of_nat (length (repeat (Z_to_bv 8 0) (Z.to_nat buflen))) = buflen).
{ rewrite repeat_length. lia. }
apply (HJ _ getrandom_I getrandom_nx (exist _ _ Hbs0) node_getrandom).
intros [bs Hb]; cbn [getrandom_nx]. apply HB; assumption.
Qed.

#[using="w HF HE Hh Hlazy ms H17 H11 Hbl Hblmax H12 Hok"] Lemma rz_getrandom_MS : forall K,
(forall bs, Z.of_nat (length bs) = buflen ->
realizes segs (mkCfg (postm (len_word bs) (wbytes m (getr R 10) bs)) model) K) ->
realizes segs (mkCfg pre model) K.
Proof. intros K HB. exact (ncl_getrandom _ (nclosed_realizes segs K) HB). Qed.
End Getrandom.

Section Newfstatat.
Hypothesis H17 : getr R 17 = Z_to_bv 64 79.
Hypothesis H10 : getr R 10 = AT_FDCWD.
Hypothesis H13 : getr R 13 = Z_to_bv 64 0.

#[using="H13"] Lemma flag32_a3 : bv_unsigned (flag32 (getr R 13)) = 0%Z.
Proof. rewrite H13. reflexivity. Qed.

#[using="H17 H10"] Lemma newfstatat_spec_head_MS : forall o,
syscall_spec (sys_input segs ms (getr R 17)) model o <->
newfstatat_spec AT_FDCWD32 (getr R 11) (flag32 (getr R 13)) (sys_input segs ms (getr R 17)) model o.
Proof.
intros o. rewrite (syscall_spec_79 _ model o) by (apply (sysno_lit 79 H17); lia).
rewrite in_arg0_si, in_arg1_si, in_arg3_sys_input. unfold ms.
rewrite ms_gpr_MSsvc0, ms_gpr_MSsvc1, ms_gpr_MSsvc3, H10. reflexivity.
Qed.

#[using="Type"] Lemma stat_in_mem_MS : in_mem (sys_input segs ms (getr R 17)) = mrb segs m.
Proof. unfold ms. rewrite in_mem_si, ms_read_byte_MSsvc. reflexivity. Qed.

#[using="w HF HE Hh Hlazy ms H17 H10 H13"] Lemma ncl_newfstatat_toolong : forall (J : config -> Prop) bs,
NClosed J ->
rdn segs m (getr R 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
J (mkCfg (post (errno_ret ENAMETOOLONG)) model) ->
J (mkCfg pre model).
Proof.
intros J bs HJ Hrd Hnz Hc.
pose proof (read_cstr_toolong_of_rdn segs m (getr R 11) bs (rdn_length _ _ _ _ _ Hrd) Hnz Hrd) as Hp.
eapply ncl_ecall; [exact HJ | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
eapply (ncl_det J ms model _ _ model); [exact HJ | exact Hh | reflexivity | | exact Hh | exact Hlazy |].
- intros o. rewrite newfstatat_spec_head_MS.
apply (newfstatat_toolong_outcome _ _ _ _ model flag32_a3). rewrite stat_in_mem_MS. exact Hp.
- unfold ms. rewrite adv_copyins_ret_MSsvc. exact Hc.
Qed.

#[using="w HF HE Hh Hlazy ms H17 H10 H13"] Lemma ncl_newfstatat_empty : forall (J : config -> Prop),
NClosed J ->
path_at_MS (getr R 11) [] ->
J (mkCfg (post (errno_ret ENOENT)) model) ->
J (mkCfg pre model).
Proof.
intros J HJ Hp Hc.
eapply ncl_ecall; [exact HJ | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
eapply (ncl_det J ms model _ _ model); [exact HJ | exact Hh | reflexivity | | exact Hh | exact Hlazy |].
- intros o. rewrite newfstatat_spec_head_MS.
apply (newfstatat_empty_outcome _ _ _ _ model flag32_a3). rewrite stat_in_mem_MS. exact (path_at_MS_cstr _ [] Hp).
- unfold ms. rewrite adv_copyins_ret_MSsvc. exact Hc.
Qed.

#[using="w HF HE Hh Hlazy ms H17 H10 H13"] Lemma ncl_newfstatat_absent : forall (J : config -> Prop) p,
NClosed J ->
path_at_MS (getr R 11) p -> p <> [] -> p <> dot_path -> fs_lookup (m_fs model) p = None ->
J (mkCfg (post (errno_ret ENOENT)) model) ->
J (mkCfg pre model).
Proof.
intros J p HJ Hp Hne Hnd Hfs Hc.
eapply ncl_ecall; [exact HJ | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
eapply (ncl_det J ms model _ _ model); [exact HJ | exact Hh | reflexivity | | exact Hh | exact Hlazy |].
- intros o. rewrite newfstatat_spec_head_MS.
apply (newfstatat_absent_outcome _ _ _ _ model flag32_a3 eq_refl p);
[rewrite stat_in_mem_MS; exact (path_at_MS_cstr _ p Hp) | exact Hne | exact Hnd | exact Hfs].
- unfold ms. rewrite adv_copyins_ret_MSsvc. exact Hc.
Qed.

End Newfstatat.

Section ClockGettime.
Hypothesis H17 : getr R 17 = Z_to_bv 64 113.

Hypothesis H10 : clockid_percall_b (clockid32 (getr R 10)) = true.

Hypothesis Hok : store_ok segs m (getr R 11) 16 = true.

Definition clock_I : Type := {bs : list byte | realtime_ok_b bs = true}.
Definition clock_nx (i : clock_I) : config :=
mkCfg (postm (Z_to_bv 64 0) (wbytes m (getr R 11) (proj1_sig i))) model.

#[using="Hh Hlazy H17 H10 Hok"] Lemma node_clock_gettime : node_ok segs (mkCfg ms model) clock_I (fun _ => []) clock_nx.
Proof.
destruct (read_bytes_map_of_store_ok segs m (getr R 11) 16 Hok ltac:(cbn; lia)) as [wv Hw].
assert (Hchk : forall o, syscall_spec (sys_input segs ms (getr R 17)) model o <-> clock_rt_out (getr R 11) model o).
{ intros o. rewrite (syscall_spec_113 _ model o) by (apply (sysno_lit 113 H17); lia).
rewrite in_arg0_si, in_arg1_si. unfold ms. rewrite ms_gpr_MSsvc0, ms_gpr_MSsvc1.
apply (clock_gettime_realtime_outcome _ _ _ model o wv H10).
rewrite in_wmem_si, ms_writable_byte_MSsvc. exact Hw. }
pose (effs := fun i : clock_I => mkEffect (Z_to_bv 64 0) [(getr R 11, proj1_sig i)] []).
eapply node_ok_ext; [| apply (node_family segs ms model (getr R 17) clock_I effs (fun _ => model) (fun _ => []) _
Hh eq_refl Hchk)].
- intros [bs Hbs]. unfold effs, clock_nx. cbn [proj1_sig]. unfold ms. rewrite adv_write1_MSsvc. reflexivity.
- intros [bs Hbs]. unfold effs. cbn [proj1_sig]. exists bs. auto.
- intros o (bs & Hbs & ->). exists (exist _ bs Hbs). reflexivity.
- intros _; exact Hh.
- intros _; exact Hlazy.
- intros i. exact (not_spurious_lit 113 _ H17 eq_refl eq_refl).
Qed.

#[using="w HF HE Hh Hlazy ms H17 H10 Hok"] Lemma ncl_clock_gettime : forall (J : config -> Prop),
NClosed J ->
(forall bs, realtime_ok_b bs = true -> J (mkCfg (postm (Z_to_bv 64 0) (wbytes m (getr R 11) bs)) model)) ->
J (mkCfg pre model).
Proof.
intros J HJ HB.
eapply ncl_ecall; [exact HJ | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
apply (HJ _ clock_I clock_nx (exist _ _ realtime_ok_zeros) node_clock_gettime).
intros [bs Hbs]. unfold clock_nx. cbn [proj1_sig]. apply HB. exact Hbs.
Qed.

#[using="w HF HE Hh Hlazy ms H17 H10 Hok"] Lemma lbw_clock_gettime : forall (V : config -> Prop) (T : TSet) (p : bool) (wf : list byte -> bool),
(forall bs, realtime_ok_b bs = true ->
lbw segs V T (wf bs) (mkCfg (postm (Z_to_bv 64 0) (wbytes m (getr R 11) bs)) model)) ->
(p = true -> exists bs0, realtime_ok_b bs0 = true /\ wf bs0 = true) ->
lbw segs V T p (mkCfg pre model).
Proof.
intros V T p wf HB Hw.
eapply ncl_ecall; [apply nclosed_lbw | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
apply (lbw_node segs V T p (mkCfg ms model) clock_I clock_nx (fun i => Some (wf (proj1_sig i))) node_clock_gettime).
- intros [bs Hbs] q Hq. injection Hq as <-. unfold clock_nx. cbn [proj1_sig]. apply HB. exact Hbs.
- intros i Hq. discriminate Hq.
- intros Hp. destruct (Hw Hp) as (bs0 & H1 & H2). exists (exist _ bs0 H1). cbn [proj1_sig]. rewrite H2. reflexivity.
Qed.
End ClockGettime.

Section Mremap.
Variables (old : word) (old_len new_len : Z).
Hypothesis H17 : getr R 17 = Z_to_bv 64 216.
Hypothesis H10 : getr R 10 = old.
Hypothesis H11 : getr R 11 = Z_to_bv 64 old_len.
Hypothesis H12 : getr R 12 = Z_to_bv 64 new_len.
Hypothesis H13 : getr R 13 = Z_to_bv 64 MREMAP_MAYMOVE.
Hypothesis Hal : (bv_unsigned old mod page_size = 0)%Z.
Hypothesis Hol : (0 < old_len)%Z.
Hypothesis Hnl : (0 < new_len)%Z.
Let old_nZ := page_round_up_Z old_len.
Let new_nZ := page_round_up_Z new_len.
Let old_n : word := Z_to_bv 64 old_nZ.
Let new_n : word := Z_to_bv 64 new_nZ.

Hypothesis Hob : (bv_unsigned old + old_nZ <= alloc_ceiling)%Z.
Hypothesis Hceil : alloc_top (m_vmmaps model) = alloc_ceiling.
Hypothesis Hnb : (new_nZ < two_pow_64)%Z.
Hypothesis Hhas : map_has (vm_maps (m_vmmaps model)) old old_n = true.
Hypothesis Hrf : region_free (vm_reserved (m_vmmaps model)) old old_n = true.
Hypothesis Hna : region_free (vm_noaccess (m_vmmaps model)) old old_n = true.

#[using="RC__ old new_len Hol old_nZ new_nZ Hob"] Lemma old_len_lt : (old_len < 2 ^ 64)%Z.
Proof.
pose proof alloc_ceiling_val. pose proof (u64_range old).
pose proof (page_round_up_Z_bounds old_len ltac:(lia)). unfold old_nZ in *. lia.
Qed.

#[using="RC__ old old_len Hnl old_nZ new_nZ Hnb"] Lemma new_len_lt : (new_len < 2 ^ 64)%Z.
Proof. pose proof (page_round_up_Z_bounds new_len ltac:(lia)). unfold new_nZ, two_pow_64 in *. lia. Qed.

#[using="RC__ Hlazy new_len H11 H12 H13 Hol Hnl new_nZ Hob Hceil Hnb Hhas Hrf Hna"] Lemma mremap_gates :
bv_unsigned (getr R 13) = MREMAP_MAYMOVE
/\ page_align_is0_b (getr R 12) = false
/\ page_align_is0_b (getr R 11) = false
/\ mremap_source_b (m_vmmaps model) old old_n old_nZ = true
/\ mremap_backing_uniform_b model old old_n = true.
Proof.
pose proof old_len_lt. pose proof new_len_lt. pose proof alloc_ceiling_val.
pose proof (page_round_up_Z_bounds old_len ltac:(lia)). pose proof (u64_range old).
repeat split.
- rewrite H13. apply u64_lit. unfold MREMAP_MAYMOVE. lia.
- unfold page_align_is0_b, w_is0, bv_eqb. rewrite H12, u64_lit by lia.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite (proj2 (Z.eqb_neq _ _)) by lia.
apply Z.leb_gt. unfold new_nZ in Hnb. exact Hnb.
- unfold page_align_is0_b, w_is0, bv_eqb. rewrite H11, u64_lit by lia.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite (proj2 (Z.eqb_neq _ _)) by lia.
apply Z.leb_gt. unfold old_nZ in *. unfold two_pow_64. lia.
- unfold mremap_source_b. rewrite Hceil, (proj2 (Z.leb_le _ _) Hob), Hrf, Hhas, Hna. reflexivity.
- unfold mremap_backing_uniform_b. rewrite Hlazy. cbn [map_contains existsb region_free]. reflexivity.
Qed.

#[using="RC__ H17 H10 H11 H12 old_nZ new_nZ"] Lemma mremap_spec_MS : forall o,
syscall_spec (sys_input segs ms (getr R 17)) model o <->
mremap_spec old (Z_to_bv 64 old_len) (Z_to_bv 64 new_len) (getr R 13) (sys_input segs ms (getr R 17)) model o.
Proof.
intros o. rewrite (syscall_spec_216 _ model o) by (apply (sysno_lit 216 H17); lia).
rewrite in_arg0_si, in_arg1_si, in_arg2_si, in_arg3_sys_input. unfold ms.
rewrite ms_gpr_MSsvc0, ms_gpr_MSsvc1, ms_gpr_MSsvc2, ms_gpr_MSsvc3, H10, H11, H12. reflexivity.
Qed.

#[using="RC__ old new_len Hol new_nZ Hob"] Lemma old_nZ_eq : page_round_up_Z (bv_unsigned (Z_to_bv 64 old_len)) = old_nZ.
Proof. pose proof old_len_lt. rewrite u64_lit by lia. reflexivity. Qed.
#[using="RC__ old old_len Hnl old_nZ Hnb"] Lemma new_nZ_eq : page_round_up_Z (bv_unsigned (Z_to_bv 64 new_len)) = new_nZ.
Proof. pose proof new_len_lt. rewrite u64_lit by lia. reflexivity. Qed.

#[using="RC__ w HF HE Hh Hlazy ms H17 H10 H11 H12 H13 Hal Hol Hnl old_n Hob Hceil Hnb Hhas Hrf Hna"] Lemma ncl_mremap_same : forall (J : config -> Prop),
NClosed J ->
old_nZ = new_nZ ->
J (mkCfg (post old) model) ->
J (mkCfg pre model).
Proof.
intros J HJ Heq Hc. destruct mremap_gates as (G1 & G2 & G3 & G4 & G5).
eapply ncl_ecall; [exact HJ | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
eapply (ncl_det J ms model _ (mkEffect old [] []) model); [exact HJ | exact Hh | reflexivity | | exact Hh | exact Hlazy |].
- intros o. rewrite mremap_spec_MS.
apply (mremap_same_outcome old _ _ (getr R 13) _ model G1 Hal);
rewrite ?H11, ?H12, ?old_nZ_eq, ?new_nZ_eq; try assumption.
+ rewrite <- H12. exact G2.
+ rewrite <- H11. exact G3.
- unfold ms. rewrite adv_MSsvc. exact Hc.
Qed.

End Mremap.

#[using="w HF HE Hh Hlazy ms"] Lemma rz_writev_MS : forall (fd : Z) (iov : word) iovs bss (T : nat -> TSet),
fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
(0 < fd < 2^31)%Z ->
getr R 17 = Z_to_bv 64 66 ->
getr R 10 = Z_to_bv 64 fd ->
getr R 11 = iov ->
getr R 12 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
(1 <= length iovs <= 1024)%nat ->
(bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
iov_array segs m iov iovs ->
iov_bufs_ok iovs ->
iov_bufs segs m iovs bss ->
let bs := concat bss in
(1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
(forall k, (1 <= k)%nat -> (k <= length bs)%nat ->
realizes segs (mkCfg (post (Z_to_bv 64 (Z.of_nat k))) model) (T k)) ->
realizes segs (mkCfg pre model)
(t_alt (fun i : wr_index bs => t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).
Proof.
intros fd iov iovs bss T Hfd Hfdr H17 H10 H11 H12 Hcnt Hiok Harr Hbok Hbufs bs Ht1 Ht30 Hk.
eapply ncl_ecall; [apply nclosed_realizes | exact Hh | exact Hlazy | exact HF | exact HE |]. fold ms.
eapply (rz_writev_pending segs ms (getr R 17) model fd iov iovs bss T);
[reflexivity | exact Hh | exact Hlazy | reflexivity | exact Hfd | exact Hfdr
| apply (sysno_lit 66 H17); lia
| unfold ms; rewrite ms_gpr_MSsvc0; exact H10 | unfold ms; rewrite ms_gpr_MSsvc1; exact H11
| unfold ms; rewrite ms_gpr_MSsvc2; exact H12
| exact Hcnt | exact Hiok | exact Harr | exact Hbok | exact Hbufs | exact Ht1 | exact Ht30 |].
intros k Hk1 Hk2. unfold ms. rewrite adv_set_MSsvc. apply Hk; assumption.
Qed.

#[using="w HF HE Hh Hlazy ms"] Lemma rz_writev_wall_MS : forall (fd : Z) (iov : word) iovs bss (K : TSet),
fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
(0 < fd < 2^31)%Z ->
getr R 17 = Z_to_bv 64 66 ->
getr R 10 = Z_to_bv 64 fd ->
getr R 11 = iov ->
getr R 12 = Z_to_bv 64 (Z.of_nat (length iovs)) ->
(1 <= length iovs <= 1024)%nat ->
(bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
iov_array segs m iov iovs ->
iov_bufs_ok iovs ->
iov_bufs segs m iovs bss ->
let bs := concat bss in
(1 <= iovs_total iovs)%Z -> (iovs_total iovs <= 2 ^ 30)%Z ->
K [] ->
(forall k, (1 <= k)%nat -> (k <= length bs)%nat ->
realizes segs (mkCfg (post (Z_to_bv 64 (Z.of_nat k))) model)
(t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs)) K)) ->
realizes segs (mkCfg pre model) (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs) K).
Proof.
intros fd iov iovs bss K Hfd Hfdr H17 H10 H11 H12 Hcnt Hiok Harr Hbok Hbufs bs Ht1 Ht30 HK Hk.
pose proof (gather_iovecs_length _ _ _ (gather_of_bufs segs ms iovs bss eq_refl Hbufs)) as Hlen.
apply rz_wall; [unfold bs; lia | exact HK |].
apply (rz_writev_MS fd iov iovs bss (fun k => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs)) K)); assumption.
Qed.

End MSNodes.

End WithSegs.

End RC__1.
End Mq1.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uaccess.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import QwNp Qpox QsV0 QsRG.Mq0 Qnhz.Mq0 QsRG Qrxj QSjk Qn1e.Mq1 QiVh Qn1e QRjH QBxa.Mq4 QRjH.Mq3 QBxa.Mq0 Q9ox.Mq0 QSpR.Mq2.
Import QMz4.
Import ListNotations.
Open Scope bv_scope.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma rz_read_dir_mapped : forall regs (pc : word) mem model w fd (cnt : Z) K,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None -> m_vm_lazy model = [] ->
getr regs 17 = Z_to_bv 64 63 ->
getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
fd_lookup (m_fds model) fd = Some FdDir ->
getr regs 12 = Z_to_bv 64 cnt ->
(1 <= cnt)%Z -> (cnt <= 2 ^ 24)%Z ->
(bv_unsigned (getr regs 11) + cnt <= task_size_max)%Z ->
store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
intros regs pc mem model w fd cnt K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk H12 Hc1 H64 Hover Hok Hc.
eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
eapply rz_ret_only_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
intros o. rewrite (syscall_spec_63 _ model o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
rewrite in_arg0_si, in_arg1_si, in_arg2_si, ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32).
apply (read_dir_outcome fd _ _ _ model o Hlk).

apply access_okb_of_bound. rewrite H12, u64_lit by lia. rewrite <- task_size_max_eq. exact Hover.
Qed.

End WithSegs.
End FPGEN1.

End Mq2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qrxj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qrxj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
Section FPGEN1.
Context {fF : FPF} {fC : FPC}.

Definition vals_ev (vals : list word) : nat -> word :=
fun n => nth n vals (Z_to_bv 64 0).

Fixpoint expr_vars_lt (b : nat) (e : expr) : bool :=
match e with
| ELit _ => true
| EVar n => Nat.ltb n b
| EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
| EExt _ _ _ x => expr_vars_lt b x
| EBlob _ _ _ _ => true
end.

Definition saddr_vars_lt (b : nat) (a : saddr) : bool := expr_vars_lt b (a_base a).

Fixpoint sr_vars_lt (b : nat) (sr : list expr) : bool :=
match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.

Definition kentry_vars_lt (b : nat) (K : kentry) : bool :=
match K with
| KWord a _ v => saddr_vars_lt b a && expr_vars_lt b v
| KZero a n => saddr_vars_lt b a && expr_vars_lt b n
| KBlob a n _ => saddr_vars_lt b a && expr_vars_lt b n
| KImg _ _ => true
| KAlign e _ => expr_vars_lt b e
| KRange e _ _ => expr_vars_lt b e
| KWr a _ => saddr_vars_lt b a
| KDisj a1 _ a2 _ => saddr_vars_lt b a1 && saddr_vars_lt b a2
end.

Fixpoint kn_vars_lt (b : nat) (kn : list kentry) : bool :=
match kn with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.

Fixpoint log_vars_lt (b : nat) (log : list sentry) : bool :=
match log with
| [] => true
| SE a _ v :: r => saddr_vars_lt b a && expr_vars_lt b v && log_vars_lt b r
end.

Definition env_agree (b : nat) (E E' : env) : Prop :=
(forall n, (n < b)%nat -> ev E n = ev E' n) /\ eb E = eb E'.

#[using="Type"] Lemma edenot_agree : forall b E E' e,
env_agree b E E' -> expr_vars_lt b e = true -> edenot E e = edenot E' e.
Proof.
intros b E E' e [Hv Hb]. induction e; cbn [expr_vars_lt edenot]; intros H;
repeat match goal with
| H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
end;
try reflexivity;
try (rewrite IHe1, IHe2 by assumption; reflexivity);
try (rewrite IHe by assumption; reflexivity).
- apply Nat.ltb_lt in H. apply Hv. exact H.
- rewrite Hb. reflexivity.
Qed.

#[using="Type"] Lemma adenot_agree : forall b E E' a,
env_agree b E E' -> saddr_vars_lt b a = true -> adenot E a = adenot E' a.
Proof.
intros b E E' a Ha H. unfold adenot. rewrite (edenot_agree b E E' _ Ha H). reflexivity.
Qed.

#[using="Type"] Lemma regs_ok_agree : forall b E E' sr regs,
env_agree b E E' -> sr_vars_lt b sr = true -> regs_ok E sr regs -> regs_ok E' sr regs.
Proof.
intros b E E' sr regs Ha Hsr HR r. rewrite (HR r).
unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
assert (Hnth : forall i, expr_vars_lt b (nth i sr (ELit 0)) = true).
{ clear HR r. induction sr as [|e t IH]; intros i.
- destruct i; reflexivity.
- cbn [sr_vars_lt] in Hsr. apply andb_prop in Hsr as [He Ht].
destruct i; [exact He | apply IH; exact Ht]. }
apply (edenot_agree b); [exact Ha | apply Hnth].
Qed.

#[using="Type"] Lemma mem_denot_agree : forall b E E' base log,
env_agree b E E' -> log_vars_lt b log = true -> mem_denot E base log = mem_denot E' base log.
Proof.
intros b E E' base log Ha. induction log as [|[a w v] r IH]; cbn [log_vars_lt mem_denot]; intros H.
- reflexivity.
- apply andb_prop in H as [H1 H3]. apply andb_prop in H1 as [H1 H2].
rewrite IH by exact H3. rewrite (adenot_agree b E E' a Ha H1), (edenot_agree b E E' v Ha H2).
reflexivity.
Qed.

#[using="Type"] Lemma flat_agree : forall b E E' a n,
env_agree b E E' -> saddr_vars_lt b a = true -> flat E a n <-> flat E' a n.
Proof.
intros b E E' a n Ha H. unfold flat, estart.
rewrite (edenot_agree b E E' (a_base a) Ha H). tauto.
Qed.

#[using="Type"] Lemma log_flat_agree : forall b E E' log,
env_agree b E E' -> log_vars_lt b log = true -> log_flat E log -> log_flat E' log.
Proof.
intros b E E' log Ha. induction log as [|[a w v] r IH]; cbn [log_vars_lt log_flat]; intros H Hl.
- exact I.
- apply andb_prop in H as [H1 H3]. apply andb_prop in H1 as [H1 H2].
destruct Hl as (Hw & Hf & Hr). split; [exact Hw|]. split.
+ apply (flat_agree b E E' a _ Ha H1). exact Hf.
+ apply IH; assumption.
Qed.

#[using="Type"] Lemma know_ok_agree : forall segs b E E' base kn,
env_agree b E E' -> kn_vars_lt b kn = true -> know_ok segs E base kn -> know_ok segs E' base kn.
Proof.
intros segs b E E' base kn Ha. induction kn as [|K r IH]; cbn [kn_vars_lt]; intros H Hk.
- constructor.
- apply andb_prop in H as [HK Hr]. apply Forall_cons_iff in Hk as [Hk1 Hk2].
constructor; [| apply IH; assumption].
destruct Ha as [Hv Hb].
destruct K as [a w v|a n|a n k|lo hi|ae am|re rlo rhi|wa wn|da1 dn1 da2 dn2]; cbn [kentry_vars_lt kentry_ok] in *;
[ | | | | rewrite <- (edenot_agree b E E' ae (conj Hv Hb) HK); exact Hk1
| rewrite <- (edenot_agree b E E' re (conj Hv Hb) HK); exact Hk1
| unfold flat, estart in *; rewrite <- (edenot_agree b E E' (a_base wa) (conj Hv Hb) HK); exact Hk1
| apply andb_prop in HK as [HK1 HK2]; unfold estart in *;
rewrite <- (edenot_agree b E E' (a_base da1) (conj Hv Hb) HK1),
<- (edenot_agree b E E' (a_base da2) (conj Hv Hb) HK2); exact Hk1 ].
+ apply andb_prop in HK as [H1 H2].
rewrite <- (adenot_agree b E E' a (conj Hv Hb) H1), <- (edenot_agree b E E' v (conj Hv Hb) H2).
destruct Hk1 as (A & B & C). split; [exact A|]. split; [|exact C].
apply (flat_agree b E E' a _ (conj Hv Hb) H1). exact B.
+ apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
destruct Hk1 as [A B]. split; [|exact B].
unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
+ apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *. rewrite <- Hb.
rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
destruct Hk1 as (A & B & C). split; [|split; [exact B | exact C]].
unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
+ exact Hk1.
Qed.

#[using="Type"] Lemma vals_app_agree : forall vals extra ebs,
env_agree (length vals) (Env (vals_ev vals) ebs) (Env (vals_ev (vals ++ extra)) ebs).
Proof.
intros vals extra ebs. split; [|reflexivity]. intros n Hn. cbn [ev]. unfold vals_ev.
rewrite app_nth1 by exact Hn. reflexivity.
Qed.

Section Run.
Variable segs : list Segment.

#[using="Type"] Lemma st_ok_entry : forall E base rom pc sr kn nx regs,
regs_ok E sr regs -> know_ok segs E base kn ->
st_ok segs E base rom (SS pc sr [] kn nx) (mkst regs (Z_to_bv 64 pc) base rom).
Proof.
intros E base rom pc sr kn nx regs HR HK. exists regs. cbn [s_pc s_log s_regs s_know mem_denot].
split; [reflexivity|]. split; [exact HR|]. split; [exact I | exact HK].
Qed.

#[using="Type"] Theorem run_sound : forall fuel stops scr pc sr kn nx ss' scs scr' E base rom regs,
sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
regs_ok E sr regs -> know_ok segs E base kn ->
scs_denot segs base E scs ->
exists R, regs_ok E (s_regs ss') R
/\ log_flat E (s_log ss')
/\ msteps segs (mkst regs (Z_to_bv 64 pc) base rom)
(mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof.
intros fuel stops scr pc sr kn nx ss' scs scr' E base rom regs Hex HR HK Hsc.
eapply sym_exec_ex; [exact Hex | exact Hsc | apply st_ok_entry; assumption].
Qed.

#[using="Type"] Theorem carry_after : forall E base log kn hints kn' scs hs',
carry log kn hints = (kn', scs, hs') ->
log_flat E log -> know_ok segs E base kn -> scs_denot segs base E scs ->
know_ok segs E (mem_denot E base log) kn'.
Proof. intros. eapply carry_sound; eauto. Qed.

#[using="Type"] Lemma reg_val : forall E sr R (r : reg), regs_ok E sr R -> getr R r = edenot E (sr_get sr r).
Proof. intros E sr R r HR. apply HR. Qed.

#[using="Type"] Lemma regs_ok_set : forall E sr R (rd : reg) v e,
regs_ok E sr R -> rd <> 0%bv -> edenot E e = v ->
regs_ok E (sr_upd sr (ridx rd) e) (regupd R rd v).
Proof.
intros E sr R rd v e HR Hrd He.
pose proof (regs_ok_upd E sr R rd v e HR He) as H.
assert (Hb : bv_eqb rd 0 = false).
{ unfold bv_eqb. apply Z.eqb_neq. intros Hc. apply Hrd. apply bv_eq. exact Hc. }
rewrite Hb in H. exact H.
Qed.

End Run.

Definition sr_init : list expr :=
[ELit 0; ELit 0; EVar 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0;
ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0; ELit 0].

#[using="Type"] Lemma regs_ok_init : forall (sp : word) rest ebs,
regs_ok (Env (vals_ev (sp :: rest)) ebs) sr_init
(regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp).
Proof.
intros sp rest ebs r.
unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
- pose proof (ridx_range r) as Hlt.
rewrite <- (ridx_roundtrip r). rewrite <- (ridx_roundtrip r) in Hr0.
set (n := ridx r) in *. clearbody n.
do 32 (destruct n as [|n]; [vm_compute in Hr0 |- *; first [discriminate | reflexivity] |]).
exfalso. lia.
Qed.

Definition stk_ok (segs : list Segment) (mem : word -> option byte) (sp : word) (K : Z) : Prop :=
forall (a : word) (n : nat),
(bv_unsigned sp - K <= bv_unsigned a)%Z ->
(bv_unsigned a + Z.of_nat n <= bv_unsigned sp)%Z ->
store_ok segs mem a n = true.

#[using="Type"] Lemma stk_ok_vaddi : forall segs mem sp K off n,
stk_ok segs mem sp K -> (K <= bv_unsigned sp)%Z ->
(- K <= off)%Z -> (off + Z.of_nat n <= 0)%Z ->
store_ok segs mem (v_addi sp off) n = true.
Proof.
intros segs mem sp K off n Hs HK H1 H2. pose proof (u64_range sp).
apply Hs; unfold v_addi; rewrite u_small by lia; lia.
Qed.

#[using="Type"] Lemma stk_ok_lit : forall segs mem sp K z n,
stk_ok segs mem sp K ->
(bv_unsigned sp - K <= z)%Z -> (z + Z.of_nat n <= bv_unsigned sp)%Z -> (0 <= z)%Z ->
store_ok segs mem (Z_to_bv 64 z) n = true.
Proof.
intros segs mem sp K z n Hs H1 H2 H3. pose proof (u64_range sp).
apply Hs; rewrite u_small by lia; lia.
Qed.

#[using="Type"] Lemma stk_ok_grows : forall segs mem mem' sp K,
stk_ok segs mem sp K -> mem_grows mem mem' -> stk_ok segs mem' sp K.
Proof.
intros segs mem mem' sp K Hs Hg a n H1 H2. eapply store_ok_mono; [exact Hg | apply Hs; assumption].
Qed.

#[using="Type"] Lemma stk_ok_mem_denot : forall segs E mem log sp K,
stk_ok segs mem sp K -> stk_ok segs (mem_denot E mem log) sp K.
Proof. intros. eapply stk_ok_grows; [eassumption | apply mem_denot_grows]. Qed.

#[using="Type"] Lemma stk_ok_init : forall segs ph sp argv envp uid hw rnd,
stk_ok segs (wrap_mem ph sp argv envp uid hw rnd) sp stack_max_size.
Proof.
intros segs ph sp argv envp uid hw rnd a n H1 H2.
apply store_ok_wrap_window; assumption.
Qed.

#[using="Type"] Lemma kwr_of_stk_ok : forall segs E mem (e : expr) (sp : word) K,
edenot E e = sp -> stk_ok segs mem sp K -> (0 <= K <= bv_unsigned sp)%Z ->
kentry_ok segs E mem (KWr (SA e (- K)) K).
Proof.
intros segs E mem e sp K He Hs HK. cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off]. rewrite He.
pose proof (u64_range sp). split; [lia|].
intros d m Hd Hm. apply Hs; rewrite u_small by lia; lia.
Qed.

#[using="Type"] Lemma kword_intro : forall segs E mem (e : expr) (a : word) off w (v : expr) (x : word),
edenot E e = a -> edenot E v = x -> (1 <= w)%nat -> (w <= 8)%nat ->
(0 <= bv_unsigned a + off)%Z -> (bv_unsigned a + off + Z.of_nat w <= 2 ^ 64)%Z ->
rdn segs mem (Z_to_bv 64 (bv_unsigned a + off)) w = Some (word_to_le_bytes w x) ->
kentry_ok segs E mem (KWord (SA e off) w v).
Proof.
intros segs E mem e a off w v x He Hv Hw1 Hw H1 H2 Hr. cbn [kentry_ok]. unfold flat, estart, adenot, v_addi.
cbn [a_base a_off]. rewrite He, Hv. split; [exact Hw|]. split; [lia | exact Hr].
Qed.

#[using="Type"] Lemma krange_intro : forall segs E mem (e : expr) lo hi,
(lo <= bv_unsigned (edenot E e) <= hi)%Z -> kentry_ok segs E mem (KRange e lo hi).
Proof. intros. cbn [kentry_ok]. lia. Qed.

#[using="Type"] Lemma kalign_intro : forall segs E mem (e : expr) m,
(0 < m)%Z -> (bv_unsigned (edenot E e) mod m = 0)%Z -> kentry_ok segs E mem (KAlign e m).
Proof. intros. cbn [kentry_ok]. auto. Qed.

#[using="Type"] Lemma kimg_intro : forall segs E mem lo hi,
(0 <= lo)%Z -> (hi <= 2 ^ 64)%Z ->
(forall i, (lo <= i < hi)%Z -> mem (Z_to_bv 64 i) = None) ->
kentry_ok segs E mem (KImg lo hi).
Proof. intros. cbn [kentry_ok]. auto. Qed.

#[using="Type"] Lemma kzero_intro : forall segs E mem (e : expr) (a : word) off (n : expr) len,
edenot E e = a -> bv_unsigned (edenot E n) = len ->
(0 <= bv_unsigned a + off)%Z -> (0 < len)%Z -> (bv_unsigned a + off + len <= 2 ^ 64)%Z ->
(forall i, (0 <= i < len)%Z -> mem (Z_to_bv 64 (bv_unsigned a + off + i)) = Some (Z_to_bv 8 0)) ->
kentry_ok segs E mem (KZero (SA e off) n).
Proof.
intros segs E mem e a off n len He Hn H1 H2 H3 Hz. cbn [kentry_ok]. unfold flat, elenZ, estart.
cbn [a_base a_off]. rewrite He, Hn. split; [lia | exact Hz].
Qed.

#[using="Type"] Lemma kblob_intro : forall segs E mem (e : expr) (a : word) off (n : expr) k bs,
edenot E e = a -> eb E k = bs -> bv_unsigned (edenot E n) = Z.of_nat (length bs) ->
(0 <= bv_unsigned a + off)%Z -> (bv_unsigned a + off < 2 ^ 64)%Z ->
(bv_unsigned a + off + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
(forall i, (0 <= i < Z.of_nat (length bs))%Z ->
mem (Z_to_bv 64 (bv_unsigned a + off + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))) ->
kentry_ok segs E mem (KBlob (SA e off) n k).
Proof.
intros segs E mem e a off n k bs He Hb Hn H1 H1' H2 Hz. cbn [kentry_ok]. unfold flat, elenZ, estart.
cbn [a_base a_off]. rewrite He, Hn, Hb. split; [lia|]. split; [reflexivity | exact Hz].
Qed.

#[using="Type"] Lemma wrap_mem_none_low : forall ph sp argv envp uid hw rnd (i : Z),
(0 <= i)%Z -> (i < bv_unsigned sp - stack_max_size)%Z ->
wrap_mem ph sp argv envp uid hw rnd (Z_to_bv 64 i) = None.
Proof.
intros ph sp argv envp uid hw rnd i H0 Hi. unfold wrap_mem.
pose proof (u64_range sp) as Hsp.
assert (Hu : bv_unsigned (Z_to_bv 64 i) = i) by (apply u_small; unfold stack_max_size in Hi; lia).
unfold stack_to_mem. rewrite Hu.
replace (Z.leb (bv_unsigned sp) i) with false by (symmetry; apply Z.leb_gt; unfold stack_max_size in Hi; lia).
replace (Z.leb (bv_unsigned sp - stack_max_size) i) with false by (symmetry; apply Z.leb_gt; lia).
reflexivity.
Qed.

#[using="Type"] Lemma ext_val_zx_id : forall n (v : word),
(bv_unsigned v < 2 ^ (8 * Z.of_nat n))%Z -> ext_val false 0 n v = v.
Proof.
intros n v Hv. unfold ext_val, ext_Z. pose proof (u64_range v).
change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r, Z.mod_small by lia.
apply Z_to_bv_bv_unsigned.
Qed.

#[using="Type"] Lemma ext_val_sx_id : forall n (v : word),
(1 <= n)%nat -> (bv_unsigned v < 2 ^ (8 * Z.of_nat n - 1))%Z -> ext_val true 0 n v = v.
Proof.
intros n v Hn Hv. unfold ext_val, ext_Z. pose proof (u64_range v).
assert (Hp : (2 ^ (8 * Z.of_nat n - 1) * 2 = 2 ^ (8 * Z.of_nat n))%Z).
{ rewrite Z.mul_comm, <- Z.pow_succ_r by lia. f_equal. lia. }
change (2 ^ (8 * Z.of_nat 0))%Z with 1%Z. rewrite Z.div_1_r, Z.mod_small by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
replace (Z.of_N (8 * N.of_nat n)) with (8 * Z.of_nat n)%Z by lia.
rewrite <- Hp. rewrite Z.div_mul by lia.
rewrite Z.mod_small by lia. replace (bv_unsigned v + 2 ^ (8 * Z.of_nat n - 1) - 2 ^ (8 * Z.of_nat n - 1))%Z
with (bv_unsigned v) by lia.
apply Z_to_bv_bv_unsigned.
Qed.

#[using="Type"] Lemma branch_eq_lit : forall (v : word) z,
(0 <= z < 2 ^ 64)%Z ->
branch_taken BC_EQ v (Z_to_bv 64 z) = Z.eqb (bv_unsigned v) z.
Proof.
intros v z Hz. cbn [branch_taken]. unfold bv_eqb. rewrite u_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma branch_ne_lit : forall (v : word) z,
(0 <= z < 2 ^ 64)%Z ->
branch_taken BC_NE v (Z_to_bv 64 z) = negb (Z.eqb (bv_unsigned v) z).
Proof.
intros v z Hz. cbn [branch_taken]. unfold bv_eqb. rewrite u_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma branch_ltu_lit_r : forall (v : word) z,
(0 <= z < 2 ^ 64)%Z ->
branch_taken BC_LTU v (Z_to_bv 64 z) = Z.ltb (bv_unsigned v) z.
Proof.
intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma branch_ltu_lit_l : forall (v : word) z,
(0 <= z < 2 ^ 64)%Z ->
branch_taken BC_LTU (Z_to_bv 64 z) v = Z.ltb z (bv_unsigned v).
Proof.
intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma branch_geu_lit_r : forall (v : word) z,
(0 <= z < 2 ^ 64)%Z ->
branch_taken BC_GEU v (Z_to_bv 64 z) = negb (Z.ltb (bv_unsigned v) z).
Proof.
intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.

#[using="Type"] Lemma branch_geu_lit_l : forall (v : word) z,
(0 <= z < 2 ^ 64)%Z ->
branch_taken BC_GEU (Z_to_bv 64 z) v = negb (Z.ltb z (bv_unsigned v)).
Proof.
intros v z Hz. cbn [branch_taken]. unfold bv_ltu. rewrite u_small by lia. reflexivity.
Qed.
End FPGEN1.

Ltac split_scs :=
lazymatch goal with
| |- scs_denot _ _ _ [] => constructor
| |- scs_denot _ _ _ (_ :: _) => constructor; [| split_scs]
| |- Forall _ [] => constructor
| |- Forall _ (_ :: _) => constructor; [| split_scs]
end.

Ltac ground_mod :=
repeat match goal with
| |- context [ (?a mod ?b)%Z ] =>
lazymatch a with
| context [bv_unsigned _] => fail
| _ => lazymatch b with
| context [bv_unsigned _] => fail
| _ => let v := eval vm_compute in (a mod b)%Z in change ((a mod b)%Z) with v
end
end
end.

Ltac sc_unfold :=
unfold sc_denot, flat, estart, elenZ, adenot;
cbn [a_base a_off edenot ev eb vals_ev nth];
rewrite ?Z_to_bv_unsigned, ?bv_wrap64_mod; ground_mod.

Ltac lit_u :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
lazymatch z with
| context [bv_unsigned _] => fail
| _ => rewrite (u_small z) by (cbn; lia)
end
end.

Ltac sc_store :=
match goal with
| Hs : stk_ok _ _ _ _ |- store_ok _ _ (v_addi _ _) _ = true =>
apply (stk_ok_vaddi _ _ _ _ _ _ Hs); lia
| Hs : stk_ok _ _ _ _ |- store_ok _ _ (Z_to_bv 64 _) _ = true =>
apply (stk_ok_lit _ _ _ _ _ _ Hs); lia
end.

Ltac sc_auto extra :=
sc_unfold;
first [ lia
| sc_store
| extra
| match goal with |- _ /\ _ => repeat split; first [lia | sc_store | extra] end
| idtac ].

Ltac sym_run_tac segs fuel stops scr nx HR HK R' HR' Hlf Hms extra :=
lazymatch type of HR with
| regs_ok ?E ?sr ?regs =>
lazymatch type of HK with
| know_ok _ _ ?base ?kn =>
lazymatch goal with
| |- context [mkst regs (Z_to_bv 64 ?pc) base ?rom] =>
let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn nx) []) in
lazymatch r with
| (?ss', ?scs, ?scr') =>
let Hsc := fresh "Hsc" in
assert (Hsc : scs_denot segs base E scs);
[ split_scs; sc_auto extra
| destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E base rom regs
(eq_refl _) HR HK Hsc) as (R' & HR' & Hlf & Hms);
clear Hsc ]
end
end
end
end.
