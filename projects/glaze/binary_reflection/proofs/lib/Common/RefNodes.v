(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module ErrEscape.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.



End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section OmniWithSegs.
Variable segs : list Segment.










End OmniWithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AllErrorWithSegs.
Variable segs : list Segment.





End AllErrorWithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Section NoUnmodeledWithSegs.
Variable segs : list Segment.





End NoUnmodeledWithSegs.







End WithFP1.
End ErrEscape.
Require LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module FileSim.
(* [comment removed for export] *)

Import Stdlib.NArith.NArith Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.LinuxProcessSem.OmniRun.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec ErrEscape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma with_fds_fs : forall f m, m_fs (with_fds f m) = m_fs m.
Proof. reflexivity. Qed.
Lemma with_fds_halted : forall f m, m_halted (with_fds f m) = m_halted m.
Proof. reflexivity. Qed.
Lemma with_fds_fds : forall f m, m_fds (with_fds f m) = f.
Proof. reflexivity. Qed.




(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma adv_eff_ret : forall regs pc x8 mem rom r,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc; ms_svc_pending := Some x8;
       ms_resv := None; ms_fcsr := fp_csr; ms_mem := mem; ms_rom := rom |} (mkEffect r [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
  intros regs pc x8 mem rom r.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros apply_writes apply_zeros].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_sysno_si : forall segs ms x8, in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.
Lemma in_arg0_si : forall segs ms x8, in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.
Lemma in_arg1_si : forall segs ms x8, in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof. reflexivity. Qed.
Lemma in_arg2_si : forall segs ms x8, in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof. reflexivity. Qed.
Lemma in_mem_si : forall segs ms x8, in_mem (sys_input segs ms x8) = ms_read_byte ms.
Proof. reflexivity. Qed.
Lemma in_wmem_si : forall segs ms x8,
  in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms.
Proof. reflexivity. Qed.



















(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma length_file_read : forall data off count,
  length (file_read data off count)
  = Nat.min (word_to_nat count) (length data - word_to_nat off)%nat.
Proof.
  intros data off count. rewrite file_read_unguarded.
  rewrite length_firstn, length_skipn. reflexivity.
Qed.





(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mrb (segs : list Segment) (mem : word -> option byte)
    : word -> option byte :=
  fun a => match mem a with Some b => Some b | None => seg_rom segs a end.



(* [comment removed for export] *)
Lemma mrb_first : forall segs mem a n b rest,
  rdn segs mem a (S n) = Some (b :: rest) -> mrb segs mem a = Some b.
Proof.
  intros segs mem a n b rest H. unfold mrb. cbn [rdn] in H.
  destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end)
    as [b1|]; [|discriminate].
  destruct (rdn segs mem (a + 1) n) as [rest1|]; [|discriminate].
  injection H; intros; subst; congruence.
Qed.

(* [comment removed for export] *)
Lemma rdn_tail : forall segs mem a n b rest,
  rdn segs mem a (S n) = Some (b :: rest) -> rdn segs mem (a + 1) n = Some rest.
Proof.
  intros segs mem a n b rest H. cbn [rdn] in H.
  destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end)
    as [b1|]; [|discriminate].
  destruct (rdn segs mem (a + 1) n) as [rest1|]; [|discriminate].
  injection H; intros; subst; reflexivity.
Qed.

Lemma read_cstr_aux_of_rdn : forall segs str fuel mem a,
  (length str < fuel)%nat -> ~ In (Z_to_bv 8 0) str ->
  rdn segs mem a (length str + 1) = Some (str ++ [Z_to_bv 8 0]) ->
  read_cstr_aux (mrb segs mem) a fuel = CstrOk str.
Proof.
  intros segs str; induction str as [|b str IH]; intros fuel mem a Hf Hnz Hr.
  - cbn [length] in *. destruct fuel as [|fuel]; [lia|].
    assert (Hb0 : mrb segs mem a = Some (Z_to_bv 8 0))
      by (apply (mrb_first segs mem a 0 (Z_to_bv 8 0) []); exact Hr).
    cbn [read_cstr_aux]. rewrite Hb0. reflexivity.
  - cbn [length] in *. destruct fuel as [|fuel]; [lia|].
    cbn [read_cstr_aux]. cbn [app] in Hr.
    assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
    assert (Hfirst : mrb segs mem a = Some b)
      by (apply (mrb_first segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]));
          exact Hr).
    assert (Htail : rdn segs mem (a + 1) (length str + 1)
                    = Some (str ++ [Z_to_bv 8 0]))
      by (apply (rdn_tail segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]));
          exact Hr).
    rewrite Hfirst. rewrite (bv_eqb_neq b (Z_to_bv 8 0) Hb).
    rewrite (IH fuel mem (a + 1) ltac:(lia)
               ltac:(intro; apply Hnz; right; assumption) Htail).
    reflexivity.
Qed.

Lemma read_cstr_of_rdn : forall segs mem a str,
  (length str <= 4095)%nat -> ~ In (Z_to_bv 8 0) str ->
  rdn segs mem a (length str + 1) = Some (str ++ [Z_to_bv 8 0]) ->
  read_cstr (mrb segs mem) a = CstrOk str.
Proof.
  intros segs mem a str Hlen Hnz Hr.
  unfold read_cstr. apply read_cstr_aux_of_rdn; [|exact Hnz|exact Hr].
  change path_max with 4096%nat. lia.
Qed.

(* [comment removed for export] *)
Lemma read_cstr_aux_toolong_of_rdn : forall segs fuel bs mem a,
  length bs = fuel -> ~ In (Z_to_bv 8 0) bs ->
  rdn segs mem a fuel = Some bs ->
  read_cstr_aux (mrb segs mem) a fuel = CstrTooLong.
Proof.
  intros segs fuel; induction fuel as [|fuel IH]; intros bs mem a Hlen Hnz Hr;
    [reflexivity|].
  destruct bs as [|b bs]; [cbn in Hlen; lia|].
  cbn [read_cstr_aux].
  assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
  assert (Hfirst : mrb segs mem a = Some b)
    by (apply (mrb_first segs mem a fuel b bs); exact Hr).
  assert (Htail : rdn segs mem (a + 1) fuel = Some bs)
    by (apply (rdn_tail segs mem a fuel b bs); exact Hr).
  rewrite Hfirst. rewrite (bv_eqb_neq b (Z_to_bv 8 0) Hb).
  rewrite (IH bs mem (a + 1) ltac:(cbn in Hlen; lia)
             ltac:(intro; apply Hnz; right; assumption) Htail).
  reflexivity.
Qed.

Lemma read_cstr_toolong_of_rdn : forall segs mem a bs,
  length bs = 4096%nat -> ~ In (Z_to_bv 8 0) bs ->
  rdn segs mem a 4096%nat = Some bs ->
  read_cstr (mrb segs mem) a = CstrTooLong.
Proof.
  intros segs mem a bs Hlen Hnz Hr.
  unfold read_cstr. change path_max with 4096%nat.
  eapply read_cstr_aux_toolong_of_rdn; eauto.
Qed.




Section WithSegs.
Variable segs : list Segment.

Inductive to_fout : machine_state -> Model -> ((word * Fs.Fs) -> Prop) -> Prop :=
| tfo_exit : forall ms model x8 (U : (word * Fs.Fs) -> Prop),
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    (forall o, U o <-> o = (bv_and (ms_gpr ms 0) (Z_to_bv 64 255), m_fs model)) ->
    to_fout ms model U
| tfo_step : forall ms ms' model U,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_fout ms' model U ->
    to_fout ms model U
| tfo_sys : forall ms model x8
    (T : SyscallEffect -> Model -> (word * Fs.Fs) -> Prop)
    (U : (word * Fs.Fs) -> Prop),
    ms_svc_pending ms = Some x8 ->
    ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
    (exists eff model' evs,
        syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)) ->
    (forall eff model' evs,
        syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
        evs = [] /\ m_halted model' = None /\ m_vm_lazy model' = []) ->
    (forall eff model' evs,
        syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
        to_fout (advance_past_svc (apply_effect ms eff)) model' (T eff model')) ->
    (forall o, U o <->
       (exists eff model' evs,
          syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
          /\ T eff model' o)) ->
    to_fout ms model U.























End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma check_syscall_56 : forall segs ms x8 eff m,
  bv_unsigned x8 = 56%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_openat (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
                 (ms_gpr ms 2) eff m.
Proof.
  intros segs ms x8 eff m Hno.
  unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.

Lemma check_syscall_57 : forall segs ms x8 eff m,
  bv_unsigned x8 = 57%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_close (fd32 (ms_gpr ms 0)) eff m.
Proof.
  intros segs ms x8 eff m Hno.
  unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.

Lemma check_syscall_63 : forall segs ms x8 eff m,
  bv_unsigned x8 = 63%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_read (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
               (ms_gpr ms 2) eff m.
Proof.
  intros segs ms x8 eff m Hno.
  unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.




(* [comment removed for export] *)
Lemma ENOMEM_in_openat_errnos : In ENOMEM openat_errnos.
Proof. left. reflexivity. Qed.

Lemma openat_errno_range : forall e,
  In e openat_errnos -> (1 <= e)%Z /\ (e <= 4095)%Z.
Proof. intros e HIn. exact (errnos_ok_range openat_errnos e eq_refl HIn). Qed.

Lemma check_open_result_never_unmodeled : forall eff m mk,
  check_open_result eff m mk <> CheckUnmodeled.
Proof.
  intros [ret ws zs us cs copyins] m mk.
  unfold check_open_result, check_new_fd_result.
  destruct ws as [|? ?]; destruct zs as [|? ?]; destruct us as [|? ?];
    destruct cs as [|? ?];
    destruct copyins as [|? ?];
    try discriminate.
  destruct (errno_ret_in openat_errnos ret); [discriminate|].
  destruct (fd_lookup (m_fds m) ret); [discriminate|].
  destruct (bv_eqb ret (alloc_fd (m_fds m))); discriminate.
Qed.

Lemma check_open_result_ok_iff : forall eff m (mk : word -> Model) m' evs,
  check_open_result eff m mk = CheckOk m' evs <->
  ((exists e, In e openat_errnos /\ eff = mkEffect (errno_ret e) [] []
              /\ m' = m /\ evs = [])
   \/ (exists fd, fd_lookup (m_fds m) fd = None /\ fd = alloc_fd (m_fds m)
                  /\ eff = mkEffect fd [] [] /\ m' = mk fd /\ evs = [])).
Proof.
  intros [ret ws zs us cs copyins] m mk m' evs.
  unfold check_open_result, check_new_fd_result. split.
  - intro H.
    destruct ws as [|? ?]; [|discriminate].
    destruct zs as [|? ?]; [|discriminate].
    destruct us as [|? ?]; [|discriminate].
    destruct cs as [|? ?]; [|discriminate].
    destruct copyins as [|? ?]; [|discriminate].
    destruct (errno_ret_in openat_errnos ret) eqn:Herr; try rewrite Herr in H.
    + inversion H; subst.
      apply errno_ret_in_true in Herr. destruct Herr as (e & HIn & ->).
      left. exists e. auto.
    + destruct (fd_lookup (m_fds m) ret) eqn:Hlk; try rewrite Hlk in H;
        [discriminate|].
      destruct (bv_eqb ret (alloc_fd (m_fds m))) eqn:Heq; try rewrite Heq in H;
        [|discriminate].
      inversion H; subst.
      right. exists ret. apply bv_eqb_eq in Heq. auto.
  - intros [ (e & HIn & Heff & -> & ->)
           | (fd & Hlk & Heq & Heff & -> & ->) ].
    + inversion Heff; subst.
      rewrite (errno_ret_in_intro _ e HIn). reflexivity.
    + inversion Heff; subst.
      rewrite errno_ret_in_alloc_fd by reflexivity.
      rewrite Hlk, bv_eqb_refl. reflexivity.
Qed.

Definition open_copyins (ms : machine_state) : list (word * nat) :=
  [(ms_gpr ms 1,
    cstr_access_len_aux (ms_read_byte ms) (ms_gpr ms 1) path_max)].

Definition check_open_result_copyins (reads : list (word * nat))
    (eff : SyscallEffect) (m : Model) (mk : word -> Model) : check_result :=
  check_copyins reads eff (check_open_result (clear_copyins eff) m mk).

Lemma effect_from_copyins_and_clear : forall eff reads core,
  eff_copyins eff = reads -> clear_copyins eff = core ->
  eff = with_copyins reads core.
Proof.
  intros [ret ws zs us cs copyins] reads core Hreads Hcore.
  cbn [eff_copyins] in Hreads. subst copyins.
  unfold clear_copyins, with_copyins in Hcore |- *.
  cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies] in Hcore |- *.
  inversion Hcore. reflexivity.
Qed.

Lemma check_open_result_copyins_never_unmodeled : forall reads eff m mk,
  check_open_result_copyins reads eff m mk <> CheckUnmodeled.
Proof.
  intros reads eff m mk.
  unfold check_open_result_copyins, check_copyins.
  destruct (access_ranges_eqb (eff_copyins eff) reads);
    [apply check_open_result_never_unmodeled|discriminate].
Qed.

Lemma check_open_result_copyins_ok_iff :
  forall reads eff m (mk : word -> Model) m' evs,
  check_open_result_copyins reads eff m mk = CheckOk m' evs <->
  ((exists e, In e openat_errnos /\
      eff = with_copyins reads (mkEffect (errno_ret e) [] []) /\
      m' = m /\ evs = [])
   \/ (exists fd, fd_lookup (m_fds m) fd = None /\
      fd = alloc_fd (m_fds m) /\
      eff = with_copyins reads (mkEffect fd [] []) /\
      m' = mk fd /\ evs = [])).
Proof.
  intros reads eff m mk m' evs.
  unfold check_open_result_copyins, check_copyins.
  destruct (access_ranges_eqb (eff_copyins eff) reads) eqn:Hreads.
  - apply access_ranges_eqb_eq in Hreads.
    rewrite check_open_result_ok_iff. split.
    + intros [(e & HIn & Hcore & -> & ->)
             | (fd & Hlk & Heq & Hcore & -> & ->)].
      * left. exists e. repeat split; try assumption.
        eapply effect_from_copyins_and_clear; eassumption.
      * right. exists fd. repeat split; try assumption.
        eapply effect_from_copyins_and_clear; eassumption.
    + intros [(e & HIn & Heff & -> & ->)
             | (fd & Hlk & Heq & Heff & -> & ->)].
      * left. exists e. repeat split; try assumption.
        rewrite Heff. reflexivity.
      * right. exists fd. repeat split; try assumption.
        rewrite Heff. reflexivity.
  - split; [discriminate|].
    intros [(e & _ & Heff & _)
           | (fd & _ & _ & Heff & _)].
    all: rewrite Heff in Hreads; cbn [eff_copyins with_copyins] in Hreads;
      pose proof (proj2 (access_ranges_eqb_eq reads reads) eq_refl) as Htrue;
      congruence.
Qed.

Lemma check_copyins_after_ret_only : forall reads eff r m evs,
  Prelude.check_copyins_after reads eff
      (check_ret_only (clear_copyins eff) r m evs) =
  check_ret_only_copyins reads eff r m evs.
Proof.
  intros reads eff r m evs.
  unfold Prelude.check_copyins_after, check_ret_only_copyins.
  destruct (check_ret_only (clear_copyins eff) r m evs) eqn:Hresult.
  - reflexivity.
  - unfold check_copyins.
    destruct (access_ranges_eqb (eff_copyins eff) reads); reflexivity.
  - exfalso. now apply check_ret_only_no_unmodeled in Hresult.
Qed.

(* [comment removed for export] *)
Lemma openat_rd_check : forall segs ms x8 model p d,
  bv_unsigned x8 = 56%Z ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = false ->
  Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z ->
  openat_plain_name p = true ->
  fs_lookup (m_fs model) p = Some d ->
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_open_result_copyins (open_copyins ms) eff model
        (fun fd => with_fds (fd_insert (m_fds model) fd
                               (FdFile p (Z_to_bv 64 0))) model).
Proof.
  intros segs ms x8 model p d Hno Hdirfd Hpath Hpe Hfl Hdot Hfs eff.
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
  unfold check_open_result_copyins, open_copyins.
  destruct (check_open_result (clear_copyins eff) model
    (fun fd : word =>
       with_fds
         (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model))
    eqn:Hresult.
  - reflexivity.
  - reflexivity.
  - exfalso. now apply check_open_result_never_unmodeled in Hresult.
Qed.



(* [comment removed for export] *)
Lemma openat_toolong_check : forall segs ms x8 model,
  bv_unsigned x8 = 56%Z ->
  modeled_open_flags (ms_gpr ms 2) = true ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrTooLong ->
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_ret_only_copyins (open_copyins ms) eff
        (errno_ret ENAMETOOLONG) model [].
Proof.
  intros segs ms x8 model Hno Hfl Hpath eff.
  rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
  rewrite Hfl. cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, Hpath.
  unfold check_ret_only_copyins, open_copyins.
  destruct (check_ret_only (clear_copyins eff) (errno_ret ENAMETOOLONG)
    model []) eqn:Hresult.
  - reflexivity.
  - unfold check_copyins.
    destruct (access_ranges_eqb (eff_copyins eff)
      [(ms_gpr ms 1,
        cstr_access_len_aux (ms_read_byte ms) (ms_gpr ms 1) path_max)]);
      reflexivity.
  - exfalso. now apply check_ret_only_no_unmodeled in Hresult.
Qed.

Section OpenNodes.
Variable segs : list Segment.



















End OpenNodes.






End WithFP1.
End FileSim.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CfgStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module Nodes.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition halt_ev (m' : Model) (code : word) : event :=
  match m_killed m' with
  | Some sig => KillEv sig (m_fs m')
  | None => ExitEv code (m_fs m')
  end.

Lemma sstep_svc_inv : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  sstep segs (mkCfg ms model) e st ->
  (exists eff model' evs,
      check_syscall (sys_input segs ms x8) eff model = CheckOk model' evs
      /\ ((exists model'', m_halted model' = None /\ e = evs
             /\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
             /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
          \/ (m_halted model' = None /\ e = []
              /\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
              /\ st = SError)
          \/ (exists code, m_halted model' = Some code
              /\ e = evs ++ [halt_ev model' code]
              /\ st = SNext (mkCfg ms model'))))
  \/ (exists eff, check_syscall (sys_input segs ms x8) eff model = CheckUnmodeled
      /\ e = [] /\ st = SError).
Proof.
  intros ms model x8 e st Hsvc Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + left. eexists. repeat split; eauto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. left. repeat split; auto.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. right. eexists. repeat split; eauto.
      unfold halt_ev. match goal with Hk : m_killed _ = None |- _ => rewrite Hk end. reflexivity.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. right.
      match goal with Hk : m_killed ?mm = Some _ |- _ =>
        destruct (m_halted mm) as [code|] eqn:Hhc;
          [| rewrite (m_killed_of_m_halted_none _ Hhc) in Hk; discriminate Hk];
        exists code; split; [reflexivity | split; [unfold halt_ev; rewrite Hk; reflexivity | reflexivity]]
      end.
  - (* [comment removed for export] *)
    match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    right. exists (mkEffect (Z_to_bv 64 0) [] []). split; [|split; reflexivity].
    apply check_syscall_err_iff. assumption.
Qed.

Lemma sstep_cfg_svc_inv : forall ms model x8 e st,
  ms_svc_pending ms = Some x8 ->
  sstep_cfg segs CfgStep.kit_cfg (mkCfg ms model) e st ->
  (exists eff model' evs,
      check_syscall (sys_input segs ms x8) eff model = CheckOk model' evs
      /\ ((exists model'', m_halted model' = None /\ e = evs
             /\ ~ spurious_refusal_cfg CfgStep.kit_cfg (sys_input segs ms x8) model eff
             /\ materialize_model_accesses model' (syscall_effect_accesses eff) = Some model''
             /\ st = SNext (mkCfg (advance_past_svc (apply_effect ms eff)) model''))
          \/ (m_halted model' = None /\ e = []
              /\ ~ spurious_refusal_cfg CfgStep.kit_cfg (sys_input segs ms x8) model eff
              /\ materialize_model_accesses model' (syscall_effect_accesses eff) = None
              /\ st = SError)
          \/ (exists code, m_halted model' = Some code
              /\ e = evs ++ [halt_ev model' code]
              /\ st = SNext (mkCfg ms model'))))
  \/ (exists eff, check_syscall (sys_input segs ms x8) eff model = CheckUnmodeled
      /\ e = [] /\ st = SError).
Proof.
  intros ms model x8 e st Hsvc Hss.
  inversion Hss; subst; try congruence.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + left. eexists. repeat split; eauto.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. left. repeat split; auto.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. right. eexists. repeat split; eauto.
      unfold halt_ev. match goal with Hk : m_killed _ = None |- _ => rewrite Hk end. reflexivity.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    left. eexists _, _, _. split.
    + apply check_syscall_ok_iff. eassumption.
    + right. right.
      match goal with Hk : m_killed ?mm = Some _ |- _ =>
        destruct (m_halted mm) as [code|] eqn:Hhc;
          [| rewrite (m_killed_of_m_halted_none _ Hhc) in Hk; discriminate Hk];
        exists code; split; [reflexivity | split; [unfold halt_ev; rewrite Hk; reflexivity | reflexivity]]
      end.
  - match goal with H : ms_svc_pending ms = Some ?y |- _ =>
      rewrite Hsvc in H; inversion H; subst end.
    right. exists (mkEffect (Z_to_bv 64 0) [] []). split; [|split; reflexivity].
    apply check_syscall_err_iff. assumption.
Qed.

Lemma node_chk_cfg : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     (exists i, eff = effs i /\ m' = ms' i /\ ev = evs i)
     \/ (refusal_b (sys_input segs ms x8) model (eff_ret eff) = true /\ m_halted m' = None
         /\ injected_family_off CfgStep.kit_cfg (sys_input segs ms x8) = true
         /\ exists i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false)) ->
  ((forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false)
   \/ (forall i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = true)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, materialize_model_accesses (ms' i) (syscall_effect_accesses (effs i)) = Some (ms' i)) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hcls Hnu Hh' Hmat.
  assert (Hns : forall i, ~ spurious_refusal_cfg CfgStep.kit_cfg (sys_input segs ms x8) model (effs i)).
  { intros i. destruct Hcls as [Hall | Hall].
    - apply spurious_refusal_not_refusal. apply Hall.
    - intros (_ & _ & (eff' & m'' & evs' & Hsp & Hnr)).
      apply check_syscall_ok_iff in Hsp.
      destruct (Hinv _ _ _ Hsp) as [(j & -> & _ & _) | (Hr & _)];
        [rewrite (Hall j) in Hnr | rewrite Hr in Hnr]; discriminate. }
  assert (Hsp : forall eff, refusal_b (sys_input segs ms x8) model (eff_ret eff) = true ->
             injected_family_off CfgStep.kit_cfg (sys_input segs ms x8) = true ->
             (exists i, refusal_b (sys_input segs ms x8) model (eff_ret (effs i)) = false) ->
             spurious_refusal_cfg CfgStep.kit_cfg (sys_input segs ms x8) model eff).
  { intros eff Hr Hoff (i & Hi). split; [exact Hoff | split; [exact Hr |]].
    exists (effs i), (ms' i), (evs i). split; [apply check_syscall_ok_iff; exact (Hok i) | exact Hi]. }
  split.
  - intros i. apply (sstep_cfg_syscall segs CfgStep.kit_cfg ms model x8 (effs i) (ms' i) (ms' i) (evs i) Hh Hsvc).
    + apply check_syscall_ok_iff. exact (Hok i).
    + exact (Hns i).
    + exact (Hh' i).
    + exact (Hmat i).
  - intros e st Hss.
    destruct (sstep_cfg_svc_inv ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hnsp & Hm & ->) | [(Hh2 & -> & Hnsp & Hm & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as [(i & -> & -> & ->) | (Hr & _ & Hoff & Hex)].
      * rewrite (Hmat i) in Hm. injection Hm as <-. exists i. split; reflexivity.
      * exfalso. exact (Hnsp (Hsp eff Hr Hoff Hex)).
    + destruct (Hinv _ _ _ Hc) as [(i & -> & -> & ->) | (Hr & _ & Hoff & Hex)].
      * rewrite (Hmat i) in Hm. discriminate.
      * exfalso. exact (Hnsp (Hsp eff Hr Hoff Hex)).
    + destruct (Hinv _ _ _ Hc) as [(i & -> & -> & ->) | (_ & Hh3 & _)].
      * rewrite Hh' in Hh2. discriminate.
      * rewrite Hh3 in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

(* [comment removed for export] *)
Lemma sstep_of_check : forall ms model x8 eff m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  sstep segs (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hh' Hlazy.
  apply (sstep_syscall segs ms model x8 eff m' m' evs Hh Hsvc).
  - apply check_syscall_ok_iff. exact Hc.
  - exact Hh'.
  - apply materialize_model_accesses_no_lazy. exact Hlazy.
Qed.

(* [comment removed for export] *)
Lemma node_chk_ev_u : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  CfgStep.node_ok_u segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hinv Hnu Hh' Hlazy. split.
  - intros i. apply (sstep_of_check ms model x8); auto.
  - intros e st Hss.
    destruct (sstep_svc_inv ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat.
      injection Hmat as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (Hlazy i)) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite Hh' in Hh2. discriminate.
    + exfalso. exact (Hnu eff Hc).
Qed.

Lemma node_chk_ev : forall ms model x8 (I : Type)
    (effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  CfgStep.alloc_no_b (bv_unsigned x8) = false ->
  (forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
  (forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
     exists i, eff = effs i /\ m' = ms' i /\ ev = evs i) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  (forall i, m_halted (ms' i) = None) ->
  (forall i, m_vm_lazy (ms' i) = []) ->
  node_ok segs (mkCfg ms model) I evs
          (fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hna Hok Hinv Hnu Hh' Hlazy.
  apply node_ok_of_u; [exact (CfgStep.kit_pending_on_sysno segs ms model x8 _ Hsvc eq_refl Hna) |].
  apply (node_chk_ev_u ms model x8 I effs ms' evs); assumption.
Qed.


(* [comment removed for export] *)
Lemma node_det : forall ms model x8 eff0 m0 evs0,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff m' evs,
     check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
     (eff = eff0 /\ m' = m0 /\ evs = evs0)) ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
  m_halted m0 = None ->
  m_vm_lazy m0 = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs0)
          (fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hnu Hh0 Hlazy0.
  apply node_ok_of_u_unit; [| exact Hh0].
  apply (node_chk_ev_u ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
  - intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
  - intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exists tt. auto.
  - exact Hnu.
  - intros []; exact Hh0.
  - intros []; exact Hlazy0.
Qed.

(* [comment removed for export] *)
Lemma node_ret_only : forall ms model x8 r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only eff r m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
  intros ms model x8 r m' evs Hh Hsvc Hchk Hh' Hlazy.
  rewrite <- (apply_effect_no_write ms r).
  apply (node_det ms model x8 (mkEffect r [] []) m' evs Hh Hsvc).
  - intros eff m'' evs'. rewrite Hchk. apply check_ret_only_ok_iff.
  - intros eff. rewrite Hchk. apply check_ret_only_no_unmodeled.
  - exact Hh'.
  - exact Hlazy.
Qed.

(* [comment removed for export] *)
Lemma node_ret_only_copyins : forall ms model x8 reads r m' evs,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_ret_only_copyins reads eff r m' evs) ->
  m_halted m' = None ->
  m_vm_lazy m' = [] ->
  node_ok segs (mkCfg ms model) unit (fun _ => evs)
          (fun _ => mkCfg (advance_past_svc (set_gpr0 ms r)) m').
Proof.
  intros ms model x8 reads r m' evs Hh Hsvc Hchk Hh' Hlazy.
  rewrite <- (apply_effect_copyins_no_write ms r reads).
  apply (node_det ms model x8 (with_copyins reads (mkEffect r [] [])) m' evs Hh Hsvc).
  - intros eff m'' evs'. rewrite Hchk. apply check_ret_only_copyins_ok_iff.
  - intros eff. rewrite Hchk. apply check_ret_only_copyins_no_unmodeled.
  - exact Hh'.
  - exact Hlazy.
Qed.








(* [comment removed for export] *)
Definition open_I (model : Model) : Type := {e : Z | In e openat_errnos} + unit.

Definition open_nx (ms : machine_state) (model : Model) (mk : word -> Model)
  (i : open_I model) : config :=
  match i with
  | inl (exist _ e _) => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model
  | inr _ => mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                   (mk (alloc_fd (m_fds model)))
  end.

Lemma node_open : forall ms model x8 reads (mk : word -> Model),
  m_halted model = None ->
  m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  (forall fd, m_vm_lazy (mk fd) = []) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  CfgStep.alloc_no_b (bv_unsigned x8) = false ->
  node_ok segs (mkCfg ms model) (open_I model) (fun _ => []) (open_nx ms model mk).
Proof.
  intros ms model x8 reads mk Hh Hlazy Hsvc Hchk Hmk Hmklazy Hfree Hna.
  apply node_ok_of_u; [exact (CfgStep.kit_pending_on_sysno segs ms model x8 _ Hsvc eq_refl Hna) |]. split.
  - intros [[e He] | []]; cbn [open_nx].
    + rewrite <- (apply_effect_copyins_no_write ms (errno_ret e) reads).
      apply (sstep_of_check ms model x8); [exact Hh | exact Hsvc | | exact Hh | exact Hlazy].
      rewrite Hchk. apply check_open_result_copyins_ok_iff. left. exists e. auto.
    + rewrite <- (apply_effect_copyins_no_write ms (alloc_fd (m_fds model)) reads).
      apply (sstep_of_check ms model x8); [exact Hh | exact Hsvc | | apply Hmk | apply Hmklazy].
      rewrite Hchk. apply check_open_result_copyins_ok_iff.
      right. exists (alloc_fd (m_fds model)). auto.
  - intros e st Hss.
    destruct (sstep_svc_inv ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. injection Hmat as <-.
        exists (inl (exist _ er Her)). cbn [open_nx].
        rewrite apply_effect_copyins_no_write. split; reflexivity.
      * subst fd. rewrite (materialize_model_accesses_no_lazy _ _ (Hmklazy _)) in Hmat.
        injection Hmat as <-.
        exists (inr tt). cbn [open_nx]. rewrite apply_effect_copyins_no_write. split; reflexivity.
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * rewrite (materialize_model_accesses_no_lazy _ _ Hlazy) in Hmat. discriminate.
      * rewrite (materialize_model_accesses_no_lazy _ _ (Hmklazy _)) in Hmat. discriminate.
    + rewrite Hchk in Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(er & Her & -> & -> & ->) | (fd & Hlk & Heq & -> & -> & ->)].
      * congruence.
      * rewrite Hmk in Hh2. discriminate.
    + exfalso. rewrite Hchk in Hc. exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hc).
Qed.


End WithSegs.
End Nodes.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AgentNodes.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition epend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
    (x8 : word) : machine_state :=
  {| ms_regs := regs; ms_fregs := fp_regs; ms_pc_val := pc;  (* [comment removed for export] *)
     ms_svc_pending := Some x8; ms_resv := None; ms_fcsr := fp_csr;
     ms_mem := mem; ms_rom := rom |}.

Lemma step_ecall_epend : forall segs regs pc mem rom w,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom)
  = MachineOk (epend regs pc mem rom (getr regs 17)).
Proof. intros. unfold epend. eapply step_ecall; eassumption. Qed.

Lemma epend_svc : forall regs pc mem rom x8, ms_svc_pending (epend regs pc mem rom x8) = Some x8.
Proof. reflexivity. Qed.

Lemma ms_gpr_epend0 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 0 = getr regs 10.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_0. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend1 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 1 = getr regs 11.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_1. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend2 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 2 = getr regs 12.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_2. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma arg_reg_3 : Z_to_bv 5 (10 + Z.of_nat 3) = (13 : reg). Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_4 : Z_to_bv 5 (10 + Z.of_nat 4) = (14 : reg). Proof. apply bv_eq. reflexivity. Qed.
Lemma arg_reg_5 : Z_to_bv 5 (10 + Z.of_nat 5) = (15 : reg). Proof. apply bv_eq. reflexivity. Qed.
Lemma ms_gpr_epend3 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 3 = getr regs 13.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_3. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend4 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 4 = getr regs 14.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_4. symmetry. apply getr_nz. reg_neq_tac. Qed.
Lemma ms_gpr_epend5 : forall regs pc mem rom x8, ms_gpr (epend regs pc mem rom x8) 5 = getr regs 15.
Proof. intros. unfold ms_gpr. cbn [ms_regs epend]. rewrite arg_reg_5. symmetry. apply getr_nz. reg_neq_tac. Qed.

Lemma ms_read_byte_epend : forall segs regs pc mem x8,
  ms_read_byte (epend regs pc mem (seg_rom segs) x8) = mrb segs mem.
Proof. reflexivity. Qed.




Lemma adv_set_epend : forall regs pc mem rom x8 v,
  advance_past_svc (set_gpr0 (epend regs pc mem rom x8) v)
  = mkst (regupd regs 10 v) (v_addi pc 4) mem rom.
Proof. intros. unfold epend. apply adv_set. Qed.

Lemma adv_eff_ret_epend : forall regs pc mem rom x8 r,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. intros. unfold epend. apply adv_eff_ret. Qed.


(* [comment removed for export] *)
Lemma rz_sys : forall segs regs pc mem rom model w T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros segs regs pc mem rom model w T Hh Hlazy HF HE Hc.
  eapply rz_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hc].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bv_and_255_small : forall code, (0 <= code < 256)%Z ->
  bv_and (Z_to_bv 64 code) (Z_to_bv 64 255) = Z_to_bv 64 code.
Proof.
  intros code Hc. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by lia.
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

End AgentNodes.
Module LibWritev.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg Nodes FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib AgentNodes.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance libwritev_fx : PropExec.FPState := PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.

Lemma bv_add_Zform : forall (a b : word), a + b = Z_to_bv 64 (bv_unsigned a + bv_unsigned b).
Proof.
  intros a b. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. reflexivity.
Qed.

Lemma word_to_nat_Z : forall z, (0 <= z < 2^64)%Z -> word_to_nat (Z_to_bv 64 z) = Z.to_nat z.
Proof.
  intros z Hz. unfold word_to_nat. rewrite Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 z) by (change (bv_modulus 64) with (2^64)%Z; lia). reflexivity.
Qed.

Lemma u64_roundtrip' : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma access_okb_of_le : forall (b : word) (n : Z),
  (0 <= n)%Z -> (bv_unsigned b + n <= TASK_SIZE)%Z -> access_okb b n = true.
Proof.
  intros b n Hn H. unfold access_okb. pose proof (bv_unsigned_in_range 64 b) as [Hb _].
  apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma check_syscall_writev : forall i eff m,
  bv_unsigned (in_sysno i) = 66%Z ->
  check_syscall i eff m = check_writev i (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) eff m.
Proof. intros i eff m H. unfold check_syscall. rewrite H. reflexivity. Qed.



Section WithSegs.
Variable segs : list Segment.

Lemma read_u64_rdn : forall ms a v,
  ms_rom ms = seg_rom segs ->
  rdn segs (ms_mem ms) a 8%nat = Some (word_to_le_bytes 8 v) ->
  read_u64 (ms_read_byte ms) a = Some v.
Proof.
  intros ms a v Hrom H. unfold read_u64.
  rewrite read_bytes_map_read_byte, (ms_read_bytes_rdn segs) by exact Hrom.
  change (word_to_nat (Z_to_bv 64 8)) with 8%nat. rewrite H.
  f_equal. apply le_word_v. apply bytes_le_to_Z_8.
Qed.

Lemma read_bytes_map_rdn : forall ms a (n : word) bs,
  ms_rom ms = seg_rom segs ->
  rdn segs (ms_mem ms) a (word_to_nat n) = Some bs ->
  read_bytes_map (ms_read_byte ms) a n = Some bs.
Proof.
  intros ms a n bs Hrom H.
  rewrite read_bytes_map_read_byte, (ms_read_bytes_rdn segs) by exact Hrom. exact H.
Qed.

(* [comment removed for export] *)
Fixpoint iov_array (mem : word -> option byte) (iov : word) (iovs : list (word * word)) : Prop :=
  match iovs with
  | [] => True
  | (b, n) :: r =>
      rdn segs mem iov 8%nat = Some (word_to_le_bytes 8 b)
      /\ rdn segs mem (Z_to_bv 64 (bv_unsigned iov + 8)) 8%nat = Some (word_to_le_bytes 8 n)
      /\ (bv_unsigned n < 2 ^ 63)%Z
      /\ iov_array mem (Z_to_bv 64 (bv_unsigned iov + 16)) r
  end.

Lemma read_iovec_entry_of_array : forall ms b n r iov,
  ms_rom ms = seg_rom segs ->
  iov_array (ms_mem ms) iov ((b, n) :: r) ->
  read_iovec_entry (ms_read_byte ms) iov = IovEntry b n.
Proof.
  intros ms b n r iov Hrom (Hb & Hn & Hlt & _). unfold read_iovec_entry.
  rewrite (read_u64_rdn ms iov b Hrom Hb).
  rewrite bv_add_Zform. change (bv_unsigned (8 : word)) with 8%Z.
  rewrite (read_u64_rdn ms _ n Hrom Hn).
  rewrite (proj2 (Z.leb_gt _ _) Hlt). reflexivity.
Qed.

Lemma copy_iovecs_of_array : forall ms iovs iov,
  ms_rom ms = seg_rom segs ->
  iov_array (ms_mem ms) iov iovs ->
  copy_iovecs_aux (ms_read_byte ms) iov (length iovs) = ImpOk iovs.
Proof.
  intros ms iovs; induction iovs as [|[b n] r IH]; intros iov Hrom Ha; [reflexivity|].
  cbn [length copy_iovecs_aux].
  rewrite (read_iovec_entry_of_array ms b n r iov Hrom Ha).
  destruct Ha as (_ & _ & _ & Hr).
  rewrite bv_add_Zform. change (bv_unsigned (16 : word)) with 16%Z.
  rewrite (IH _ Hrom Hr). reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint iov_bufs (mem : word -> option byte) (iovs : list (word * word)) (bss : list (list byte)) : Prop :=
  match iovs, bss with
  | [], [] => True
  | (b, n) :: r, bs :: bss' => rdn segs mem b (word_to_nat n) = Some bs /\ iov_bufs mem r bss'
  | _, _ => False
  end.

Lemma gather_of_bufs : forall ms iovs bss,
  ms_rom ms = seg_rom segs ->
  iov_bufs (ms_mem ms) iovs bss ->
  gather_iovecs (ms_read_byte ms) iovs = Some (concat bss).
Proof.
  intros ms iovs; induction iovs as [|[b n] r IH]; intros [|bs bss] Hrom Hb; cbn in Hb; try contradiction.
  - reflexivity.
  - destruct Hb as [H1 H2]. cbn [gather_iovecs concat].
    rewrite (read_bytes_map_rdn ms b n bs Hrom H1), (IH bss Hrom H2). reflexivity.
Qed.

Lemma cap_iovecs_id : forall iovs left,
  (iovs_total iovs <= left)%Z -> cap_iovecs_aux iovs left = iovs.
Proof.
  induction iovs as [|[b n] r IH]; intros left H; [reflexivity|].
  cbn [cap_iovecs_aux]. cbn [iovs_total] in H. pose proof (iovs_total_nonneg r).
  rewrite Z.min_r by lia. rewrite u64_roundtrip', IH by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint iov_bufs_ok (iovs : list (word * word)) : Prop :=
  match iovs with
  | [] => True
  | (b, n) :: r => (bv_unsigned b + bv_unsigned n <= TASK_SIZE)%Z /\ iov_bufs_ok r
  end.

Lemma iovs_access_okb_of_ok : forall iovs, iov_bufs_ok iovs -> iovs_access_okb iovs = true.
Proof.
  induction iovs as [|[b n] r IH]; intros H; [reflexivity|].
  destruct H as [Hb Hr]. unfold iovs_access_okb. cbn [forallb fst snd].
  rewrite (access_okb_intro b n Hb). cbn [andb]. exact (IH Hr).
Qed.

(* [comment removed for export] *)
Lemma import_iovecs_of_array : forall ms iovs iov,
  ms_rom ms = seg_rom segs ->
  (1 <= length iovs <= 1024)%nat ->
  (bv_unsigned iov + 16 * Z.of_nat (length iovs) <= TASK_SIZE)%Z ->
  iov_array (ms_mem ms) iov iovs ->
  iov_bufs_ok iovs ->
  import_iovecs (ms_read_byte ms) iov (Z_to_bv 64 (Z.of_nat (length iovs))) = ImpOk iovs.
Proof.
  intros ms iovs iov Hrom Hcnt Hok Harr Hbok. unfold import_iovecs.
  destruct iovs as [|[b n] r]; [cbn in Hcnt; lia|].
  destruct r as [|[b2 n2] r2].
  - (* [comment removed for export] *)
    cbn [length] in *. change (Z.of_nat 1) with 1%Z in *.
    rewrite (proj2 (bv_eqb_eq _ _) eq_refl).
    rewrite (access_okb_of_le iov 16) by lia.
    rewrite (read_iovec_entry_of_array ms b n [] iov Hrom Harr).
    destruct Hbok as [Hb _]. pose proof (u64_range n).
    rewrite (access_okb_of_le b (Z.min (bv_unsigned n) MAX_RW_COUNT))
      by (unfold MAX_RW_COUNT in *; lia).
    reflexivity.
  - (* [comment removed for export] *)
    set (cnt := Z.of_nat (length ((b, n) :: (b2, n2) :: r2))) in *.
    assert (Hc2 : (2 <= cnt <= 1024)%Z) by (unfold cnt; cbn [length] in *; lia).
    assert (E1 : bv_eqb (Z_to_bv 64 cnt) (Z_to_bv 64 1) = false).
    { unfold bv_eqb. apply Z.eqb_neq. rewrite !u64_lit by lia. lia. }
    assert (E0 : bv_eqb (Z_to_bv 64 cnt) (Z_to_bv 64 0) = false).
    { unfold bv_eqb. apply Z.eqb_neq. rewrite !u64_lit by lia. lia. }
    rewrite E1, E0. rewrite u64_lit by lia.
    replace ((IOV_MAX <? cnt)%Z) with false by (symmetry; apply Z.ltb_ge; unfold IOV_MAX; lia).
    rewrite (access_okb_of_le iov (16 * cnt)) by lia.
    rewrite word_to_nat_Z by lia. unfold cnt. rewrite Nat2Z.id.
    rewrite (copy_iovecs_of_array ms _ iov Hrom Harr).
    rewrite (iovs_access_okb_of_ok _ Hbok). reflexivity.
Qed.









End WithSegs.
End LibWritev.
Require Stdlib.Logic.FunctionalExtensionality Stdlib.Lists.Finite.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module ShapeNodes.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.










(* [comment removed for export] *)
Lemma fd32_small : forall fd : word, (bv_unsigned fd < 2^32)%Z -> fd32 fd = fd.
Proof. exact fd32_id. Qed.




(* [comment removed for export] *)

Section Generic.
Variable segs : list Segment.








End Generic.




Section EcallState.
Context {fx : FPState}.





















(* [comment removed for export] *)
Lemma write_to_mem_wbytes : forall data mem a,
  write_to_mem mem a data = wbytes mem a data.
Proof. induction data as [|b data IH]; intros mem a; [reflexivity|]. cbn. apply IH. Qed.


End EcallState.
End ShapeNodes.
Require LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module SpecConsts.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


End SpecConsts.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.glaze.binary_reflection.lib.Common Require Import AllocEd.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.AsanCeil.  (* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib AgentNodes SpecConsts.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.






Lemma with_tid_halted : forall t m, m_halted (with_tid t m) = m_halted m.
Proof. intros t m. reflexivity. Qed.

Lemma with_tid_lazy : forall t m, m_vm_lazy (with_tid t m) = m_vm_lazy m.
Proof. intros t m. reflexivity. Qed.

Lemma with_vmmaps_lazy' : forall h m, m_vm_lazy (with_vmmaps h m) = m_vm_lazy m.
Proof. intros h m. reflexivity. Qed.

Lemma with_vmmaps_eta : forall m,
  with_vmmaps (m_vmmaps m) m = m.
Proof. intros m. destruct m as [? [? ? ?] ? ? ? ?]; reflexivity. Qed.

Lemma vmmaps_eta : forall h,
  mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) = h.
Proof. intros h. destruct h; reflexivity. Qed.

Lemma Z_to_bv_u_eq' : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof. intros a z ->. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma vm_forget_range_id : forall lo hi m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_forget_range lo hi m = m.
Proof.
  intros lo hi m Hl Hm. unfold vm_forget_range, with_vm_backing.
  rewrite Hl, Hm. cbn [maps_subtract List.filter].
  destruct m as [? [? l mt] ? ? ? ?]. cbn in Hl, Hm. subst. reflexivity.
Qed.


Lemma vm_forget_range_halted : forall lo hi m,
  m_halted (vm_forget_range lo hi m) = m_halted m.
Proof. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma mmap_check : forall ms x8 model eff,
  bv_unsigned x8 = 222%Z ->
  check_syscall (sys_input segs ms x8) eff model
  = check_mmap (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 4) (ms_gpr ms 5) eff model.
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

Lemma munmap_check : forall ms x8 model eff,
  bv_unsigned x8 = 215%Z ->
  check_syscall (sys_input segs ms x8) eff model = check_munmap (ms_gpr ms 0) (ms_gpr ms 1) eff model.
Proof. intros ms x8 model eff Hno. unfold check_syscall. rewrite in_sysno_sys_input, Hno. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive three : Type := T1 | T2 | T3.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma adv_ret_epend : forall regs pc mem rom x8 r,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof. intros. unfold epend. apply adv_eff_ret. Qed.

Lemma adv_zeros1_epend : forall regs pc mem rom x8 r a n,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [(a, n)] [] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (zfill a n mem) rom.
Proof.
  intros. unfold epend.
  assert (Hm : apply_zeros (apply_unmaps mem []) [(a, n)] = zfill a n mem).
  { cbn [apply_unmaps]. unfold zfill. exact (apply_zeros_one mem a n). }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_writes apply_copies].
  unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.

Lemma adv_unmaps1_epend : forall regs pc mem rom x8 r a n,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffectU r [] [] [(a, n)] [] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (unfill a n mem) rom.
Proof.
  intros. unfold epend.
  assert (Hm : apply_writes (apply_zeros (apply_unmaps mem [(a, n)]) []) [] = unfill a n mem).
  { cbn [apply_writes apply_zeros].
    apply functional_extensionality. intro x.
    unfold apply_unmaps, zeros_cover, unfill. cbn [existsb fst snd].
    rewrite orb_false_r. reflexivity. }
  unfold apply_effect, advance_past_svc, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros eff_unmaps eff_copies apply_copies].
  unfold mkst, regupd. rewrite b_npc4, Hm. reflexivity.
Qed.

Lemma adv_write1_epend : forall regs pc mem rom x8 r buf data,
  advance_past_svc (apply_effect (epend regs pc mem rom x8) (mkEffect r [(buf, data)] []))
  = mkst (regupd regs 10 r) (v_addi pc 4) (wbytes mem buf data) rom.
Proof. intros. unfold epend. rewrite adv_apply_write, write_to_mem_wbytes. reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma node_brk_u : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  CfgStep.node_ok_u segs (mkCfg ms model)
    {r : word | brk_resolution_ok model (ms_gpr ms 0) r}
    (fun _ => [])
    (fun i => mkCfg (advance_past_svc (apply_effect ms
                       (mkEffectU (proj1_sig i) []
                          (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
                          (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])))
                    (brk_model (ms_gpr ms 0) (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno. split.
  - intros [r Hr]. cbn [proj1_sig].
    pose proof (brk_ok_intro segs ms x8 model r Hno Hr) as Hspec.
    destruct (brk_step_shape segs ms x8 model _ _ _ Hh Hlazy Hno Hspec) as (_ & Hh' & _ & _ & Hlazy').
    apply (sstep_syscall segs ms model x8 _ _ _ [] Hh Hsvc Hspec Hh').
    apply materialize_model_accesses_no_lazy. rewrite Hlazy'. exact Hlazy.
  - intros e st Hss.
    destruct (sstep_brk_inv segs ms model x8 e st Hh Hlazy Hsvc Hno Hss) as (eff & model' & Hspec & -> & ->).
    apply (brk_ok_iff segs ms x8 model eff model' [] Hno) in Hspec.
    destruct Hspec as (Heff & _ & Hok & ->).
    exists (exist _ (eff_ret eff) Hok). cbn [proj1_sig]. rewrite <- Heff. split; reflexivity.
Qed.

Definition brk_nx (ms : machine_state) (model : Model)
    (i : {r : word | brk_resolution_ok model (ms_gpr ms 0) r}) : config :=
  mkCfg (advance_past_svc (apply_effect ms
           (mkEffectU (proj1_sig i) []
              (brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
              (brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])))
        (brk_model (ms_gpr ms 0) (proj1_sig i) model).

Lemma brk_nx_halted : forall ms model (x8 : word) i,
  m_halted model = None -> m_vm_lazy model = [] -> bv_unsigned x8 = 214%Z ->
  m_halted (cfg_model (brk_nx ms model i)) = None.
Proof.
  intros ms model x8 [r Hr] Hh Hlazy Hno. cbn [brk_nx cfg_model proj1_sig].
  pose proof (brk_ok_intro segs ms x8 model r Hno Hr) as Hspec.
  exact (proj1 (proj2 (brk_step_shape segs ms x8 model _ _ _ Hh Hlazy Hno Hspec))).
Qed.

Lemma brk_nx_refusal : forall ms model (x8 : word) i,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  CfgStep.child_refusal_b segs (mkCfg ms model) (brk_nx ms model i)
  = brk_refusal_b model (ms_gpr ms 0) (proj1_sig i).
Proof.
  intros ms model x8 i Hh Hlazy Hsvc Hno.
  pose proof (brk_nx_halted ms model x8 i Hh Hlazy Hno) as Hh'.
  destruct i as [r Hr]. unfold brk_nx in *. cbn [proj1_sig cfg_model] in *.
  rewrite (CfgStep.child_refusal_b_syscall segs ms model x8 _ _ Hsvc Hh').
  cbn [eff_ret]. rewrite (CfgStep.refusal_b_brk (sys_input segs ms x8) model r Hno).
  reflexivity.
Qed.

Lemma brk_refusal_b_moved : forall m (req r : word),
  r <> vm_brk (m_vmmaps m) -> brk_refusal_b m req r = false.
Proof.
  intros m req r Hne. unfold brk_refusal_b. cbv zeta.
  rewrite (bv_eqb_neq _ _ Hne). apply andb_false_r.
Qed.

Lemma brk_keep_ok : forall m req, brk_resolution_ok m req (vm_brk (m_vmmaps m)).
Proof.
  intros m req. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
  destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps m))))%Z%bool.
  - apply bv_eqb_refl.
  - destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps m)))%Z.
    + rewrite bv_eqb_refl, Bool.orb_true_r. reflexivity.
    + rewrite bv_eqb_refl, Bool.orb_true_r. cbn [andb].
      unfold Mmap.brk_grow_ok. rewrite Z.ltb_irrefl, Bool.andb_false_r. reflexivity.
Qed.

Lemma brk_only_keep : forall m req r,
  Mmap.brk_r_ok m req req = false -> brk_resolution_ok m req r -> r = vm_brk (m_vmmaps m).
Proof.
  intros m req r Eg Hr. unfold brk_resolution_ok, Mmap.brk_r_ok in *. cbv zeta in *.
  destruct (w_is0 req || (bv_unsigned req <? bv_unsigned (min_brk (m_vmmaps m))))%Z%bool.
  - apply bv_eqb_eq. exact Hr.
  - destruct (bv_unsigned req <? bv_unsigned (vm_brk (m_vmmaps m)))%Z.
    + rewrite bv_eqb_refl in Eg. discriminate Eg.
    + rewrite bv_eqb_refl in Eg. cbn [orb andb] in Eg.
      apply andb_true_iff in Hr as [Hr Hg]. apply orb_true_iff in Hr as [Hr | Hr];
        apply bv_eqb_eq in Hr; [subst r; rewrite Hg in Eg; discriminate Eg | exact Hr].
Qed.

Lemma brk_exact_inh : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
  exists i : {r : word | brk_resolution_ok model (ms_gpr ms 0) r},
    CfgStep.child_refusal_b segs (mkCfg ms model) (brk_nx ms model i) = false
    \/ (forall j, CfgStep.child_refusal_b segs (mkCfg ms model) (brk_nx ms model j) = true).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno.
  pose proof (brk_keep_ok model (ms_gpr ms 0)) as Hkeep.
  destruct (brk_refusal_b model (ms_gpr ms 0) (vm_brk (m_vmmaps model))) eqn:Ek.
  - destruct (Mmap.brk_r_ok model (ms_gpr ms 0) (ms_gpr ms 0)) eqn:Eg.
    + exists (exist _ (ms_gpr ms 0) Eg). left.
      rewrite (brk_nx_refusal ms model x8 _ Hh Hlazy Hsvc Hno). cbn [proj1_sig].
      apply brk_refusal_b_moved. intros E.
      unfold brk_refusal_b in Ek. cbv zeta in Ek. rewrite E, bv_eqb_refl in Ek.
      cbn [negb] in Ek. rewrite andb_true_r, andb_false_r in Ek. discriminate Ek.
    + exists (exist _ _ Hkeep). right. intros [r Hr].
      rewrite (brk_nx_refusal ms model x8 _ Hh Hlazy Hsvc Hno). cbn [proj1_sig].
      rewrite (brk_only_keep model _ r Eg Hr). exact Ek.
  - exists (exist _ _ Hkeep). left.
    rewrite (brk_nx_refusal ms model x8 _ Hh Hlazy Hsvc Hno). exact Ek.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma brk_r_ok_grow_cases : forall m req r,
  let h := m_vmmaps m in
  (0 < bv_unsigned req)%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
  (bv_unsigned (vm_brk h) <= bv_unsigned req)%Z ->
  brk_resolution_ok m req r <->
  (r = vm_brk h \/ (r = req /\ Mmap.brk_grow_ok m req req = true)).
Proof.
  intros m req r h Hpos Hs Hb.
  unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta. fold h.
  assert (E0 : w_is0 req = false).
  { unfold w_is0, bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
  rewrite E0. unfold min_brk.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [orb].
  rewrite (proj2 (Z.ltb_ge _ _)) by lia.
  rewrite andb_true_iff, orb_true_iff, !bv_eqb_eq. split.
  - intros [[-> | ->] Hg]; [right; auto | left; reflexivity].
  - intros [-> | [-> Hg]]; split; [right; reflexivity | | left; reflexivity | exact Hg].
    unfold Mmap.brk_grow_ok. fold h. rewrite Z.ltb_irrefl, andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_model_keep : forall m req,
  brk_model req (vm_brk (m_vmmaps m)) m = m.
Proof.
  intros m req. unfold brk_model, with_brk_next. cbv zeta.
  rewrite brk_unmaps_keep. cbn [forget_vm_ranges].
  unfold brk_model_next, brk_maps_next.
  rewrite Z.ltb_irrefl, andb_false_r, brk_grants_keep, brk_unmaps_keep.
  cbn [app maps_subtract_ranges fold_left]. rewrite vmmaps_eta. apply with_vmmaps_eta.
Qed.

(* [comment removed for export] *)
Lemma brk_model_grow_eq : forall m (d : Z),
  let h := m_vmmaps m in
  let b := vm_brk h in
  (0 < d)%Z -> (0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z ->
  brk_model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) m
  = with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
                   (vm_noaccess h) (vm_start_brk h)
                   (Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) m.
Proof.
  intros m d h b Hd Hb0 Hnw Hbal Hdal.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)).
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
  assert (Hreq0 : req <> Z_to_bv 64 0).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
  unfold brk_model, with_brk_next. cbv zeta. fold h. fold b.
  rewrite (brk_unmaps_grow req b) by lia. cbn [forget_vm_ranges].
  unfold brk_model_next, brk_maps_next. fold b.
  rewrite (proj2 (Z.ltb_ge (bv_unsigned req) (bv_unsigned b))) by lia. rewrite andb_false_r.
  rewrite (brk_grants_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
  cbn [app maps_subtract_ranges fold_left].
  replace (req - b) with (Z_to_bv 64 d); [reflexivity|].
  apply bv_eq. rewrite bv_sub_unsigned, Hureq.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). rewrite u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition noaccess_model (a n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                 ((a, n) :: vm_maps (m_vmmaps m))
                 ((a, n) :: vm_noaccess (m_vmmaps m))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.


(* [comment removed for export] *)
Definition grant_ok_na_pin (m : Model) (a : word) (n : Z) : bool :=
  (bv_unsigned a mod page_size =? 0)%Z && (0 <? bv_unsigned a)%Z
  && (bv_unsigned a + n <=? alloc_top (m_vmmaps m))%Z
  && region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n).




Lemma grant_na_pin_not_errno : forall m a n,
  (0 <= n)%Z -> grant_ok_na_pin m a n = true -> errno_ret_in mmap_errnos a = false.
Proof.
  intros m a n Hn Hg. unfold grant_ok_na_pin in Hg.
  apply andb_true_iff in Hg as [Hg _]. apply andb_true_iff in Hg as [Hg Htop]. apply Z.leb_le in Htop.
  apply errno_ret_in_below; [reflexivity|]. alloc_top_bounds. unfold two_pow_64 in *. lia.
Qed.



(* [comment removed for export] *)
Lemma errno_ret_in_when_false : forall b r, errno_ret_in mmap_errnos r = false -> errno_ret_in (mmap_errnos_when b) r = false.
Proof. intros [|] r H; [exact H | reflexivity]. Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mprotect_model (addr n : word) (m : Model) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                 (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                 (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m.

Lemma mprotect_model_next_eq : forall m addr n, mprotect_model_next m addr n = mprotect_model addr n m.
Proof. reflexivity. Qed.

Lemma check_syscall_226 : forall ms x8 eff m,
  bv_unsigned x8 = 226%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_mprotect (ms_gpr ms 0) (ms_gpr ms 1) (ms_gpr ms 2) eff m.
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.

Lemma mprotect_check : forall ms x8 model eff (addr : word) (len : Z),
  bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z ->
  ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len < two_pow_64)%Z ->
  ms_gpr ms 2 = Z_to_bv 64 3 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  check_syscall (sys_input segs ms x8) eff model
  = match eff with
    | mkEffectU r [] zs [] [] [] =>
        if errno_ret_in mprotect_errnos r   (* [comment removed for export] *)
        then match zs with [] => CheckOk model [] | _ => CheckReject end
        else if mprotect_budget_ok model addr n && w_is0 r && listNN_eqb zs [(addr, n)]
             then CheckOk (mprotect_model addr n model) []
             else CheckReject
    | _ => CheckReject
    end.
Proof.
  intros ms x8 model eff addr len Hno H0 Hal H1 Hlen Hnw H2 n Hna Hma.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; unfold two_pow_64 in Hlen'; lia).
  rewrite (check_syscall_226 ms x8 eff model Hno). unfold check_mprotect.
  rewrite H0, H2, Hu1.
  replace (mprotect_grows_conflict_b (Z_to_bv 64 3)) with false by (vm_compute; reflexivity).
  replace (mprotect_modeled_b (Z_to_bv 64 3)) with true by (vm_compute; reflexivity).
  rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0, bv_eqb. rewrite Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. apply Z.eqb_neq. lia. }
  rewrite E1. rewrite (proj2 (Z.leb_gt _ _)) by lia.
  cbv beta iota zeta. fold n. rewrite Hna, Hma. cbn [andb].
  destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
  destruct us; [| try (match goal with |- context [errno_ret_in ?es r] => destruct (errno_ret_in es r) end); reflexivity].
  destruct cs; [| try (match goal with |- context [errno_ret_in ?es r] => destruct (errno_ret_in es r) end); reflexivity].
  destruct ci; [| try (match goal with |- context [errno_ret_in ?es r] => destruct (errno_ret_in es r) end); reflexivity].
  reflexivity.
Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fixed_noaccess_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
                   ((addr, n) :: maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).

(* [comment removed for export] *)
Definition fixed_destroyed_model (addr n : word) (m : Model) : Model :=
  vm_forget_range (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n)
    (with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps m))
                   (maps_subtract (vm_maps (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
                   (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m))
                 (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m))) m).




(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma check_syscall_96 : forall ms x8 eff m,
  bv_unsigned x8 = 96%Z ->
  check_syscall (sys_input segs ms x8) eff m = check_set_tid_address eff m.
Proof. intros ms x8 eff m Hno. unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity. Qed.

Definition tid_I : Type := { t : word | (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z }.

Lemma one_tid_ok : (0 < bv_unsigned (Z_to_bv 64 1) < PID_MAX_ENVELOPE)%Z.
Proof. unfold PID_MAX_ENVELOPE. rewrite u64_lit by lia. lia. Qed.

Lemma node_set_tid : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
  m_tid model = None ->
  node_ok segs (mkCfg ms model) tid_I (fun _ => [])
    (fun i => mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Htid.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model =
     match eff with
     | mkEffectU ret [] [] [] [] [] =>
         if (0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z
         then CheckOk (with_tid ret model) [] else CheckReject
     | _ => CheckReject end).
  { intros eff. rewrite (check_syscall_96 ms x8 eff model Hno). unfold check_set_tid_address. rewrite Htid. reflexivity. }
  pose (effs := fun i : tid_I => mkEffectU (proj1_sig i) [] [] [] [] []).
  assert (Enx : forall i : tid_I,
    mkCfg (advance_past_svc (set_gpr0 ms (proj1_sig i))) (with_tid (proj1_sig i) model)
    = mkCfg (advance_past_svc (apply_effect ms (effs i))) (with_tid (proj1_sig i) model)).
  { intros [t Ht]. cbn [proj1_sig effs]. rewrite <- (apply_effect_no_write ms t). reflexivity. }
  apply node_ok_of_u; [exact (CfgStep.kit_pending_on_sysno segs ms model x8 96 Hsvc Hno eq_refl) |].
  split.
  - intros i. rewrite Enx. apply (sstep_of_check segs ms model x8); [exact Hh | exact Hsvc | | rewrite with_tid_halted; exact Hh | rewrite with_tid_lazy; exact Hlazy].
    destruct i as [t [Ht1 Ht2]]. subst effs. cbn [proj1_sig]. rewrite Hchk.
    rewrite (proj2 (Z.ltb_lt _ _) Ht1), (proj2 (Z.ltb_lt _ _) Ht2). reflexivity.
  - assert (Hinv : forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
              exists i : tid_I, eff = effs i /\ m' = with_tid (proj1_sig i) model /\ ev = []).
    { intros [ret ws zs us cs ci] m' ev Hc. rewrite Hchk in Hc.
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z) eqn:Eb; [|discriminate].
      apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
      injection Hc as <- <-. exists (exist _ ret (conj E1 E2)). repeat split; reflexivity. }
    intros e st Hss.
    destruct (sstep_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hmat & ->) | [(Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
         | (eff & Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans (with_tid_lazy _ model) Hlazy)) in Hmat.
      injection Hmat as <-. exists i. rewrite Enx. split; reflexivity.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->).
      rewrite (materialize_model_accesses_no_lazy _ _ (eq_trans (with_tid_lazy _ model) Hlazy)) in Hmat. discriminate.
    + destruct (Hinv _ _ _ Hc) as (i & -> & -> & ->). rewrite with_tid_halted in Hh2. congruence.
    + exfalso. rewrite Hchk in Hc. destruct eff as [ret ws zs us cs ci].
      destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
      destruct cs; [|discriminate]. destruct ci; [|discriminate].
      destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z); discriminate.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rz_exit_at : forall regs (pc : word) mem rom model w code,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
  getr regs 10 = code ->
  realizes segs (mkCfg (mkst regs pc mem rom) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs pc mem rom model w code HF HE Hh Hlazy H17 H10.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply rz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma vm_backing_used_simple : forall m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used m = vm_backed_bytes (m_vmmaps m).
Proof.
  intros m Hl Hm. unfold vm_backing_used. rewrite Hl, Hm. cbn [maps_subtract_all length Z.of_nat Z.mul]. unfold vm_backed_bytes. lia.
Qed.


(* [comment removed for export] *)
Lemma brk_grow_ok_aligned_intro : forall m d,
  let h := m_vmmaps m in
  let b := vm_brk h in
  (bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
  (0 < bv_unsigned b)%Z ->
  (bv_unsigned b + d <= alloc_ceiling)%Z -> init_sp_ok h ->
  region_free (vm_reserved h ++ vm_maps h) b (Z_to_bv 64 (d + page_size)) = true ->
  (vm_backing_used m + d <= vm_limit h)%Z ->
  Mmap.brk_grow_ok m (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true.
Proof.
  intros m d h b Hbal Hdal Hd Hb0 Hce Hisp Hrf Hlive.
  pose proof alloc_ceiling_val as Hcv. pose proof (u64_range b) as Hbr.
  pose proof (alloc_ceiling_le_alloc_top h Hisp) as Htop.
  assert (Hureq : bv_unsigned (Z_to_bv 64 (bv_unsigned b + d)) = (bv_unsigned b + d)%Z) by (apply u64_lit; lia).
  unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok. fold h. fold b. rewrite Hureq.
  rewrite (proj2 (Z.ltb_lt 0 _) Hb0), (proj2 (Z.ltb_lt (bv_unsigned b) _)) by lia. cbn [andb].
  rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
  rewrite (page_round_up_Z_aligned (bv_unsigned b + d))
    by (first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
  rewrite (proj2 (Z.ltb_lt _ _)) by lia.
  rewrite (proj2 (Z.leb_le _ _)) by lia.
  replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
  replace (bv_unsigned b + d + page_size - bv_unsigned b)%Z with (d + page_size)%Z by lia. rewrite Hrf.
  replace (bv_unsigned (Z_to_bv 64 (bv_unsigned b + d) - b)) with d.
  2:{ rewrite bv_sub_unsigned, Hureq. rewrite bv_wrap_small by (unfold bv_modulus; lia). lia. }
  rewrite (proj2 (Z.leb_le _ _) Hlive). reflexivity.
Qed.


End WithSegs.

(* [comment removed for export] *)
Local Open Scope Z_scope.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u64_roundtrip : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros x. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma region_free_app : forall l1 l2 (lo n : word),
  region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof.
  induction l1 as [|[b s] l1 IH]; intros l2 lo n; [reflexivity|].
  cbn [region_free app]. rewrite IH, andb_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_free_In : forall l (lo n b s : word),
  region_free l lo n = true -> In (b, s) l ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo.
Proof.
  induction l as [|[b' s'] l IH]; intros lo n b s Hrf Hin; [destruct Hin|].
  apply region_free_cons in Hrf as [Hd Hrf].
  destruct Hin as [E | Hin]; [injection E as -> ->; exact Hd | exact (IH _ _ _ _ Hrf Hin)].
Qed.

Lemma region_free_intro : forall l (lo n : word),
  (forall b s, In (b, s) l ->
     bv_unsigned lo + bv_unsigned n <= bv_unsigned b \/ bv_unsigned b + bv_unsigned s <= bv_unsigned lo) ->
  region_free l lo n = true.
Proof.
  induction l as [|[b s] l IH]; intros lo n H; [reflexivity|].
  cbn [region_free]. rewrite IH by (intros b' s' Hin; apply H; right; exact Hin).
  rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap. apply andb_false_iff.
  destruct (H b s (or_introl eq_refl)) as [Hl | Hr]; [right | left]; apply Z.ltb_ge; lia.
Qed.



Lemma map_contains_head : forall (a sz lo n : word) l,
  bv_unsigned a <= bv_unsigned lo ->
  bv_unsigned lo + bv_unsigned n <= bv_unsigned a + bv_unsigned sz ->
  map_contains ((a, sz) :: l) lo n = true.
Proof.
  intros a sz lo n l H1 H2. unfold map_contains. cbn [existsb fst snd].
  rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). reflexivity.
Qed.







(* [comment removed for export] *)
Lemma live_bytes_cons : forall (a n : word) l, live_bytes ((a, n) :: l) = bv_unsigned n + live_bytes l.
Proof. reflexivity. Qed.

Lemma live_bytes_app : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; intros l2; [reflexivity|]. cbn [live_bytes app]. rewrite IH. lia. Qed.



(* [comment removed for export] *)
Lemma maps_subtract_nil : forall (lo hi : Z), maps_subtract [] lo hi = [].
Proof. reflexivity. Qed.

Lemma maps_subtract_cons : forall (a sz : word) (lo hi : Z) l,
  maps_subtract ((a, sz) :: l) lo hi = iv_subtract a sz lo hi ++ maps_subtract l lo hi.
Proof. reflexivity. Qed.

Lemma maps_subtract_app : forall l1 l2 (lo hi : Z),
  maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof.
  induction l1 as [|[a sz] l1 IH]; intros l2 lo hi; [reflexivity|].
  cbn [maps_subtract app]. rewrite IH, app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_covered : forall (a sz : word) (lo hi : Z),
  lo <= bv_unsigned a -> bv_unsigned a + bv_unsigned sz <= hi ->
  iv_subtract a sz lo hi = [].
Proof.
  intros a sz lo hi H1 H2. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_ge _ _) H2). reflexivity.
Qed.


(* [comment removed for export] *)
Lemma iv_subtract_disjoint : forall (a sz : word) (lo hi : Z),
  0 < bv_unsigned sz -> lo <= hi ->
  (hi <= bv_unsigned a \/ bv_unsigned a + bv_unsigned sz <= lo) ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hsz Hlh Hd. unfold iv_subtract.
  destruct Hd as [Hd | Hd].
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a) lo)) by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app].
    rewrite Z.max_l by lia. rewrite u64_roundtrip.
    replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite u64_roundtrip. reflexivity.
  - rewrite (proj2 (Z.ltb_lt (bv_unsigned a) lo)) by lia.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [app].
    rewrite Z.min_l by lia. rewrite u64_roundtrip. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma iv_subtract_prefix : forall (a sz : word) (lo hi : Z),
  lo <= bv_unsigned a -> bv_unsigned a <= hi ->
  hi < bv_unsigned a + bv_unsigned sz ->
  iv_subtract a sz lo hi = [(Z_to_bv 64 hi, Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - hi))].
Proof.
  intros a sz lo hi H1 H2 H3. unfold iv_subtract.
  rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_lt _ _) H3). cbn [app].
  rewrite Z.max_r by lia. reflexivity.
Qed.






(* [comment removed for export] *)
Lemma live_bytes_iv_subtract_le : forall (a sz : word) (lo hi : Z),
  lo <= hi ->
  live_bytes (iv_subtract a sz lo hi) <= bv_unsigned sz.
Proof.
  intros a sz lo hi Hlh. pose proof (u64_range a). pose proof (u64_range sz).
  unfold iv_subtract.
  destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2;
    cbn [app live_bytes];
    first [apply Z.ltb_lt in E1 | apply Z.ltb_ge in E1]; first [apply Z.ltb_lt in E2 | apply Z.ltb_ge in E2];
    rewrite ?u64_lit by lia; lia.
Qed.

Lemma live_bytes_maps_subtract_le : forall l (lo hi : Z),
  lo <= hi -> live_bytes (maps_subtract l lo hi) <= live_bytes l.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi Hlh; [cbn; lia|].
  cbn [maps_subtract live_bytes]. rewrite live_bytes_app.
  pose proof (live_bytes_iv_subtract_le a sz lo hi Hlh). specialize (IH lo hi Hlh). lia.
Qed.


Lemma maps_subtract_all_cons : forall maps (a n : word) cuts,
  maps_subtract_all maps ((a, n) :: cuts)
  = maps_subtract_all (maps_subtract maps (bv_unsigned a) (bv_unsigned a + bv_unsigned n)) cuts.
Proof. reflexivity. Qed.

Lemma live_bytes_maps_subtract_all_le : forall cuts maps,
  live_bytes (maps_subtract_all maps cuts) <= live_bytes maps.
Proof.
  induction cuts as [|[a n] cuts IH]; intros maps; [cbn; lia|].
  rewrite maps_subtract_all_cons. etransitivity; [apply IH|].
  apply live_bytes_maps_subtract_le. pose proof (u64_range n). lia.
Qed.

(* [comment removed for export] *)
Lemma vm_backed_bytes_le_live : forall h, vm_backed_bytes h <= vm_live_bytes h.
Proof. intros h. unfold vm_backed_bytes, vm_backed_maps, vm_live_bytes. apply live_bytes_maps_subtract_all_le. Qed.

(* [comment removed for export] *)
Lemma vm_backing_used_le_live : forall m,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_backing_used m <= vm_live_bytes (m_vmmaps m).
Proof.
  intros m Hl Hm. rewrite (vm_backing_used_simple m Hl Hm). apply vm_backed_bytes_le_live.
Qed.


(* [comment removed for export] *)
Lemma mprotect_budget_ok_intro : forall m addr n,
  m_vm_lazy m = [] -> m_vm_materialized m = [] ->
  vm_live_bytes (m_vmmaps m) <= vm_limit (m_vmmaps m) ->
  mprotect_budget_ok m addr n = true.
Proof.
  intros m addr n Hl Hm Hlive. unfold mprotect_budget_ok, vm_backing_within_limit.
  rewrite mprotect_model_next_eq. apply Z.leb_le.
  etransitivity; [apply vm_backing_used_le_live; [unfold mprotect_model; rewrite with_vmmaps_lazy'; exact Hl | exact Hm]|].
  unfold mprotect_model. rewrite with_vmmaps_vm. cbn [vm_live_bytes vm_maps vm_limit]. exact Hlive.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cand (N : Z) (j : nat) : Z := bottomup_floor + Z.of_nat j * (2 * N).

Definition zconflict (a n : Z) (p : word * word) : Prop :=
  a < bv_unsigned (fst p) + bv_unsigned (snd p) /\ bv_unsigned (fst p) < a + n.

Definition zconflictb (a n : Z) (p : word * word) : bool :=
  (a <? bv_unsigned (fst p) + bv_unsigned (snd p)) && (bv_unsigned (fst p) <? a + n).

Lemma zconflictb_spec : forall a n p, zconflictb a n p = true <-> zconflict a n p.
Proof.
  intros a n p. unfold zconflictb, zconflict. rewrite andb_true_iff, !Z.ltb_lt. tauto.
Qed.

Lemma cand_spacing : forall N j k, 0 <= N -> (j < k)%nat -> cand N j + 2 * N <= cand N k.
Proof. intros N j k HN H. unfold cand. rewrite bottomup_floor_val. nia. Qed.

(* [comment removed for export] *)
Lemma conflict_unique : forall N n p j k,
  0 <= n <= N -> bv_unsigned (snd p) <= N ->
  zconflict (cand N j) n p -> zconflict (cand N k) n p -> j = k.
Proof.
  intros N n p j k Hn Hs [A1 A2] [B1 B2].
  destruct (Nat.lt_trichotomy j k) as [Hlt | [Heq | Hgt]]; [| exact Heq |].
  - pose proof (cand_spacing N j k ltac:(lia) Hlt). lia.
  - pose proof (cand_spacing N k j ltac:(lia) Hgt). lia.
Qed.

(* [comment removed for export] *)
Lemma filter_keep_all_but_one : forall (P : nat -> bool) (js : list nat),
  List.NoDup js ->
  (forall j k, In j js -> In k js -> P j = true -> P k = true -> j = k) ->
  (length js <= S (length (List.filter (fun j => negb (P j)) js)))%nat.
Proof.
  intros P js Hnd Huniq. induction js as [|j js IH]; [cbn; lia|].
  inversion Hnd as [|x l Hnotin Hnd']; subst.
  cbn [List.filter List.length]. destruct (P j) eqn:Pj; cbn [negb].
  - (* [comment removed for export] *)
    assert (Hall : forall k, In k js -> P k = false).
    { intros k Hk. destruct (P k) eqn:Pk; [|reflexivity].
      exfalso. assert (j = k) by (apply Huniq; [left; reflexivity | right; exact Hk | exact Pj | exact Pk]).
      subst k. exact (Hnotin Hk). }
    assert (Hid : List.filter (fun j0 => negb (P j0)) js = js).
    { clear -Hall. induction js as [|k js IH]; [reflexivity|].
      cbn [List.filter]. rewrite (Hall k (or_introl eq_refl)). cbn [negb]. f_equal. apply IH.
      intros k' Hk'. apply Hall. right. exact Hk'. }
    rewrite Hid. lia.
  - cbn [List.length].
    assert (IH' : (length js <= S (length (List.filter (fun j0 : nat => negb (P j0)) js)))%nat).
    { apply IH; [exact Hnd'|]. intros a b Ha Hb Pa Pb. apply Huniq; [right | right | |]; assumption. }
    lia.
Qed.

Lemma pick_candidate : forall (N n : Z) (l : list (word * word)) (js : list nat),
  0 <= n <= N ->
  Forall (fun p => bv_unsigned (snd p) <= N) l ->
  List.NoDup js -> (length l < length js)%nat ->
  exists j, In j js /\ forall p, In p l -> ~ zconflict (cand N j) n p.
Proof.
  intros N n l. induction l as [|p l IH]; intros js Hn Hsz Hnd Hlen.
  - destruct js as [|j js]; [cbn in Hlen; lia|]. exists j. split; [left; reflexivity | intros q []].
  - inversion Hsz as [|p' l' Hp Hl]; subst.
    set (js' := List.filter (fun j => negb (zconflictb (cand N j) n p)) js).
    assert (Hnd' : List.NoDup js') by (apply List.NoDup_filter; exact Hnd).
    assert (Hlen' : (length js <= S (length js'))%nat).
    { apply filter_keep_all_but_one; [exact Hnd|].
      intros j k _ _ Pj Pk. apply zconflictb_spec in Pj. apply zconflictb_spec in Pk.
      eapply (conflict_unique N n p); eassumption. }
    destruct (IH js' Hn Hl Hnd' ltac:(cbn in Hlen; lia)) as (j & Hj & Hfree).
    exists j. unfold js' in Hj. apply filter_In in Hj as [Hj Hnp]. split; [exact Hj|].
    intros q [<- | Hq].
    + intros Hc. apply zconflictb_spec in Hc. rewrite Hc in Hnp. discriminate.
    + apply Hfree. exact Hq.
Qed.

Lemma region_free_of_noconflict : forall l (a n : Z),
  0 <= a -> 0 <= n -> a + n < 2 ^ 64 ->
  (forall p, In p l -> ~ zconflict a n p) ->
  region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true.
Proof.
  induction l as [|[b s] l IH]; intros a n Ha Hn Hnw Hno; [reflexivity|].
  cbn [region_free]. rewrite IH; [| lia | lia | lia | intros p Hp; apply Hno; right; exact Hp].
  rewrite andb_true_r. apply negb_true_iff. unfold iv_overlap.
  rewrite !u64_lit by lia.
  specialize (Hno (b, s) (or_introl eq_refl)). unfold zconflict in Hno. cbn [fst snd] in Hno.
  apply andb_false_iff. destruct (Z_lt_le_dec a (bv_unsigned b + bv_unsigned s)).
  - right. apply Z.ltb_ge. lia.
  - left. apply Z.ltb_ge. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
