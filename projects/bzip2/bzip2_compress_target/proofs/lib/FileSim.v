(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SimInv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require CatSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatSim CatExec SeqExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require StreamSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require StreamSim.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SimInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim.ExitSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StreamSim.StreamExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StreamSim. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence OmniEquivalence. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require CatSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatSim. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. From Stdlib Require Lia. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)

Import ListNotations.
Open Scope bv_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma with_fds_halted : forall f m, m_halted (with_fds f m) = m_halted m.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma with_fs_halted : forall f m, m_halted (with_fs f m) = m_halted m.
Proof. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma adv_eff_ret : forall regs pc x8 mem rom r,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc; ms_svc_pending := Some x8;
       ms_resv := None; ms_fcsr := (Z_to_bv 32 0); ms_mem := mem; ms_rom := rom |} (mkEffect r [] []))
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
Lemma adv_eff_ret_copyins : forall regs pc x8 mem rom r copyins,
  advance_past_svc (apply_effect
    {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc; ms_svc_pending := Some x8;
       ms_resv := None; ms_fcsr := (Z_to_bv 32 0); ms_mem := mem; ms_rom := rom |}
    (with_copyins copyins (mkEffect r [] [])))
  = mkst (regupd regs 10 r) (v_addi pc 4) mem rom.
Proof.
  intros regs pc x8 mem rom r copyins.
  unfold with_copyins.
  apply adv_eff_ret.
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

Lemma path_eqb_neq : forall p q, p <> q -> path_eqb p q = false.
Proof.
  intros p q Hne. destruct (path_eqb p q) eqn:E; [|reflexivity].
  apply path_eqb_eq in E. congruence.
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

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mrb (segs : list Segment) (mem : word -> option byte)
    : word -> option byte :=
  fun a => match mem a with Some b => Some b | None => seg_rom segs a end.

(* [comment removed for export] *)

Lemma ms_read_byte_rec_mrb : forall segs regs fr pc sv rv fc mem,
  ms_read_byte {| ms_regs := regs; ms_fregs := fr; ms_pc_val := pc; ms_svc_pending := sv;
                  ms_resv := rv; ms_fcsr := fc; ms_mem := mem; ms_rom := seg_rom segs |}
  = mrb segs mem.
Proof. reflexivity. Qed.

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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma read_argv_cstr_k : forall ph segs (sp : word) av ev k uid hw rnd,
  (k < length av)%nat ->
  (bv_unsigned sp + Z.of_nat (length (build_stack_bytes ph sp av ev uid hw rnd)) < 2^64)%Z ->
  rdn segs (stack_to_mem sp (entry_stack_image ph sp av ev uid hw rnd))
      (cat_argv_ptr sp av ev k) (length (nth k av []) + 1)
  = Some (nth k av [] ++ [Z_to_bv 8 0]).
Proof.
  intros ph segs sp av ev k uid hw rnd Hk Hnw.
  destruct (bsb_byte_k ph sp av ev k uid hw rnd Hk) as [pre [post [E Hlen]]].
  pose proof (read_at_offset_image segs ph sp av ev uid hw rnd
    pre (nth k av [] ++ [Z_to_bv 8 0]) post (length (nth k av []) + 1)) as H.
  rewrite Hlen in H.
  replace (cat_argv_ptr sp av ev k)
    with (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
  2:{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
      rewrite nat_to_word_add_merge. reflexivity. }
  apply H; [exact E | | exact Hnw].
  rewrite length_app. cbn [length]. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

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

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma tfo_sys_det : forall ms model x8 eff model' U,
  ms_svc_pending ms = Some x8 ->
  syscall_spec (sys_input segs ms x8) model (Ok eff model' []) ->
  (forall eff2 m2 evs2,
      syscall_spec (sys_input segs ms x8) model (Ok eff2 m2 evs2) ->
      eff2 = eff /\ m2 = model' /\ evs2 = []) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  m_halted model' = None ->
  m_vm_lazy model' = [] ->
  to_fout (advance_past_svc (apply_effect ms eff)) model' U ->
  to_fout ms model U.
Proof.
  intros ms model x8 eff model' U Hsvc Hok Huniq Hne Hh' Hlazy' Hcont.
  apply (tfo_sys ms model x8 (fun _ _ => U) U); [exact Hsvc | exact Hne | | | |].
  - exists eff, model', []. exact Hok.
  - intros eff2 m2 evs2 Hs.
    cps_destruct (Huniq eff2 m2 evs2 Hs) as (_ & -> & ->).
    repeat split; assumption.
  - intros eff2 m2 evs2 Hs.
    cps_destruct (Huniq eff2 m2 evs2 Hs) as (-> & -> & _). exact Hcont.
  - intro o. split.
    + intro Ho. exists eff, model', []. auto.
    + cps_intros (e2 & m2 & ev2 & _ & Ht). exact Ht.
Qed.

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

Lemma check_syscall_64 : forall segs ms x8 eff m,
  bv_unsigned x8 = 64%Z ->
  check_syscall (sys_input segs ms x8) eff m
  = check_write (sys_input segs ms x8) (fd32 (ms_gpr ms 0)) (ms_gpr ms 1)
                (ms_gpr ms 2) eff m.
Proof.
  intros segs ms x8 eff m Hno.
  unfold check_syscall. rewrite in_sysno_si, Hno. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma errno_ret_recover : forall e,
  (1 <= e)%Z -> (e <= 4095)%Z ->
  (two_pow_64 - bv_unsigned (errno_ret e))%Z = e.
Proof.
  intros e H1 H2. rewrite (errno_ret_unsigned e H1 H2). lia.
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
      apply errno_ret_in_true in Herr. cps_destruct Herr as (e & HIn & ->).
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
Lemma openat_wr_check : forall segs ms x8 model p,
  bv_unsigned x8 = 56%Z ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  path_eqb p [] = false ->
  Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = wr_create_flags ->
  openat_plain_name p = true ->
  fs_under (m_fs model) p = false ->       (* [comment removed for export] *)
  forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_open_result_copyins (open_copyins ms) eff model
        (fun fd => with_fds (fd_insert (m_fds model) fd
                               (FdFileW p (Z_to_bv 64 0)))
                     (with_fs (fs_set (m_fs model) p []) model)).
Proof.
  intros segs ms x8 model p Hno Hdirfd Hpath Hpe Hfl Hdot Hfsu eff.
  pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
  apply openat_plain_name_nodirref in Hdot.
  rewrite (check_syscall_56 segs ms x8 eff model Hno). unfold check_openat.
  rewrite (modeled_open_flags_wr _ Hfl). cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, Hpath. cbv beta iota zeta.
  rewrite Hpe. cbv beta iota.
  rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
  unfold Open.check_openat_resolved.
  rewrite Hunw. cbv beta iota.
  rewrite Hfl.
  change (wr_create_flags =? 0)%Z with false. cbv beta iota.
  rewrite Z.eqb_refl. cbv beta iota.
  unfold Open.check_openat_create, check_create_wronly.
  rewrite ?Hdot, ?Hfsu.
  unfold check_open_result_copyins, open_copyins.
  destruct (check_open_result (clear_copyins eff) model
    (fun fd : word =>
       with_fds
         (fd_insert (m_fds model) fd (FdFileW p (Z_to_bv 64 0)))
         (with_fs (fs_set (m_fs model) p []) model)))
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

(* [comment removed for export] *)
Lemma tfo_open_core : forall ms model (mk : word -> Model) x8 reads
    (Te : Z -> (word * Fs.Fs) -> Prop) (Ts : word -> (word * Fs.Fs) -> Prop) U,
  ms_svc_pending ms = Some x8 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model
               = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None /\ m_vm_lazy (mk fd) = []) ->
  (forall e, In e openat_errnos ->
     to_fout segs (advance_past_svc
                     (apply_effect ms
                       (with_copyins reads (mkEffect (errno_ret e) [] []))))
             model (Te e)) ->
  (forall fd, fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
     to_fout segs (advance_past_svc
                    (apply_effect ms (with_copyins reads (mkEffect fd [] []))))
             (mk fd) (Ts fd)) ->
  (forall o, U o <->
     ((exists e, In e openat_errnos /\ Te e o)
      \/ (exists fd, fd_lookup (m_fds model) fd = None
                     /\ fd = alloc_fd (m_fds model) /\ Ts fd o))) ->
  to_fout segs ms model U.
Proof.
  intros ms model mk x8 reads Te Ts U Hsvc Hh Hlazy Hchk Hmk Herr Hok HU.
  apply (tfo_sys segs ms model x8
    (fun eff model' =>
       if addr_is_error_b (eff_ret eff)
       then Te ((two_pow_64 - bv_unsigned (eff_ret eff))%Z)
       else Ts (eff_ret eff)) U); [exact Hsvc | | | | |].
  - (* [comment removed for export] *)
    intro Hspec.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] []))
      in Hspec.
    rewrite Hchk in Hspec.
    exact (check_open_result_copyins_never_unmodeled _ _ _ _ Hspec).
  - (* [comment removed for export] *)
    exists (with_copyins reads (mkEffect (errno_ret ENOMEM) [] [])), model, [].
    apply check_syscall_ok_iff. rewrite Hchk.
    apply check_open_result_copyins_ok_iff. left. exists ENOMEM.
    repeat split; try reflexivity. apply ENOMEM_in_openat_errnos.
  - (* [comment removed for export] *)
    intros eff model' evs Hspec.
    apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
    apply check_open_result_copyins_ok_iff in Hspec.
    destruct Hspec as [ (e & _ & -> & -> & ->)
                      | (fd & _ & _ & -> & -> & ->) ].
    + repeat split; assumption.
    + destruct (Hmk fd) as [Hhalt Hlazy']. repeat split; assumption.
  - (* [comment removed for export] *)
    intros eff model' evs Hspec.
    apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
    apply check_open_result_copyins_ok_iff in Hspec.
    destruct Hspec as [ (e & HIn & -> & -> & _)
                      | (fd & Hlk & Heq & -> & -> & _) ].
    + destruct (openat_errno_range e HIn) as [He1 He2].
      cbn [eff_ret with_copyins].
      rewrite (errno_ret_error_b e He1 He2).
      rewrite (errno_ret_recover e He1 He2).
      apply Herr; assumption.
    + cbn [eff_ret with_copyins].
      assert (Hne : addr_is_error_b fd = false)
        by (rewrite Heq; apply alloc_fd_not_error_b).
      rewrite Hne.
      apply Hok; assumption.
  - (* [comment removed for export] *)
    intro o. rewrite HU. split.
    + intros [ (e & HIn & Ht) | (fd & Hlk & Heq & Ht) ].
      * destruct (openat_errno_range e HIn) as [He1 He2].
        exists (with_copyins reads (mkEffect (errno_ret e) [] [])), model, [].
        split.
        { apply check_syscall_ok_iff. rewrite Hchk.
          apply check_open_result_copyins_ok_iff. left. exists e. auto. }
        { cbn [eff_ret with_copyins]. rewrite (errno_ret_error_b e He1 He2).
          rewrite (errno_ret_recover e He1 He2). exact Ht. }
      * exists (with_copyins reads (mkEffect fd [] [])), (mk fd), [].
        split.
        { apply check_syscall_ok_iff. rewrite Hchk.
          apply check_open_result_copyins_ok_iff. right. exists fd. auto. }
        { cbn [eff_ret with_copyins].
          assert (Hne : addr_is_error_b fd = false)
            by (rewrite Heq; apply alloc_fd_not_error_b).
          rewrite Hne. exact Ht. }
    + cps_intros (eff & model' & evs & Hspec & Ht).
      apply check_syscall_ok_iff in Hspec. rewrite Hchk in Hspec.
      apply check_open_result_copyins_ok_iff in Hspec.
      destruct Hspec as [ (e & HIn & -> & -> & _)
                        | (fd & Hlk & Heq & -> & -> & _) ].
      * destruct (openat_errno_range e HIn) as [He1 He2].
        cbn [eff_ret with_copyins] in Ht.
        rewrite (errno_ret_error_b e He1 He2) in Ht.
        rewrite (errno_ret_recover e He1 He2) in Ht.
        left. exists e. auto.
      * cbn [eff_ret with_copyins] in Ht.
        assert (Hne : addr_is_error_b fd = false)
          by (rewrite Heq; apply alloc_fd_not_error_b).
        rewrite Hne in Ht.
        right. exists fd. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma tfo_openat_toolong : forall ms model x8 U,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 56%Z ->
  modeled_open_flags (ms_gpr ms 2) = true ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrTooLong ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (advance_past_svc
                  (apply_effect ms
                    (with_copyins (open_copyins ms)
                      (mkEffect (errno_ret ENAMETOOLONG) [] []))))
          model U ->
  to_fout segs ms model U.
Proof.
  intros ms model x8 U Hsvc Hno Hfl Hpath Hh Hlazy Hcont.
  pose proof (openat_toolong_check segs ms x8 model Hno Hfl Hpath) as Hchk.
  apply (tfo_sys_det segs ms model x8
           (with_copyins (open_copyins ms)
             (mkEffect (errno_ret ENAMETOOLONG) [] [])) model U);
    [exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
  - apply check_syscall_ok_iff. rewrite Hchk.
    apply check_ret_only_copyins_ok_iff. auto.
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs.
    exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
Qed.

(* [comment removed for export] *)
Lemma tfo_openat_enoent : forall ms model x8 p U,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 56%Z ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk p ->
  Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z ->
  openat_plain_name p = true ->
  fs_lookup (m_fs model) p = None ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (advance_past_svc
                  (apply_effect ms
                    (with_copyins (open_copyins ms)
                      (mkEffect (errno_ret ENOENT) [] []))))
          model U ->
  to_fout segs ms model U.
Proof.
  intros ms model x8 p U Hsvc Hno Hdirfd Hpath Hfl Hdot Hfs Hh Hlazy Hcont.
  pose proof (openat_plain_name_noslash _ Hdot) as Hunw.
  apply openat_plain_name_nodirref in Hdot.
  assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model
                 = check_ret_only_copyins (open_copyins ms) eff
                     (errno_ret ENOENT) model []).
  { intro eff. rewrite (check_syscall_56 segs ms x8 eff model Hno).
    unfold check_openat.
    rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
    unfold Prelude.check_copyins_after, Open.check_openat_body.
    rewrite in_mem_si, Hpath. cbv beta iota zeta.
    (* [comment removed for export] *)
    destruct (path_eqb p []) eqn:Hpe; cbv beta iota.
    - apply check_copyins_after_ret_only.
    - rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
      unfold Open.check_openat_resolved.
      rewrite Hunw. cbv beta iota.
      rewrite Hfl, Z.eqb_refl. cbv beta iota.
      unfold Open.check_openat_read. rewrite Hdot, Hfs.
      apply check_copyins_after_ret_only. }
  apply (tfo_sys_det segs ms model x8
           (with_copyins (open_copyins ms) (mkEffect (errno_ret ENOENT) [] []))
           model U);
    [exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
  - apply check_syscall_ok_iff. rewrite Hchk.
    apply check_ret_only_copyins_ok_iff. auto.
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs.
    exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
Qed.

(* [comment removed for export] *)

Lemma tfo_read_file : forall ms model x8 p off data w U,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 63%Z ->
  fd_lookup (m_fds model) (ms_gpr ms 0) = Some (FdFile p off) ->
  fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
  fs_lookup (m_fs model) p = Some data ->
  read_bytes_map (ms_writable_byte segs ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some w ->
  (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z ->
  (0 < bv_unsigned (ms_gpr ms 2))%Z ->
  (* [comment removed for export] *)
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs
    (advance_past_svc (apply_effect ms
       (mkEffect (len_word (file_read data off (ms_gpr ms 2)))
                 (delivered_writes (ms_gpr ms 1)
                    (file_read data off (ms_gpr ms 2))) [])))
    (with_fds
       (fd_insert (m_fds model) (ms_gpr ms 0)
          (FdFile p (off + len_word (file_read data off (ms_gpr ms 2)))))
       model)
    U ->
  to_fout segs ms model U.
Proof.
  intros ms model x8 p off data w U Hsvc Hno Hfd Hfd32 Hfs Hw Hcnt Hpos Haok Hh Hlazy Hcont.
  set (bs := file_read data off (ms_gpr ms 2)).
  assert (HL : (bv_unsigned (len_word (file_read data off (ms_gpr ms 2)))
                <= bv_unsigned (ms_gpr ms 2))%Z).
  { unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
    pose proof (u64_range (ms_gpr ms 2)) as Hc.
    rewrite length_file_read, Nat2Z.inj_min.
    unfold word_to_nat.
    rewrite Z.mod_small; lia. }
  assert (Hchk : forall eff m' evs,
    check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs <->
    (eff = mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) []
     /\ m' = with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
               (FdFile p (off + len_word bs))) model
     /\ evs = [])).
  { intros eff m' evs.
    rewrite (check_syscall_63 segs ms x8 eff model Hno). unfold check_read.
    rewrite Hfd32, Hfd. cbv beta iota.
    rewrite Haok. cbn [negb]. cbv beta iota.
    rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned.
    rewrite Hfs. cbv beta iota zeta.
    rewrite in_wmem_si.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw). cbv beta iota.
    unfold bs.
    destruct (file_read data off (ms_gpr ms 2)) as [|b bsr].
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
        destruct (bv_eqb a (ms_gpr ms 1) && listN_eqb bs' (b :: bsr)
                  && bv_eqb ret (len_word (b :: bsr)))
          eqn:Hb; try rewrite Hb in H; [|discriminate].
        apply andb_true_iff in Hb as [Hb Hr].
        apply andb_true_iff in Hb as [Ha Hbs].
        apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hr. apply listN_eqb_eq in Hbs.
        inversion H; subst. cbn [delivered_writes].
        repeat split; congruence.
      + cps_intros (Heff & -> & ->). cbn [delivered_writes] in Heff.
        inversion Heff; subst.
        rewrite bv_eqb_refl.
        rewrite (proj2 (listN_eqb_eq _ _) eq_refl).
        rewrite bv_eqb_refl. cbn [andb]. reflexivity. }
  apply (tfo_sys_det segs ms model x8
           (mkEffect (len_word bs) (delivered_writes (ms_gpr ms 1) bs) [])
           (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
              (FdFile p (off + len_word bs))) model) U);
    [exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
  - apply check_syscall_ok_iff. apply Hchk. auto.
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. apply Hchk in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite (check_syscall_63 segs ms x8 _ model Hno) in Hs.
    unfold check_read in Hs.
    rewrite Hfd32, Hfd in Hs. cbv beta iota in Hs.
    rewrite Haok in Hs. cbn [negb] in Hs. cbv beta iota in Hs.
    rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned in Hs.
    rewrite Hfs in Hs. cbv beta iota zeta in Hs.
    rewrite in_wmem_si in Hs.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw) in Hs.
    cbv beta iota in Hs.
    revert Hs.
    destruct (file_read data off (ms_gpr ms 2)) as [|b0 bsr]; intro Hs.
    + exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
    + discriminate.
Qed.

(* [comment removed for export] *)

Lemma tfo_write_file : forall ms model x8 p off data bs U,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  fd_lookup (m_fds model) (ms_gpr ms 0) = Some (FdFileW p off) ->
  fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
  read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some bs ->
  (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z ->
  fs_lookup (m_fs model) p = Some data ->
  (* [comment removed for export] *)
  negb (modeled_file_gap data off bs) = false ->
  (* [comment removed for export] *)
  w_is0 (ms_gpr ms 2) = false ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs
    (advance_past_svc (apply_effect ms
      (with_copyins [(ms_gpr ms 1, length bs)]
        (mkEffect (ms_gpr ms 2) [] []))))
    (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
                 (FdFileW p (off + ms_gpr ms 2)))
       (with_fs (fs_set (m_fs model) p (file_write data off bs)) model))
    U ->
  to_fout segs ms model U.
Proof.
  intros ms model x8 p off data bs U Hsvc Hno Hfd Hfd32 Hrd Hcnt Hfs Hgap Hnz Hh Hlazy Hcont.
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some bs).
  { rewrite in_mem_si. exact Hrd. }
  assert (Hchk : forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_ret_only_copyins [(ms_gpr ms 1, length bs)] eff (ms_gpr ms 2)
        (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
                     (FdFileW p (off + ms_gpr ms 2)))
           (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) []).
  { intro eff.
    rewrite (check_syscall_64 segs ms x8 eff model Hno). unfold check_write.
    rewrite Hfd32, Hfd. cbv beta iota.
    rewrite (rw_range_in_range _ _ Hcnt). cbv beta iota zeta.
    rewrite (write_source_of_rw _ _ _ Hcnt), (readable_bytes_full _ _ _ _ Hrb).
    pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
    assert (Hret : len_word bs = ms_gpr ms 2).
    { unfold len_word. rewrite Hlen. apply Z_to_bv_bv_unsigned. }
    assert (Hgate : (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) = false).
    { destruct (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) eqn:Hg'; [|reflexivity].
      exfalso. apply andb_prop in Hg' as [Hnz' Hz].
      apply Nat.eqb_eq in Hz. apply negb_true_iff in Hnz'.
      rewrite Hz in Hlen. cbn in Hlen.
      assert (Hzero : ms_gpr ms 2 = Z_to_bv 64 0).
      { rewrite <- (Z_to_bv_bv_unsigned 64 (ms_gpr ms 2)). rewrite <- Hlen. reflexivity. }
      unfold w_is0 in Hnz'. rewrite Hzero, bv_eqb_refl in Hnz'. discriminate. }
    rewrite Hgate. cbv beta iota.
    rewrite Hfs. cbv beta iota.
    rewrite Hgap. cbv beta iota.
    rewrite Hret.
    rewrite Hnz. reflexivity. }
  apply (tfo_sys_det segs ms model x8
           (with_copyins [(ms_gpr ms 1, length bs)]
             (mkEffect (ms_gpr ms 2) [] []))
           (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
                        (FdFileW p (off + ms_gpr ms 2)))
              (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)));
    [exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
  - apply check_syscall_ok_iff. rewrite Hchk.
    apply check_ret_only_copyins_ok_iff. auto.
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_ret_only_copyins_ok_iff in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs.
    exact (check_ret_only_copyins_no_unmodeled _ _ _ _ _ Hs).
Qed.

(* [comment removed for export] *)
Lemma tfo_write_file_zero : forall ms model x8 p off data bs U,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 64%Z ->
  fd_lookup (m_fds model) (ms_gpr ms 0) = Some (FdFileW p off) ->
  fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
  read_bytes_map (ms_read_byte ms) (ms_gpr ms 1) (ms_gpr ms 2) = Some bs ->
  (bv_unsigned (ms_gpr ms 2) <= rw_bytes_max)%Z ->
  fs_lookup (m_fs model) p = Some data ->
  (* [comment removed for export] *)
  negb (modeled_file_gap data off bs) = false ->
  w_is0 (ms_gpr ms 2) = true ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs
    (advance_past_svc (apply_effect ms (mkEffect (ms_gpr ms 2) [] [])))
    (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
                 (FdFileW p (off + ms_gpr ms 2)))
       (with_fs (fs_set (m_fs model) p (file_write data off bs)) model))
    U ->
  to_fout segs ms model U.
Proof.
  intros ms model x8 p off data bs U Hsvc Hno Hfd Hfd32 Hrd Hcnt Hfs Hgap Hz Hok Hh Hlazy Hcont.
  assert (Hrb : read_bytes_map (in_mem (sys_input segs ms x8))
                  (ms_gpr ms 1) (ms_gpr ms 2) = Some bs).
  { rewrite in_mem_si. exact Hrd. }
  assert (Hchk : forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_ret_only eff (ms_gpr ms 2)
        (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
                     (FdFileW p (off + ms_gpr ms 2)))
           (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) []).
  { intro eff.
    rewrite (check_syscall_64 segs ms x8 eff model Hno). unfold check_write.
    rewrite Hfd32, Hfd. cbv beta iota.
    rewrite (rw_range_in_range _ _ Hcnt). cbv beta iota zeta.
    rewrite (write_source_of_rw _ _ _ Hcnt), (readable_bytes_full _ _ _ _ Hrb).
    pose proof (read_bytes_map_length _ _ _ _ Hrb) as Hlen.
    assert (Hret : len_word bs = ms_gpr ms 2).
    { unfold len_word. rewrite Hlen. apply Z_to_bv_bv_unsigned. }
    assert (Hgate : (negb (w_is0 (ms_gpr ms 2)) && (length bs =? 0)%nat) = false).
    { rewrite Hz. reflexivity. }
    rewrite Hgate. cbv beta iota.
    rewrite Hfs. cbv beta iota.
    rewrite Hgap. cbv beta iota.
    rewrite Hret.
    rewrite Hz. cbv beta iota.
    unfold check_access_ok_zero. rewrite Hok. reflexivity. }
  apply (tfo_sys_det segs ms model x8
           (mkEffect (ms_gpr ms 2) [] [])
           (with_fds (fd_insert (m_fds model) (ms_gpr ms 0)
                        (FdFileW p (off + ms_gpr ms 2)))
              (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)));
    [exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
  - apply check_syscall_ok_iff. rewrite Hchk.
    apply check_ret_only_ok_iff. auto.
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_ret_only_ok_iff in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs.
    exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
Qed.

(* [comment removed for export] *)

Lemma tfo_close : forall ms model x8 e U,
  ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = 57%Z ->
  fd_lookup (m_fds model) (ms_gpr ms 0) = Some e ->
  fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs
    (advance_past_svc (apply_effect ms (mkEffect (Z_to_bv 64 0) [] [])))
    (with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model)
    U ->
  to_fout segs ms model U.
Proof.
  intros ms model x8 e U Hsvc Hno Hfd Hfd32 Hh Hlazy Hcont.
  assert (Hchk : forall eff,
    check_syscall (sys_input segs ms x8) eff model
    = check_ret_only eff (Z_to_bv 64 0)
        (with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model) []).
  { intro eff.
    rewrite (check_syscall_57 segs ms x8 eff model Hno). unfold check_close.
    rewrite Hfd32, Hfd. reflexivity. }
  apply (tfo_sys_det segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
           (with_fds (fd_remove (m_fds model) (ms_gpr ms 0)) model));
    [exact Hsvc | | | | exact Hh | exact Hlazy | exact Hcont].
  - apply check_syscall_ok_iff. rewrite Hchk.
    apply check_ret_only_ok_iff. auto.
  - intros eff2 m2 evs2 Hs.
    apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    apply check_ret_only_ok_iff in Hs. exact Hs.
  - intro Hs.
    apply (check_syscall_complete_unmodeled _ _ (mkEffect (Z_to_bv 64 0) [] [])) in Hs.
    rewrite Hchk in Hs.
    exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
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

Lemma record_gpr : forall regs fr pc sv rv fc mem rom k,
  ms_gpr {| ms_regs := regs; ms_fregs := fr; ms_pc_val := pc; ms_svc_pending := sv;
            ms_resv := rv; ms_fcsr := fc; ms_mem := mem; ms_rom := rom |} k
  = reg_get regs (Z_to_bv 5 (10 + Z.of_nat k)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma tfo_exit_rec : forall regs pc mem rom model code fsv,
  bv_unsigned (getr regs 17) = 93%Z ->
  reg_get regs 10 = code -> (bv_unsigned code < 256)%Z ->
  m_fs model = fsv ->
  to_fout segs {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := (Z_to_bv 32 0); ms_mem := mem; ms_rom := rom |}
          model (fun o => o = (code, fsv)).
Proof.
  intros regs pc mem rom model code fsv H17 H10 Hc Hfs.
  subst fsv.
  eapply (tfo_exit segs _ model (getr regs 17)).
  - cbn [ms_svc_pending]. reflexivity.
  - left. exact H17.
  - intro o. rewrite record_gpr, arg_reg_0.
    rewrite H10, (land_255_small code Hc). tauto.
Qed.

(* [comment removed for export] *)
Lemma tfo_read_rec : forall regs pc mem rom model fdv p off data buf cnt U,
  bv_unsigned (getr regs 17) = 63%Z ->
  reg_get regs 10 = fdv -> reg_get regs 11 = buf -> reg_get regs 12 = cnt ->
  fd_lookup (m_fds model) fdv = Some (FdFile p off) ->
  fd32 fdv = fdv ->
  fs_lookup (m_fs model) p = Some data ->
  wseg_ok segs buf (word_to_nat cnt) = true ->
  (bv_unsigned cnt <= rw_bytes_max)%Z ->
  (0 < bv_unsigned cnt)%Z ->
  (* [comment removed for export] *)
  access_okb buf (bv_unsigned cnt) = true ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs
    (mkst (regupd regs 10 (len_word (file_read data off cnt))) (v_addi pc 4)
          (write_to_mem mem buf (file_read data off cnt)) rom)
    (with_fds (fd_insert (m_fds model) fdv
        (FdFile p (off + len_word (file_read data off cnt)))) model)
    U ->
  to_fout segs {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := (Z_to_bv 32 0); ms_mem := mem; ms_rom := rom |} model U.
Proof.
  intros regs pc mem rom model fdv p off data buf cnt U
    H17 H10 H11 H12 Hfd Hfd32 Hfs Hwseg Hcnt Hpos Haok Hh Hlazy Hcont.
  set (ms := {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := (Z_to_bv 32 0); ms_mem := mem; ms_rom := rom |}).
  assert (Hg0 : ms_gpr ms 0 = fdv)
    by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
  assert (Hg1 : ms_gpr ms 1 = buf)
    by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
  assert (Hg2 : ms_gpr ms 2 = cnt)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  destruct (wseg_ok_wdef segs buf cnt ms Hwseg) as [w Hw].
  apply (tfo_read_file ms model (getr regs 17) p off data w U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - rewrite Hg0. exact Hfd.
  - rewrite Hg0. exact Hfd32.
  - exact Hfs.
  - rewrite Hg1, Hg2. exact Hw.
  - rewrite Hg2. exact Hcnt.
  - rewrite Hg2. exact Hpos.
  - rewrite Hg1, Hg2. exact Haok.
  - exact Hh.
  - exact Hlazy.
  - rewrite Hg0, Hg1, Hg2. unfold ms.
    rewrite adv_apply_delivered. exact Hcont.
Qed.

(* [comment removed for export] *)
Lemma tfo_write_rec : forall regs pc mem model fdv p off data bs buf cnt U,
  bv_unsigned (getr regs 17) = 64%Z ->
  reg_get regs 10 = fdv -> reg_get regs 11 = buf -> reg_get regs 12 = cnt ->
  fd_lookup (m_fds model) fdv = Some (FdFileW p off) ->
  fd32 fdv = fdv ->
  rdn segs mem buf (word_to_nat cnt) = Some bs ->
  (bv_unsigned cnt <= rw_bytes_max)%Z ->
  fs_lookup (m_fs model) p = Some data ->
  (* [comment removed for export] *)
  negb (modeled_file_gap data off bs) = false ->
  (* [comment removed for export] *)
  (access_okb buf (bv_unsigned cnt) = true \/ (0 < bv_unsigned cnt)%Z) ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (mkst (regupd regs 10 cnt) (v_addi pc 4) mem (seg_rom segs))
    (with_fds (fd_insert (m_fds model) fdv (FdFileW p (off + cnt)))
       (with_fs (fs_set (m_fs model) p (file_write data off bs)) model)) U ->
  to_fout segs {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := (Z_to_bv 32 0); ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model fdv p off data bs buf cnt U
    H17 H10 H11 H12 Hfd Hfd32 Hrd Hcnt Hfs Hgap Hok Hh Hlazy Hcont.
  set (ms := {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := (Z_to_bv 32 0); ms_mem := mem; ms_rom := seg_rom segs |}).
  assert (Hg0 : ms_gpr ms 0 = fdv)
    by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
  assert (Hg1 : ms_gpr ms 1 = buf)
    by (unfold ms; rewrite record_gpr, arg_reg_1; exact H11).
  assert (Hg2 : ms_gpr ms 2 = cnt)
    by (unfold ms; rewrite record_gpr, arg_reg_2; exact H12).
  destruct (w_is0 cnt) eqn:Hz.
  - (* [comment removed for export] *)
    apply (tfo_write_file_zero ms model (getr regs 17) p off data bs U).
    + unfold ms. cbn [ms_svc_pending]. reflexivity.
    + exact H17.
    + rewrite Hg0. exact Hfd.
    + rewrite Hg0. exact Hfd32.
    + rewrite Hg1, Hg2.
      rewrite read_bytes_map_read_byte.
      rewrite (ms_read_bytes_rdn segs ms) by reflexivity.
      exact Hrd.
    + rewrite Hg2. exact Hcnt.
    + exact Hfs.
    + exact Hgap.
    + rewrite Hg2. exact Hz.
    + destruct Hok as [Hfl | Hp].
      * rewrite Hg1, Hg2. exact Hfl.
      * (* [comment removed for export] *)
        rewrite (w_is0_pos cnt Hp) in Hz. discriminate.
    + exact Hh.
    + exact Hlazy.
    + rewrite Hg0, Hg2. unfold ms.
      rewrite adv_eff_ret. exact Hcont.
  - (* [comment removed for export] *)
    apply (tfo_write_file ms model (getr regs 17) p off data bs U).
    + unfold ms. cbn [ms_svc_pending]. reflexivity.
    + exact H17.
    + rewrite Hg0. exact Hfd.
    + rewrite Hg0. exact Hfd32.
    + rewrite Hg1, Hg2.
      rewrite read_bytes_map_read_byte.
      rewrite (ms_read_bytes_rdn segs ms) by reflexivity.
      exact Hrd.
    + rewrite Hg2. exact Hcnt.
    + exact Hfs.
    + exact Hgap.
    + rewrite Hg2. exact Hz.
    + exact Hh.
    + exact Hlazy.
    + rewrite Hg0, Hg2. unfold ms.
      rewrite adv_eff_ret_copyins. exact Hcont.
Qed.

(* [comment removed for export] *)
Lemma tfo_close_rec : forall regs pc mem rom model fdv e U,
  bv_unsigned (getr regs 17) = 57%Z ->
  reg_get regs 10 = fdv ->
  fd_lookup (m_fds model) fdv = Some e ->
  fd32 fdv = fdv ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4) mem rom)
    (with_fds (fd_remove (m_fds model) fdv) model) U ->
  to_fout segs {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := (Z_to_bv 32 0); ms_mem := mem; ms_rom := rom |} model U.
Proof.
  intros regs pc mem rom model fdv e U H17 H10 Hfd Hfd32 Hh Hlazy Hcont.
  set (ms := {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := (Z_to_bv 32 0); ms_mem := mem; ms_rom := rom |}).
  assert (Hg0 : ms_gpr ms 0 = fdv)
    by (unfold ms; rewrite record_gpr, arg_reg_0; exact H10).
  apply (tfo_close ms model (getr regs 17) e U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - rewrite Hg0. exact Hfd.
  - rewrite Hg0. exact Hfd32.
  - exact Hh.
  - exact Hlazy.
  - rewrite Hg0. unfold ms. rewrite adv_eff_ret. exact Hcont.
Qed.

(* [comment removed for export] *)
Lemma tfo_open_enoent_rec : forall regs pc mem model p U,
  bv_unsigned (getr regs 17) = 56%Z ->
  reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 0 ->
  read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
  openat_plain_name p = true ->
  fs_lookup (m_fs model) p = None ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (mkst (regupd regs 10 (errno_ret ENOENT)) (v_addi pc 4)
                     mem (seg_rom segs))
          model U ->
  to_fout segs {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := (Z_to_bv 32 0); ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model p U H17 H10 H12 Hpath Hdot Hfs Hh Hlazy Hcont.
  set (ms := {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := (Z_to_bv 32 0); ms_mem := mem; ms_rom := seg_rom segs |}).
  apply (tfo_openat_enoent ms model (getr regs 17) p U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
  - unfold ms. rewrite record_gpr, arg_reg_1.
    rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
  - unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
    vm_compute. reflexivity.
  - exact Hdot.
  - exact Hfs.
  - exact Hh.
  - exact Hlazy.
  - unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
Qed.

(* [comment removed for export] *)
Lemma tfo_open_rd_rec : forall regs pc mem model p d
    (Te : Z -> (word * Fs.Fs) -> Prop) (Ts : word -> (word * Fs.Fs) -> Prop) U,
  bv_unsigned (getr regs 17) = 56%Z ->
  reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 0 ->
  read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
  path_eqb p [] = false ->
  openat_plain_name p = true ->
  fs_lookup (m_fs model) p = Some d ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall e, In e openat_errnos ->
     to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
                        mem (seg_rom segs))
             model (Te e)) ->
  (forall fd, fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
     to_fout segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
             (with_fds (fd_insert (m_fds model) fd
                          (FdFile p (Z_to_bv 64 0))) model) (Ts fd)) ->
  (forall o, U o <->
     ((exists e, In e openat_errnos /\ Te e o)
      \/ (exists fd, fd_lookup (m_fds model) fd = None
                     /\ fd = alloc_fd (m_fds model) /\ Ts fd o))) ->
  to_fout segs {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := (Z_to_bv 32 0); ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model p d Te Ts U
    H17 H10 H12 Hpath Hpe Hdot Hfs Hh Hlazy Herr Hok HU.
  set (ms := {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := (Z_to_bv 32 0); ms_mem := mem; ms_rom := seg_rom segs |}).
  apply (tfo_open_core ms model
           (fun fd => with_fds (fd_insert (m_fds model) fd
                                  (FdFile p (Z_to_bv 64 0))) model)
           (getr regs 17) (open_copyins ms) Te Ts U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact Hh.
  - exact Hlazy.
  - intro eff. apply (openat_rd_check segs ms (getr regs 17) model p d).
    + exact H17.
    + unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
    + unfold ms. rewrite record_gpr, arg_reg_1.
      rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
    + exact Hpe.
    + unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
      vm_compute. reflexivity.
    + exact Hdot.
    + exact Hfs.
  - intro fd. split; [rewrite with_fds_halted; exact Hh | exact Hlazy].
  - intros e HIn.
    unfold ms. rewrite adv_eff_ret_copyins. apply Herr; assumption.
  - intros fd Hlk Hlt.
    unfold ms. rewrite adv_eff_ret_copyins. apply Hok; assumption.
  - exact HU.
Qed.

(* [comment removed for export] *)
Lemma tfo_open_wr_rec : forall regs pc mem model p
    (Te : Z -> (word * Fs.Fs) -> Prop) (Ts : word -> (word * Fs.Fs) -> Prop) U,
  bv_unsigned (getr regs 17) = 56%Z ->
  reg_get regs 10 = AT_FDCWD -> reg_get regs 12 = Z_to_bv 64 577 ->
  read_cstr (mrb segs mem) (reg_get regs 11) = CstrOk p ->
  path_eqb p [] = false ->
  openat_plain_name p = true ->
  fs_under (m_fs model) p = false ->       (* [comment removed for export] *)
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall e, In e openat_errnos ->
     to_fout segs (mkst (regupd regs 10 (errno_ret e)) (v_addi pc 4)
                        mem (seg_rom segs))
             model (Te e)) ->
  (forall fd, fd_lookup (m_fds model) fd = None -> fd = alloc_fd (m_fds model) ->
     to_fout segs (mkst (regupd regs 10 fd) (v_addi pc 4) mem (seg_rom segs))
             (with_fds (fd_insert (m_fds model) fd (FdFileW p (Z_to_bv 64 0)))
                (with_fs (fs_set (m_fs model) p []) model)) (Ts fd)) ->
  (forall o, U o <->
     ((exists e, In e openat_errnos /\ Te e o)
      \/ (exists fd, fd_lookup (m_fds model) fd = None
                     /\ fd = alloc_fd (m_fds model) /\ Ts fd o))) ->
  to_fout segs {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := (Z_to_bv 32 0); ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model p Te Ts U
    H17 H10 H12 Hpath Hpe Hdot Hfsu Hh Hlazy Herr Hok HU.
  set (ms := {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := (Z_to_bv 32 0); ms_mem := mem; ms_rom := seg_rom segs |}).
  apply (tfo_open_core ms model
           (fun fd => with_fds (fd_insert (m_fds model) fd
                                  (FdFileW p (Z_to_bv 64 0)))
                        (with_fs (fs_set (m_fs model) p []) model))
           (getr regs 17) (open_copyins ms) Te Ts U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact Hh.
  - exact Hlazy.
  - intro eff. apply (openat_wr_check segs ms (getr regs 17) model p).
    + exact H17.
    + unfold ms. rewrite record_gpr, arg_reg_0. exact H10.
    + unfold ms. rewrite record_gpr, arg_reg_1.
      rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
    + exact Hpe.
    + unfold ms. rewrite record_gpr, arg_reg_2. rewrite H12.
      vm_compute. reflexivity.
    + exact Hdot.
    + exact Hfsu.
  - intro fd. split.
    + rewrite with_fds_halted, with_fs_halted. exact Hh.
    + exact Hlazy.
  - intros e HIn.
    unfold ms. rewrite adv_eff_ret_copyins. apply Herr; assumption.
  - intros fd Hlk Hlt.
    unfold ms. rewrite adv_eff_ret_copyins. apply Hok; assumption.
  - exact HU.
Qed.

(* [comment removed for export] *)
Lemma tfo_open_toolong_rec : forall regs pc mem model U,
  bv_unsigned (getr regs 17) = 56%Z ->
  modeled_open_flags (reg_get regs 12) = true ->
  read_cstr (mrb segs mem) (reg_get regs 11) = CstrTooLong ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  to_fout segs (mkst (regupd regs 10 (errno_ret ENAMETOOLONG)) (v_addi pc 4)
                     mem (seg_rom segs))
          model U ->
  to_fout segs {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
                  ms_svc_pending := Some (getr regs 17);
                  ms_resv := None; ms_fcsr := (Z_to_bv 32 0); ms_mem := mem; ms_rom := seg_rom segs |}
          model U.
Proof.
  intros regs pc mem model U H17 Hfl Hpath Hh Hlazy Hcont.
  set (ms := {| ms_regs := regs; ms_fregs := bvmap_empty; ms_pc_val := pc;
                ms_svc_pending := Some (getr regs 17);
                ms_resv := None; ms_fcsr := (Z_to_bv 32 0); ms_mem := mem; ms_rom := seg_rom segs |}).
  apply (tfo_openat_toolong ms model (getr regs 17) U).
  - unfold ms. cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms. rewrite record_gpr, arg_reg_2. exact Hfl.
  - unfold ms. rewrite record_gpr, arg_reg_1.
    rewrite (ms_read_byte_rec_mrb segs). exact Hpath.
  - exact Hh.
  - exact Hlazy.
  - unfold ms. rewrite adv_eff_ret_copyins. exact Hcont.
Qed.

End OpenNodes.

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
