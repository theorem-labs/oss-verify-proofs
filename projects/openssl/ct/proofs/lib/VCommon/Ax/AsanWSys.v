(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import
  PropExec SimInv CatSim CatExec SeqExec FileSim ShapeAlg ShapeAlgCfg AgentLib AgentNodes Nodes NodesCfg
  NodesOpenCfg StoreOk.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Gen.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

(* [comment removed for export] *)
Lemma node_sys_nl : forall ms model x8 (I : Type)
    (E : I -> SyscallEffect) (M : I -> Model) (EV : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall i, syscall_spec (sys_input segs ms x8) model (Ok (E i) (M i) (EV i))) ->
  (forall i, ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model (E i)) ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) ->
     ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff ->
     exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  ~ syscall_spec (sys_input segs ms x8) model Unmodeled ->
  (forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) -> m_halted m' = None) ->
  (forall i, acc_ok (M i) (syscall_effect_accesses (E i))) ->
  node_ok_cfg segs cfg (mkCfg ms model) I EV
          (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)).
Proof.
  intros ms model x8 I E M EV Hh Hsvc Hcomp Hns Hsound Hnu Hnh Hacc. split.
  - intro i. apply (sstep_cfg_syscall segs cfg ms model x8 (E i) (M i) (M i) (EV i));
      [exact Hh | exact Hsvc | apply Hcomp | apply Hns | apply (Hnh _ _ _ (Hcomp i))
       | apply materialize_acc_ok; apply Hacc].
  - intros e st Hss. inversion Hss; subst;
      try (match goal with H1 : ms_svc_pending ms = None |- _ => rewrite Hsvc in H1; discriminate H1 end);
      match goal with H1 : ms_svc_pending ms = Some ?y |- _ =>
        rewrite Hsvc in H1; injection H1; intro; subst y end.
    + match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?e1), Hn : ~ spurious_refusal_cfg _ _ _ ?eff,
        Hm : materialize_model_accesses ?m1 _ = Some ?m2 |- _ =>
          destruct (Hsound _ _ _ Hs Hn) as (i & -> & -> & ->);
          rewrite (materialize_acc_ok _ _ (Hacc i)) in Hm;
          injection Hm; intro; subst m2; exists i; split; reflexivity
      end.
    + exfalso. match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?e1), Hn : ~ spurious_refusal_cfg _ _ _ ?eff,
        Hm : materialize_model_accesses ?m1 _ = None |- _ =>
          destruct (Hsound _ _ _ Hs Hn) as (i & -> & -> & ->);
          rewrite (materialize_acc_ok _ _ (Hacc i)) in Hm; discriminate Hm
      end.
    + exfalso. match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?e1), Hc : m_halted ?m1 = Some _ |- _ =>
          rewrite (Hnh _ _ _ Hs) in Hc; discriminate Hc
      end.
    + exfalso. match goal with
      | Hs : syscall_spec _ _ (Ok ?eff ?m1 ?e1), Hk : m_killed ?m1 = Some _ |- _ =>
          rewrite (m_killed_of_m_halted_none _ (Hnh _ _ _ Hs)) in Hk; discriminate Hk
      end.
    + exfalso. apply Hnu. assumption.
Qed.

(* [comment removed for export] *)
Lemma node_chk_nl : forall ms model x8 (chk : SyscallEffect -> check_result) (I : Type)
    (E : I -> SyscallEffect) (M : I -> Model) (EV : I -> list event),
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = chk eff) ->
  (forall i, chk (E i) = CheckOk (M i) (EV i)) ->
  (forall i, ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model (E i)) ->
  (forall eff m' evs, chk eff = CheckOk m' evs ->
     ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff ->
     exists i, eff = E i /\ m' = M i /\ evs = EV i) ->
  (forall eff m' evs, chk eff = CheckOk m' evs -> m_halted m' = None) ->
  chk (mkEffect (Z_to_bv 64 0) [] []) <> CheckUnmodeled ->
  (forall i, acc_ok (M i) (syscall_effect_accesses (E i))) ->
  node_ok_cfg segs cfg (mkCfg ms model) I EV
          (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)).
Proof.
  intros ms model x8 chk I E M EV Hh Hsvc Hchk Hok Hns Hinv Hnh Hnu Hacc.
  apply (node_sys_nl ms model x8 I E M EV Hh Hsvc).
  - intro i. apply check_syscall_ok_iff. rewrite Hchk. apply Hok.
  - exact Hns.
  - intros eff m' evs Hs Hn. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    exact (Hinv _ _ _ Hs Hn).
  - intro Hs.
    pose proof (proj2 (check_syscall_err_iff (sys_input segs ms x8)
                         (mkEffect (Z_to_bv 64 0) [] []) model) Hs) as Hs'.
    rewrite Hchk in Hs'. exact (Hnu Hs').
  - intros eff m' evs Hs. apply check_syscall_ok_iff in Hs. rewrite Hchk in Hs.
    exact (Hnh _ _ _ Hs).
  - exact Hacc.
Qed.

(* [comment removed for export] *)
Lemma rzc_ecall_nl : forall ms model w T,
  m_halted model = None -> ms_svc_pending ms = None ->
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = true ->
  realizes_cfg segs cfg (mkCfg (latch ms) model) T ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model w T Hh Hsvc HF HE Hc.
  eapply rzc_acc; [exact Hh | exact Hsvc | eapply wacc_Ecall; [exact HF | exact HE] | apply acc_ok_nil | exact Hc].
Qed.

End Gen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lg0 : forall S, ms_gpr (latch S) 0 = rg S 10. Proof. reflexivity. Qed.
Lemma lg1 : forall S, ms_gpr (latch S) 1 = rg S 11. Proof. reflexivity. Qed.
Lemma lg2 : forall S, ms_gpr (latch S) 2 = rg S 12. Proof. reflexivity. Qed.
Lemma lsvc : forall S, ms_svc_pending (latch S) = Some (rg S 17). Proof. reflexivity. Qed.

Lemma mrb_latch : forall segs S, ms_rom S = seg_rom segs -> ms_read_byte (latch S) = mrb segs (ms_mem S).
Proof. intros segs S H. unfold ms_read_byte, mrb, latch. cbn [ms_mem ms_rom]. rewrite H. reflexivity. Qed.

Lemma adv_ret_latch : forall S (r : word),
  advance_past_svc (set_gpr0 (latch S) r) = setx S 10 r (ms_pc_val S + Z_to_bv 64 4) (ms_resv S) (ms_mem S).
Proof. reflexivity. Qed.

Lemma adv_write_latch : forall S (r buf : word) (bs : list byte),
  advance_past_svc (apply_effect (latch S) (mkEffect r (delivered_writes buf bs) []))
  = setx S 10 r (ms_pc_val S + Z_to_bv 64 4) (ms_resv S) (write_to_mem (ms_mem S) buf bs).
Proof. intros S r buf bs. destruct bs; reflexivity. Qed.

Lemma with_fds_no_lazy : forall f model lo hi, no_lazy (with_fds f model) lo hi <-> no_lazy model lo hi.
Proof. intros f model lo hi. split; intros H; exact H. Qed.

(* [comment removed for export] *)
Lemma cstr_len_of_rdn : forall segs mem (p : list byte) (a : word) (fuel : nat),
  (length p < fuel)%nat -> ~ In (Z_to_bv 8 0) p ->
  rdn segs mem a (length p + 1) = Some (p ++ [Z_to_bv 8 0]) ->
  cstr_access_len_aux (mrb segs mem) a fuel = S (length p).
Proof.
  intros segs mem p. induction p as [|b p IH]; intros a fuel Hf Hnz Hr.
  - destruct fuel as [|fuel]; [cbn in Hf; lia|]. cbn [rdn length Nat.add app] in Hr.
    cbn [cstr_access_len_aux]. unfold mrb at 1.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end) as [b|] eqn:E; [|discriminate].
    injection Hr as ->. rewrite bv_eqb_refl. reflexivity.
  - destruct fuel as [|fuel]; [cbn in Hf; lia|]. cbn [rdn length Nat.add app] in Hr.
    cbn [cstr_access_len_aux]. unfold mrb at 1.
    destruct (match mem a with Some b => Some b | None => seg_rom segs a end) as [b'|] eqn:E; [|discriminate].
    destruct (rdn segs mem (a + 1) (length p + 1)) as [rest|] eqn:Er; [|discriminate].
    injection Hr as Eb Hrest. subst b' rest.
    assert (Hb : bv_eqb b (Z_to_bv 8 0) = false).
    { destruct (bv_eqb b (Z_to_bv 8 0)) eqn:Eb; [|reflexivity]. exfalso. apply Hnz. left.
      apply bv_eqb_eq in Eb. exact Eb. }
    rewrite Hb. f_equal. apply IH; [cbn in Hf; lia | intros Hin; apply Hnz; right; exact Hin | exact Er].
Qed.

Lemma cstr_len_toolong : forall segs mem (bs : list byte) (a : word),
  ~ In (Z_to_bv 8 0) bs -> rdn segs mem a (length bs) = Some bs ->
  cstr_access_len_aux (mrb segs mem) a (length bs) = length bs.
Proof.
  intros segs mem bs. induction bs as [|b bs IH]; intros a Hnz Hr; [reflexivity|].
  cbn [rdn length] in Hr. cbn [cstr_access_len_aux length]. unfold mrb at 1.
  destruct (match mem a with Some b => Some b | None => seg_rom segs a end) as [b'|] eqn:E; [|discriminate].
  destruct (rdn segs mem (a + 1) (length bs)) as [rest|] eqn:Er; [|discriminate].
  injection Hr as Eb Hrest. subst b' rest.
  assert (Hb : bv_eqb b (Z_to_bv 8 0) = false).
  { destruct (bv_eqb b (Z_to_bv 8 0)) eqn:Eb; [|reflexivity]. exfalso. apply Hnz. left.
    apply bv_eqb_eq in Eb. exact Eb. }
  rewrite Hb. f_equal. apply IH; [intros Hin; apply Hnz; right; exact Hin | exact Er].
Qed.

(* [comment removed for export] *)
Definition fds_std : list (word * FdEntry) :=
  [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
    (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
    (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ].

Lemma alloc_fd_std : alloc_fd fds_std = Z_to_bv 64 3.
Proof. vm_compute. reflexivity. Qed.

Lemma fd_lookup_std3 : fd_lookup fds_std (Z_to_bv 64 3) = None.
Proof. vm_compute. reflexivity. Qed.

Lemma fd_lookup_insert_same : forall fds (fd : word) e, fd_lookup (fd_insert fds fd e) fd = Some e.
Proof. intros fds fd e. unfold fd_insert, fd_lookup. cbn [find fst]. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma fd_remove_insert_std : forall e, fd_remove (fd_insert fds_std (Z_to_bv 64 3) e) (Z_to_bv 64 3) = fds_std.
Proof. intros e. reflexivity. Qed.

Lemma fd32_small : forall z : Z, (0 <= z < 2 ^ 32)%Z -> fd32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. apply fd32_id. rewrite bvu_z by lia. lia. Qed.

Lemma access_okb_of : forall (buf : word) (n : Z), (0 <= n)%Z -> (bv_unsigned buf + n <= TASK_SIZE)%Z ->
  access_okb buf n = true.
Proof.
  intros buf n H1 H2. unfold access_okb. pose proof (u64_range buf).
  apply andb_true_iff. split; [apply Z.leb_le | apply Z.leb_le]; lia.
Qed.

(* [comment removed for export] *)
Lemma open_flags_8000 : Z.ldiff (bv_unsigned (Z_to_bv 64 0x8000)) open_ignored_flags = 0%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma plain_name_of : forall p : list byte,
  ~ In (Z_to_bv 8 47) p -> p <> dot_path -> p <> dotdot_path -> openat_plain_name p = true.
Proof.
  intros p Hs Hd Hdd. unfold openat_plain_name, path_is_dirref, path_has_slash.
  destruct (path_eqb p dot_path) eqn:E1; [apply path_eqb_eq in E1; contradiction|].
  destruct (path_eqb p dotdot_path) eqn:E2; [apply path_eqb_eq in E2; contradiction|].
  cbn [orb negb andb].
  destruct (existsb (fun b => bv_eqb b slash_byte) p) eqn:E3; [|reflexivity].
  exfalso. apply existsb_exists in E3. destruct E3 as (b & Hb & Eb). apply bv_eqb_eq in Eb. subst b.
  exact (Hs Hb).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sys.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Hypothesis Hcfg : cfg_nonalloc_on cfg.

Lemma nospur_nl : forall ms x8 model eff (z : Z),
  bv_unsigned x8 = z -> negb (existsb (Z.eqb z) alloc_mark_sysnos) = true ->
  ~ spurious_refusal_cfg cfg (sys_input segs ms x8) model eff.
Proof.
  intros ms x8 model eff z Hz Hb. apply (nospur_nonalloc segs cfg ms x8 model eff Hcfg).
  exact (not_alloc_sysno x8 z Hz Hb).
Qed.

(* [comment removed for export] *)
Lemma rzc_det_nl : forall ms model x8 (z : Z) eff0 m' T,
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = z -> negb (existsb (Z.eqb z) alloc_mark_sysnos) = true ->
  (forall eff m2 evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m2 evs <->
                      (eff = eff0 /\ m2 = m' /\ evs = [])) ->
  check_syscall (sys_input segs ms x8) (mkEffect (Z_to_bv 64 0) [] []) model <> CheckUnmodeled ->
  m_halted m' = None ->
  acc_ok m' (syscall_effect_accesses eff0) ->
  realizes_cfg segs cfg (mkCfg (advance_past_svc (apply_effect ms eff0)) m') T ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model x8 z eff0 m' T Hh Hsvc Hz Hb Hiff Hnu Hh' Hacc Hc.
  eapply rzc_silent1; [|exact Hc].
  apply (node_chk_nl segs cfg ms model x8 (fun eff => check_syscall (sys_input segs ms x8) eff model) unit
           (fun _ => eff0) (fun _ => m') (fun _ => [])); [exact Hh | exact Hsvc | intros; reflexivity | | | | | | ].
  - intros []. apply Hiff. auto.
  - intros []. exact (nospur_nl ms x8 model eff0 z Hz Hb).
  - intros eff m2 evs Hs _. apply Hiff in Hs. destruct Hs as (-> & -> & ->). exists tt. auto.
  - intros eff m2 evs Hs. apply Hiff in Hs. destruct Hs as (_ & -> & _). exact Hh'.
  - exact Hnu.
  - intros []. exact Hacc.
Qed.

(* [comment removed for export] *)
Lemma rzc_ret_copyins_nl : forall ms model x8 (z : Z) reads r m' T,
  m_halted model = None -> ms_svc_pending ms = Some x8 ->
  bv_unsigned x8 = z -> negb (existsb (Z.eqb z) alloc_mark_sysnos) = true ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_ret_only_copyins reads eff r m' []) ->
  m_halted m' = None ->
  acc_ok m' reads ->
  realizes_cfg segs cfg (mkCfg (advance_past_svc (set_gpr0 ms r)) m') T ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model x8 z reads r m' T Hh Hsvc Hz Hb Hchk Hh' Hacc Hc.
  apply (rzc_det_nl ms model x8 z (with_copyins reads (mkEffect r [] [])) m' T Hh Hsvc Hz Hb).
  - intros eff m2 evs. rewrite Hchk. apply check_ret_only_copyins_ok_iff.
  - rewrite Hchk. apply check_ret_only_copyins_no_unmodeled.
  - exact Hh'.
  - unfold syscall_effect_accesses. cbn [eff_copyins eff_writes with_copyins write_accesses]. rewrite app_nil_r. exact Hacc.
  - rewrite apply_effect_copyins_no_write. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma rzc_open_nl : forall ms model x8 reads (mk : word -> Model) A B,
  m_halted model = None -> ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 56%Z ->
  (forall eff, check_syscall (sys_input segs ms x8) eff model = check_open_result_copyins reads eff model mk) ->
  (forall fd, m_halted (mk fd) = None) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  acc_ok model reads -> acc_ok (mk (alloc_fd (m_fds model))) reads ->
  (forall e, In e openat_errnos ->
     realizes_cfg segs cfg (mkCfg (advance_past_svc (set_gpr0 ms (errno_ret e))) model) A) ->
  realizes_cfg segs cfg (mkCfg (advance_past_svc (set_gpr0 ms (alloc_fd (m_fds model))))
                               (mk (alloc_fd (m_fds model)))) B ->
  realizes_cfg segs cfg (mkCfg ms model) (t_alt2 A B).
Proof.
  intros ms model x8 reads mk A B Hh Hsvc H56 Hchk Hmk Hfree Hacc1 Hacc2 HA HB.
  set (I := ({e : Z | In e openat_errnos} + unit)%type).
  set (E := fun i : I => match i with
                         | inl (exist _ e _) => with_copyins reads (mkEffect (errno_ret e) [] [])
                         | inr _ => with_copyins reads (mkEffect (alloc_fd (m_fds model)) [] [])
                         end).
  set (M := fun i : I => match i with inl _ => model | inr _ => mk (alloc_fd (m_fds model)) end).
  apply (rzc_alt2 segs cfg (mkCfg ms model) {e : Z | In e openat_errnos} unit
           (fun i => mkCfg (advance_past_svc (apply_effect ms (E i))) (M i)) A B
           (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
  - apply (node_chk_nl segs cfg ms model x8 (fun eff => check_open_result_copyins reads eff model mk) I E M (fun _ => []));
      [exact Hh | exact Hsvc | exact Hchk | | | | | | ].
    + intros [[e He] | []]; cbn [E M]; apply check_open_result_copyins_ok_iff.
      * left. exists e. auto.
      * right. exists (alloc_fd (m_fds model)). auto.
    + intros i. apply (nospur_nl ms x8 model (E i) 56); [exact H56 | reflexivity].
    + intros eff m2 evs Hc _. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(e & He & -> & -> & ->) | (fd & Hlk & -> & -> & -> & ->)].
      * exists (inl (exist _ e He)). cbn [E M]. auto.
      * exists (inr tt). cbn [E M]. auto.
    + intros eff m2 evs Hc. apply check_open_result_copyins_ok_iff in Hc.
      destruct Hc as [(e & He & _ & -> & _) | (fd & _ & _ & _ & -> & _)]; [exact Hh | apply Hmk].
    + apply check_open_result_copyins_never_unmodeled.
    + intros [[e He] | []]; cbn [E M]; unfold syscall_effect_accesses;
        cbn [eff_copyins eff_writes with_copyins write_accesses]; rewrite app_nil_r; assumption.
  - intros [e He]. cbn [E M]. rewrite apply_effect_copyins_no_write. exact (HA e He).
  - intros []. cbn [E M]. rewrite apply_effect_copyins_no_write. exact HB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Existing Instance PropExec.fx0.

Lemma open_acc_ok : forall S model (p : list byte),
  ms_rom S = seg_rom segs ->
  (length p <= 4095)%nat -> ~ In (Z_to_bv 8 0) p ->
  rdn segs (ms_mem S) (rg S 11) (length p + 1) = Some (p ++ [Z_to_bv 8 0]) ->
  (bv_unsigned (rg S 11) + Z.of_nat (length p) + 1 <= 2 ^ 64)%Z ->
  no_lazy model (bv_unsigned (rg S 11)) (bv_unsigned (rg S 11) + Z.of_nat (length p) + 1) ->
  acc_ok model (open_copyins (latch S)).
Proof.
  intros S model p Hrom Hlen Hnz Hr Hnw Hnl. unfold open_copyins. rewrite lg1, (mrb_latch segs S Hrom).
  rewrite (cstr_len_of_rdn segs (ms_mem S) p (rg S 11) path_max) by (try exact Hr; try exact Hnz; change path_max with 4096%nat; lia).
  apply acc_ok_one; rewrite Nat2Z.inj_succ; lia || (eapply no_lazy_sub; [exact Hnl | lia | lia]).
Qed.

Lemma path_cstr_latch : forall S (p : list byte),
  ms_rom S = seg_rom segs ->
  (length p <= 4095)%nat -> ~ In (Z_to_bv 8 0) p ->
  rdn segs (ms_mem S) (rg S 11) (length p + 1) = Some (p ++ [Z_to_bv 8 0]) ->
  read_cstr (ms_read_byte (latch S)) (ms_gpr (latch S) 1) = CstrOk p.
Proof.
  intros S p Hrom Hlen Hnz Hr. rewrite lg1, (mrb_latch segs S Hrom). apply read_cstr_of_rdn; assumption.
Qed.

Theorem rzc_openat_toolong_nl : forall ms model w (bs : list byte) K,
  ms_svc_pending ms = None -> ms_rom ms = seg_rom segs ->
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = true -> m_halted model = None ->
  rg ms 17 = Z_to_bv 64 56 ->
  Z.ldiff (bv_unsigned (rg ms 12)) open_ignored_flags = 0%Z ->
  rdn segs (ms_mem ms) (rg ms 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
  (bv_unsigned (rg ms 11) + 4096 <= 2 ^ 64)%Z ->
  no_lazy model (bv_unsigned (rg ms 11)) (bv_unsigned (rg ms 11) + 4096) ->
  realizes_cfg segs cfg
    (mkCfg (setx ms 10 (errno_ret ENAMETOOLONG) (ms_pc_val ms + Z_to_bv 64 4) (ms_resv ms) (ms_mem ms)) model) K ->
  realizes_cfg segs cfg (mkCfg ms model) K.
Proof.
  intros ms model w bs K Hsvc Hrom HF HE Hh H17 Hfl Hrd Hnz Hnw Hnl Hc.
  pose proof (rdn_length _ _ _ _ _ Hrd) as Hlen.
  eapply rzc_ecall_nl; [exact Hh | exact Hsvc | exact HF | exact HE |].
  apply (rzc_ret_copyins_nl (latch ms) model (rg ms 17) 56 (open_copyins (latch ms)) (errno_ret ENAMETOOLONG) model K
           Hh (lsvc ms)); [rewrite H17; reflexivity | reflexivity | | exact Hh | | ].
  - apply (openat_toolong_check segs (latch ms) (rg ms 17) model); [rewrite H17; reflexivity | rewrite lg2; exact (modeled_open_flags_rd _ Hfl) |].
    rewrite lg1, (mrb_latch segs ms Hrom). exact (read_cstr_toolong_of_rdn segs (ms_mem ms) (rg ms 11) bs Hlen Hnz Hrd).
  - unfold open_copyins. rewrite lg1, (mrb_latch segs ms Hrom). change path_max with 4096%nat.
    rewrite <- Hlen. rewrite (cstr_len_toolong segs (ms_mem ms) bs (rg ms 11) Hnz) by (rewrite Hlen; exact Hrd).
    rewrite Hlen. apply acc_ok_one; [exact Hnw | exact Hnl].
  - rewrite adv_ret_latch. exact Hc.
Qed.

Theorem rzc_openat_enoent_nl : forall ms model w (p : list byte) K,
  ms_svc_pending ms = None -> ms_rom ms = seg_rom segs ->
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = true -> m_halted model = None ->
  rg ms 17 = Z_to_bv 64 56 -> rg ms 10 = AT_FDCWD ->
  Z.ldiff (bv_unsigned (rg ms 12)) open_ignored_flags = 0%Z ->
  (length p <= 4095)%nat -> ~ In (Z_to_bv 8 0) p ->
  rdn segs (ms_mem ms) (rg ms 11) (length p + 1) = Some (p ++ [Z_to_bv 8 0]) ->
  (bv_unsigned (rg ms 11) + Z.of_nat (length p) + 1 <= 2 ^ 64)%Z ->
  no_lazy model (bv_unsigned (rg ms 11)) (bv_unsigned (rg ms 11) + Z.of_nat (length p) + 1) ->
  (p = [] \/ (openat_plain_name p = true /\ fs_lookup (m_fs model) p = None)) ->
  realizes_cfg segs cfg
    (mkCfg (setx ms 10 (errno_ret ENOENT) (ms_pc_val ms + Z_to_bv 64 4) (ms_resv ms) (ms_mem ms)) model) K ->
  realizes_cfg segs cfg (mkCfg ms model) K.
Proof.
  intros ms model w p K Hsvc Hrom HF HE Hh H17 H10 Hfl Hlen Hnz Hrd Hnw Hnl Hcase Hc.
  eapply rzc_ecall_nl; [exact Hh | exact Hsvc | exact HF | exact HE |].
  apply (rzc_ret_copyins_nl (latch ms) model (rg ms 17) 56 (open_copyins (latch ms)) (errno_ret ENOENT) model K
           Hh (lsvc ms)); [rewrite H17; reflexivity | reflexivity | | exact Hh | | ].
  - apply (openat_enoent_check segs (latch ms) (rg ms 17) model p); [rewrite H17; reflexivity | rewrite lg0; exact H10
      | exact (path_cstr_latch ms p Hrom Hlen Hnz Hrd) | rewrite lg2; exact Hfl |].
    destruct Hcase as [-> | Hpl]; [left; reflexivity | right; exact Hpl].
  - exact (open_acc_ok ms model p Hrom Hlen Hnz Hrd Hnw Hnl).
  - rewrite adv_ret_latch. exact Hc.
Qed.

Theorem rzc_openat_file_nl : forall ms model w (p : list byte) (d : list byte) KA KB,
  ms_svc_pending ms = None -> ms_rom ms = seg_rom segs ->
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = true -> m_halted model = None ->
  rg ms 17 = Z_to_bv 64 56 -> rg ms 10 = AT_FDCWD ->
  Z.ldiff (bv_unsigned (rg ms 12)) open_ignored_flags = 0%Z ->
  (length p <= 4095)%nat -> ~ In (Z_to_bv 8 0) p ->
  rdn segs (ms_mem ms) (rg ms 11) (length p + 1) = Some (p ++ [Z_to_bv 8 0]) ->
  (bv_unsigned (rg ms 11) + Z.of_nat (length p) + 1 <= 2 ^ 64)%Z ->
  no_lazy model (bv_unsigned (rg ms 11)) (bv_unsigned (rg ms 11) + Z.of_nat (length p) + 1) ->
  path_eqb p [] = false -> openat_plain_name p = true -> fs_lookup (m_fs model) p = Some d ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  (forall e, In e openat_errnos ->
     realizes_cfg segs cfg
       (mkCfg (setx ms 10 (errno_ret e) (ms_pc_val ms + Z_to_bv 64 4) (ms_resv ms) (ms_mem ms)) model) KA) ->
  realizes_cfg segs cfg
    (mkCfg (setx ms 10 (alloc_fd (m_fds model)) (ms_pc_val ms + Z_to_bv 64 4) (ms_resv ms) (ms_mem ms))
           (with_fds (fd_insert (m_fds model) (alloc_fd (m_fds model)) (FdFile p (Z_to_bv 64 0))) model)) KB ->
  realizes_cfg segs cfg (mkCfg ms model) (t_alt2 KA KB).
Proof.
  intros ms model w p d KA KB Hsvc Hrom HF HE Hh H17 H10 Hfl Hlen Hnz Hrd Hnw Hnl Hpe Hpl Hfs Hfree HA HB.
  pose proof (open_acc_ok ms model p Hrom Hlen Hnz Hrd Hnw Hnl) as Hacc.
  eapply rzc_ecall_nl; [exact Hh | exact Hsvc | exact HF | exact HE |].
  apply (rzc_open_nl (latch ms) model (rg ms 17) (open_copyins (latch ms))
           (fun fd => with_fds (fd_insert (m_fds model) fd (FdFile p (Z_to_bv 64 0))) model));
    [exact Hh | reflexivity | rewrite H17; reflexivity | | | exact Hfree | exact Hacc | | | ].
  - exact (openat_rd_check segs (latch ms) (rg ms 17) model p d ltac:(rewrite H17; reflexivity) ltac:(rewrite lg0; exact H10)
             (path_cstr_latch ms p Hrom Hlen Hnz Hrd) Hpe ltac:(rewrite lg2; exact Hfl) Hpl Hfs).
  - intros fd. exact Hh.
  - unfold acc_ok in *. exact Hacc.
  - intros e He. rewrite adv_ret_latch. exact (HA e He).
  - rewrite adv_ret_latch. exact HB.
Qed.

Theorem rzc_openat_dot_nl : forall ms model w KA KB,
  ms_svc_pending ms = None -> ms_rom ms = seg_rom segs ->
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = true -> m_halted model = None ->
  rg ms 17 = Z_to_bv 64 56 -> rg ms 10 = AT_FDCWD ->
  Z.ldiff (bv_unsigned (rg ms 12)) open_ignored_flags = 0%Z ->
  rdn segs (ms_mem ms) (rg ms 11) 2 = Some (dot_path ++ [Z_to_bv 8 0]) ->
  (bv_unsigned (rg ms 11) + 2 <= 2 ^ 64)%Z ->
  no_lazy model (bv_unsigned (rg ms 11)) (bv_unsigned (rg ms 11) + 2) ->
  fd_lookup (m_fds model) (alloc_fd (m_fds model)) = None ->
  (forall e, In e openat_errnos ->
     realizes_cfg segs cfg
       (mkCfg (setx ms 10 (errno_ret e) (ms_pc_val ms + Z_to_bv 64 4) (ms_resv ms) (ms_mem ms)) model) KA) ->
  realizes_cfg segs cfg
    (mkCfg (setx ms 10 (alloc_fd (m_fds model)) (ms_pc_val ms + Z_to_bv 64 4) (ms_resv ms) (ms_mem ms))
           (with_fds (fd_insert (m_fds model) (alloc_fd (m_fds model)) FdDir) model)) KB ->
  realizes_cfg segs cfg (mkCfg ms model) (t_alt2 KA KB).
Proof.
  intros ms model w KA KB Hsvc Hrom HF HE Hh H17 H10 Hfl Hrd Hnw Hnl Hfree HA HB.
  assert (Hlen : (length dot_path <= 4095)%nat) by (cbn; lia).
  assert (Hnz : ~ In (Z_to_bv 8 0) dot_path) by (cbn; intros [E|[]]; discriminate E).
  assert (Hrd' : rdn segs (ms_mem ms) (rg ms 11) (length dot_path + 1) = Some (dot_path ++ [Z_to_bv 8 0])) by exact Hrd.
  pose proof (open_acc_ok ms model dot_path Hrom Hlen Hnz Hrd' ltac:(change (Z.of_nat (length dot_path)) with 1%Z; lia)
                ltac:(change (Z.of_nat (length dot_path)) with 1%Z; eapply no_lazy_sub; [exact Hnl | lia | lia])) as Hacc.
  eapply rzc_ecall_nl; [exact Hh | exact Hsvc | exact HF | exact HE |].
  apply (rzc_open_nl (latch ms) model (rg ms 17) (open_copyins (latch ms))
           (fun fd => with_fds (fd_insert (m_fds model) fd FdDir) model));
    [exact Hh | reflexivity | rewrite H17; reflexivity | | | exact Hfree | exact Hacc | | | ].
  - exact (openat_dot_check segs (latch ms) (rg ms 17) model ltac:(rewrite H17; reflexivity) ltac:(rewrite lg0; exact H10)
             (path_cstr_latch ms dot_path Hrom Hlen Hnz Hrd') ltac:(rewrite lg2; exact Hfl)).
  - intros fd. exact Hh.
  - unfold acc_ok in *. exact Hacc.
  - intros e He. rewrite adv_ret_latch. exact (HA e He).
  - rewrite adv_ret_latch. exact HB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rzc_read_file_nl : forall ms model w (fd buf cnt : word) (p : list byte) (off : word) (data : list byte) K,
  ms_svc_pending ms = None -> ms_rom ms = seg_rom segs ->
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = true -> m_halted model = None ->
  rg ms 17 = Z_to_bv 64 63 -> rg ms 10 = fd -> rg ms 11 = buf -> rg ms 12 = cnt ->
  fd32 fd = fd ->
  fd_lookup (m_fds model) fd = Some (FdFile p off) ->
  fs_lookup (m_fs model) p = Some data ->
  store_ok segs (ms_mem ms) buf (Z.to_nat (bv_unsigned cnt)) = true ->
  (0 < bv_unsigned cnt)%Z -> (bv_unsigned cnt <= rw_bytes_max)%Z ->
  access_okb buf (bv_unsigned cnt) = true ->
  no_lazy model (bv_unsigned buf) (bv_unsigned buf + bv_unsigned cnt) ->
  realizes_cfg segs cfg
    (mkCfg (setx ms 10 (len_word (file_read data off cnt)) (ms_pc_val ms + Z_to_bv 64 4) (ms_resv ms)
                 (write_to_mem (ms_mem ms) buf (file_read data off cnt)))
           (with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word (file_read data off cnt)))) model)) K ->
  realizes_cfg segs cfg (mkCfg ms model) K.
Proof.
  intros ms model w fd buf cnt p off data K Hsvc Hrom HF HE Hh H17 H10 H11 H12 Hfd32 Hfd Hfs Hst Hpos Hcnt Haok Hnl Hcont.
  eapply rzc_ecall_nl; [exact Hh | exact Hsvc | exact HF | exact HE |].
  set (S := latch ms).
  assert (Hno : bv_unsigned (rg ms 17) = 63%Z) by (rewrite H17; reflexivity).
  assert (G0 : ms_gpr S 0 = fd) by (unfold S; rewrite lg0; exact H10).
  assert (G1 : ms_gpr S 1 = buf) by (unfold S; rewrite lg1; exact H11).
  assert (G2 : ms_gpr S 2 = cnt) by (unfold S; rewrite lg2; exact H12).
  destruct (read_bytes_map_of_store_ok segs (ms_mem ms) buf (Z.to_nat (bv_unsigned cnt)) Hst
              ltac:(pose proof (u64_range cnt); lia)) as (wv & Hw).
  rewrite Z2Nat.id in Hw by lia. rewrite Z_to_bv_bv_unsigned in Hw.
  change (wview segs (ms_mem ms)) with (ms_writable_byte segs S) in Hw.
  set (bs := file_read data off cnt).
  set (m1 := with_fds (fd_insert (m_fds model) fd (FdFile p (off + len_word bs))) model).
  assert (HL : (bv_unsigned (len_word bs) <= bv_unsigned cnt)%Z).
  { unfold len_word, bs. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
    pose proof (u64_range cnt) as Hc. rewrite length_file_read, Nat2Z.inj_min.
    unfold word_to_nat. rewrite Z.mod_small; lia. }
  assert (HLn : (Z.of_nat (length bs) <= bv_unsigned cnt)%Z).
  { unfold bs. rewrite length_file_read. unfold word_to_nat. pose proof (u64_range cnt). lia. }
  assert (Hchk : forall eff m' evs,
    check_syscall (sys_input segs S (rg ms 17)) eff model = CheckOk m' evs <->
    (eff = mkEffect (len_word bs) (delivered_writes buf bs) [] /\ m' = m1 /\ evs = [])).
  { intros eff m' evs.
    rewrite (check_syscall_63 segs S _ eff model Hno). unfold check_read.
    rewrite G0, G1, G2, Hfd32, Hfd. cbv beta iota.
    rewrite Haok. cbn [negb]. cbv beta iota.
    rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned.
    rewrite Hfs. cbv beta iota zeta.
    rewrite in_wmem_si. fold bs. fold m1.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw). cbv beta iota.
    destruct bs as [|b bsr].
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
        apply andb_true_iff in Hb as [Hb Hr].
        apply andb_true_iff in Hb as [Ha Hbs].
        apply bv_eqb_eq in Ha. apply bv_eqb_eq in Hr. apply listN_eqb_eq in Hbs.
        inversion H; subst. cbn [delivered_writes].
        repeat split; congruence.
      + intros (Heff & -> & ->). cbn [delivered_writes] in Heff.
        inversion Heff; subst.
        rewrite bv_eqb_refl. rewrite (proj2 (listN_eqb_eq _ _) eq_refl).
        rewrite bv_eqb_refl. cbn [andb]. reflexivity. }
  apply (rzc_det_nl S model (rg ms 17) 63 (mkEffect (len_word bs) (delivered_writes buf bs) []) m1 K
           Hh (lsvc ms) Hno eq_refl Hchk).
  - intros Hs.
    rewrite (check_syscall_63 segs S _ _ model Hno) in Hs. unfold check_read in Hs.
    rewrite G0, G1, G2, Hfd32, Hfd in Hs. cbv beta iota in Hs.
    rewrite Haok in Hs. cbn [negb] in Hs. cbv beta iota in Hs.
    rewrite (rw_count_clamp_of_rw _ Hcnt), Z_to_bv_bv_unsigned in Hs.
    rewrite Hfs in Hs. cbv beta iota zeta in Hs.
    rewrite in_wmem_si in Hs. fold bs in Hs.
    rewrite (read_bytes_map_prefix _ _ _ _ _ HL Hw) in Hs. cbv beta iota in Hs.
    revert Hs. destruct bs as [|b0 bsr]; intro Hs.
    + exact (check_ret_only_no_unmodeled _ _ _ _ Hs).
    + discriminate.
  - unfold m1. rewrite with_fds_halted. exact Hh.
  - unfold syscall_effect_accesses. cbn [eff_copyins eff_writes app].
    assert (Hwa : forall l : list byte, (Z.of_nat (length l) <= bv_unsigned cnt)%Z ->
                    acc_ok m1 (write_accesses (delivered_writes buf l))).
    { intros l Hl. destruct l as [|b0 l']; cbn [delivered_writes write_accesses]; [apply acc_ok_nil|].
      pose proof (proj1 (andb_true_iff _ _) Haok) as [_ Ha]. apply Z.leb_le in Ha. unfold TASK_SIZE in Ha.
      cbn [length] in *. apply acc_ok_one; [lia|].
      unfold m1. apply with_fds_no_lazy. eapply no_lazy_sub; [exact Hnl | lia | lia]. }
    apply Hwa. exact HLn.
  - unfold S. rewrite adv_write_latch. exact Hcont.
Qed.

Theorem rzc_read_dir_nl : forall ms model w K,
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = true -> m_halted model = None ->
  rg ms 17 = Z_to_bv 64 63 ->
  fd_lookup (m_fds model) (rg ms 10) = Some FdDir ->
  fd32 (rg ms 10) = rg ms 10 ->
  access_okb (rg ms 11) (bv_unsigned (rg ms 12)) = true ->
  realizes_cfg segs cfg
    (mkCfg (setx ms 10 (errno_ret EISDIR) (ms_pc_val ms + Z_to_bv 64 4) (ms_resv ms) (ms_mem ms)) model) K ->
  realizes_cfg segs cfg (mkCfg ms model) K.
Proof.
  intros ms model w K Hsvc HF HE Hh H17 Hfd Hfd32 Haok Hc.
  eapply rzc_ecall_nl; [exact Hh | exact Hsvc | exact HF | exact HE |].
  assert (Hno : bv_unsigned (rg ms 17) = 63%Z) by (rewrite H17; reflexivity).
  apply (rzc_det_nl (latch ms) model (rg ms 17) 63 (mkEffect (errno_ret EISDIR) [] []) model K Hh (lsvc ms) Hno eq_refl).
  - intros eff m2 evs. rewrite (read_dir_check segs (latch ms) (rg ms 17) model Hno); rewrite ?lg0, ?lg1, ?lg2; try assumption.
    apply check_ret_only_ok_iff.
  - rewrite (read_dir_check segs (latch ms) (rg ms 17) model Hno); rewrite ?lg0, ?lg1, ?lg2; try assumption.
    apply check_ret_only_no_unmodeled.
  - exact Hh.
  - apply acc_ok_nil.
  - exact Hc.
Qed.

Theorem rzc_close_nl : forall ms model w (fd : word) e K,
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = true -> m_halted model = None ->
  rg ms 17 = Z_to_bv 64 57 -> rg ms 10 = fd -> fd32 fd = fd ->
  fd_lookup (m_fds model) fd = Some e ->
  realizes_cfg segs cfg
    (mkCfg (setx ms 10 (Z_to_bv 64 0) (ms_pc_val ms + Z_to_bv 64 4) (ms_resv ms) (ms_mem ms))
           (with_fds (fd_remove (m_fds model) fd) model)) K ->
  realizes_cfg segs cfg (mkCfg ms model) K.
Proof.
  intros ms model w fd e K Hsvc HF HE Hh H17 H10 Hfd32 Hfd Hc.
  eapply rzc_ecall_nl; [exact Hh | exact Hsvc | exact HF | exact HE |].
  assert (Hno : bv_unsigned (rg ms 17) = 57%Z) by (rewrite H17; reflexivity).
  set (m1 := with_fds (fd_remove (m_fds model) fd) model).
  assert (Hchk : forall eff, check_syscall (sys_input segs (latch ms) (rg ms 17)) eff model
                             = check_ret_only eff (Z_to_bv 64 0) m1 []).
  { intro eff. rewrite (check_syscall_57 segs (latch ms) _ eff model Hno). unfold check_close.
    rewrite lg0, H10, Hfd32, Hfd. reflexivity. }
  apply (rzc_det_nl (latch ms) model (rg ms 17) 57 (mkEffect (Z_to_bv 64 0) [] []) m1 K Hh (lsvc ms) Hno eq_refl).
  - intros eff m2 evs. rewrite Hchk. apply check_ret_only_ok_iff.
  - rewrite Hchk. apply check_ret_only_no_unmodeled.
  - unfold m1. rewrite with_fds_halted. exact Hh.
  - apply acc_ok_nil.
  - exact Hc.
Qed.

End Sys.
