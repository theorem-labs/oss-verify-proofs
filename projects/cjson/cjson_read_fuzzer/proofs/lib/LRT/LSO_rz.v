(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require RelSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ExitSim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RzNodesImpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LMeasure.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cfg.
Module LRzAt.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RelSpec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ExitSim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LMeasure OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Strategy 1000 [path_max].

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.
Context {ACEIL : Ceil}.   (* [comment removed for export] *)

Local Abbreviation LRZ := (LRz.LRZ segs).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lrz_impl_enode : forall {A} n (dec : resp -> option A) (Q : A -> machine_state -> Prop) ms mo g K,
  impl segs (at_node segs) (enode n dec) (epost Q) ms ->
  (forall ms1, at_node segs n ms1 ->
     (forall rsp' a mo' g' K', dec rsp' = Some a ->
        (forall ms2, Q a ms2 -> LRZ ms2 mo' g' K') ->
        LRZ (nret ms1 rsp') mo' g' K') ->
     LRZ ms1 mo g K) ->
  LRZ ms mo g K.
Proof.
  intros A n dec Q ms mo g K Himpl Hnode.
  cbn in Himpl. eapply lrz_evt; [exact Himpl|].
  intros ms1 [Hat Hk]. apply (Hnode ms1 Hat).
  intros rsp' a mo' g' K' Hdec HK. specialize (Hk rsp'). rewrite Hdec in Hk. cbn in Hk.
  eapply lrz_evt; [exact Hk|]. intros ms2 HQ. apply HK. exact HQ.
Qed.

(* [comment removed for export] *)
Lemma areg_msw : forall ms mr r, areg (msw ms mr) r = areg ms r.
Proof. reflexivity. Qed.

Lemma in_mem_msw : forall ms mr x8, ms_rom ms = seg_rom segs ->
  in_mem (sys_input segs (msw ms mr) x8) = mrd segs mr.
Proof.
  intros ms mr x8 Hrom. rewrite in_mem_si. unfold ms_read_byte. cbn [ms_mem ms_rom msw]. rewrite Hrom. reflexivity.
Qed.

Lemma in_wmem_msw : forall ms mr x8, in_wmem (sys_input segs (msw ms mr) x8) = wview segs mr.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma msw_nret_plain : forall ms r, msw (nret ms (mkEffect r [] [])) (ms_mem ms) = nret ms (mkEffect r [] []).
Proof.
  intros ms r. transitivity (msw (nret ms (mkEffect r [] [])) (ms_mem (nret ms (mkEffect r [] []))));
    [rewrite mem_nret_plain; reflexivity| apply msw_nret_self].
Qed.

(* [comment removed for export] *)
Lemma lrz_det_plain : forall ms mo mo' g x8 r K,
  ms_svc_pending ms = Some x8 -> alloc_no_b (bv_unsigned x8) = false ->
  (forall mr mat, LINV segs g mo mat (ms_mem ms) mr ->
     forall o, syscall_spec (sys_input segs (msw ms mr) x8) (real mo mat) o <-> o = Ok (mkEffect r [] []) (real mo' mat) []) ->
  (forall mr mat, LINV segs g mo mat (ms_mem ms) mr -> LINV segs g mo' mat (ms_mem ms) mr) ->
  LRZ (nret ms (mkEffect r [] [])) mo' g K ->
  LRZ ms mo g K.
Proof.
  intros ms mo mo' g x8 r K Hsvc Hb Hiff HI' HK.
  apply (lrz_node_silent segs ms mo g x8 unit tt K Hsvc Hb).
  intros mr mat HI. exists (fun _ => mkEffect r [] []), (fun _ => mo'), (fun _ => g), (fun _ => ms_mem ms), (fun _ => mat).
  split.
  - intros o. rewrite (Hiff mr mat HI o). split; [intros ->; exists tt; reflexivity| intros [[] ->]; reflexivity].
  - intros []. split; [exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ (HI' mr mat HI)))|]. split; [apply materialize_model_accesses_nil|]. split.
    + rewrite mem_nret_plain. cbn [ms_mem msw]. apply HI'. exact HI.
    + rewrite msw_nret_plain. exact HK.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lrz_at_read_file : forall ms mo g (fd buf cnt : Z) p off data K,
  at_node segs (NRead fd buf cnt) ms ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) -> fs_lookup (m_fs mo) p = Some data ->
  0 <= cnt <= rw_bytes_max -> buf + cnt <= TASK_SIZE ->   (* [comment removed for export] *)
  let bs := file_read data off (Z_to_bv 64 cnt) in
  LRZ (nret ms (mkEffect (Z_to_bv 64 (Z.of_nat (length bs))) (delivered_writes (Z_to_bv 64 buf) bs) []))
      (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + Z_to_bv 64 (Z.of_nat (length bs)))%bv)) mo) g K ->
  LRZ ms mo g K.
Proof.
  intros ms mo g fd buf cnt p off data K Hat Hlk Hfs Hcnt Hnw bs HK.
  cbn [at_node] in Hat. destruct Hat as (Hsvc & Hfd & H10 & H11 & H12 & _ & Hwr).
  rewrite rw_bytes_max_val in Hcnt. rewrite TASK_SIZE_val in Hnw.
  pose proof Hwr as (Hb0 & _ & _).
  pose proof (length_file_read_le data off cnt ltac:(lia)) as Hlen. fold bs in Hlen.
  set (eff := mkEffect (Z_to_bv 64 (Z.of_nat (length bs))) (delivered_writes (Z_to_bv 64 buf) bs) []) in *.
  set (mo' := with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + Z_to_bv 64 (Z.of_nat (length bs)))%bv)) mo) in *.
  apply (lrz_node_silent segs ms mo g (Z_to_bv 64 63) unit tt K Hsvc eq_refl).
  intros mr mat HI.
  pose proof (wr_at_real _ _ _ _ _ _ _ _ HI Hwr) as Hwr'.
  destruct (read_bytes_map_wr_at segs mr buf cnt Hwr' ltac:(lia)) as [w Hw].
  assert (HI1 : LINV segs g mo' mat (write_to_mem (ms_mem ms) (wa buf) bs) (write_to_mem mr (wa buf) bs)).
  { unfold mo'. apply LINV_with_fds. apply LINV_write; [exact HI|]. pose proof Hwr as (A0 & A1 & AW). split; [lia|]. split; [lia|]. intros i Hi. apply AW. lia. }
  assert (ACC : forall a n, In (a, n) (syscall_effect_accesses eff) -> forall k, (k < n)%nat -> vis segs (write_to_mem (ms_mem ms) (wa buf) bs) (boff a k)).
  { intros a n Hin k Hk. unfold eff in Hin.
    cbv beta iota delta [syscall_effect_accesses eff_copyins eff_writes app] in Hin.
    destruct bs as [|b bs'] eqn:Ebs; cbn [delivered_writes write_accesses] in Hin; [destruct Hin|].
    destruct Hin as [Hin|[]].
    pose proof (f_equal fst Hin) as Ha. pose proof (f_equal snd Hin) as Hn. cbn [fst snd] in Ha, Hn. subst a n.
    change (Z_to_bv 64 buf) with (wa buf). apply vis_write; cbn [length] in *; lia. }
  destruct (lmaterialize segs g mo' mat _ _ (syscall_effect_accesses eff) HI1 ACC) as [Hmat HI2].
  exists (fun _ => eff), (fun _ => mo'), (fun _ => g), (fun _ => write_to_mem (ms_mem ms) (wa buf) bs),
    (fun _ => newly_materialized_pages (m_vm_lazy mo') mat (syscall_effect_accesses eff) ++ mat).
  split.
  - intros o.
    unshelve epose proof (read_file_outcome_i (sys_input segs (msw ms mr) (Z_to_bv 64 63))
               (real mo mat) (Z_to_bv 64 fd) (Z_to_bv 64 buf) (Z_to_bv 64 cnt) p off data w _ _ _ _ _ _ _ _ _ _ o) as RW.
    all: try (first [ rewrite in_sysno_pending; reflexivity
                    | rewrite in_a0_si, areg_msw; exact H10
                    | rewrite in_a1_si, areg_msw; exact H11
                    | rewrite in_a2_si, areg_msw; exact H12
                    | rewrite m_fds_real; exact Hlk
                    | rewrite m_fs_real; exact Hfs
                    | rewrite in_wmem_msw; exact Hw
                    | rewrite u64_lit by lia; rewrite rw_bytes_max_val; lia
                    | rewrite !u64_lit by lia; rewrite TASK_SIZE_val; lia
                    | rewrite u64_lit; lia ]).
    cbv zeta in RW. rewrite RW. unfold eff, mo'. rewrite real_with_fds, m_fds_real. fold bs. rewrite <- len_word_of by lia.
    split; [intros ->; exists tt; reflexivity| intros [[] ->]; reflexivity].
  - intros []. split; [exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI))|]. split; [exact Hmat|]. split.
    + unfold eff. rewrite mem_nret_delivered. cbn [ms_mem msw]. exact HI2.
    + replace (write_to_mem (ms_mem ms) (wa buf) bs) with (ms_mem (nret ms eff)).
      * rewrite msw_nret_self. exact HK.
      * unfold eff. rewrite mem_nret_delivered. reflexivity.
Qed.

Lemma lrz_at_read_dir : forall ms mo g (fd buf cnt : Z) K,
  at_node segs (NRead fd buf cnt) ms ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdDir ->
  0 <= cnt <= rw_bytes_max -> buf + cnt <= TASK_SIZE ->   (* [comment removed for export] *)
  LRZ (nret ms (efferr EISDIR)) mo g K ->
  LRZ ms mo g K.
Proof.
  intros ms mo g fd buf cnt K Hat Hlk Hcnt Hnw HK.
  cbn [at_node] in Hat. destruct Hat as (Hsvc & Hfd & H10 & H11 & H12 & _ & Hwr).
  rewrite rw_bytes_max_val in Hcnt. rewrite TASK_SIZE_val in Hnw.
  pose proof Hwr as (Hb0 & _ & _).
  apply (lrz_det_plain ms mo mo g (Z_to_bv 64 63) (errno_ret EISDIR) K Hsvc eq_refl); [| auto| exact HK].
  intros mr mat HI o.
    rewrite (syscall_spec_63 _ _ o) by (rewrite in_sysno_pending; reflexivity).
    rewrite in_a0_si, in_a1_si, in_a2_si, !areg_msw, H10, H11, H12, fd32_id by (rewrite u64_lit; lia).
    apply (read_dir_outcome _ _ _ _ (real mo mat) o); [rewrite m_fds_real; exact Hlk|].
    apply access_okb_intro. rewrite !u64_lit by lia. rewrite TASK_SIZE_val. lia.
Qed.

Lemma lrz_impl_read_file : forall (Q : read_ans -> machine_state -> Prop) ms mo g (fd buf cnt : Z) p off data K,
  impl segs (at_node segs) (enode (NRead fd buf cnt) (dec_read buf cnt)) (epost Q) ms ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdFile p off) -> fs_lookup (m_fs mo) p = Some data ->
  0 <= cnt <= rw_bytes_max -> buf + cnt <= TASK_SIZE ->   (* [comment removed for export] *)
  let bs := file_read data off (Z_to_bv 64 cnt) in
  (forall ms2, Q (RdData bs) ms2 ->
     LRZ ms2 (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 fd) (FdFile p (off + Z_to_bv 64 (Z.of_nat (length bs)))%bv)) mo) g K) ->
  LRZ ms mo g K.
Proof.
  intros Q ms mo g fd buf cnt p off data K Himpl Hlk Hfs Hcnt Hnw bs HK.
  rewrite rw_bytes_max_val in Hcnt. rewrite TASK_SIZE_val in Hnw.
  apply (lrz_impl_enode (NRead fd buf cnt) (dec_read buf cnt) Q ms mo g K Himpl).
  intros ms1 Hat Hcont.
  apply (lrz_at_read_file ms1 mo g fd buf cnt p off data K Hat Hlk Hfs Hcnt Hnw).
  apply (Hcont _ (RdData bs) _ g K); [| exact HK].
  apply dec_read_file_ok; [lia|]. apply length_file_read_le. lia.
Qed.

Lemma lrz_impl_read_dir : forall (Q : read_ans -> machine_state -> Prop) ms mo g (fd buf cnt : Z) K,
  impl segs (at_node segs) (enode (NRead fd buf cnt) (dec_read buf cnt)) (epost Q) ms ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some FdDir ->
  0 <= cnt <= rw_bytes_max -> buf + cnt <= TASK_SIZE ->   (* [comment removed for export] *)
  (forall ms2, Q (RdErr EISDIR) ms2 -> LRZ ms2 mo g K) ->
  LRZ ms mo g K.
Proof.
  intros Q ms mo g fd buf cnt K Himpl Hlk Hcnt Hnw HK.
  apply (lrz_impl_enode (NRead fd buf cnt) (dec_read buf cnt) Q ms mo g K Himpl).
  intros ms1 Hat Hcont.
  apply (lrz_at_read_dir ms1 mo g fd buf cnt K Hat Hlk Hcnt Hnw).
  apply (Hcont _ (RdErr EISDIR) _ g K); [| exact HK].
  unfold dec_read, efferr, eff0. rewrite errno_of_errno_ret by (unfold EISDIR; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lrz_at_close : forall ms mo g (fd : Z) e K,
  at_node segs (NClose fd) ms ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some e ->
  LRZ (nret ms (eff0 (Z_to_bv 64 0))) (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo) g K ->
  LRZ ms mo g K.
Proof.
  intros ms mo g fd e K Hat Hlk HK.
  cbn [at_node] in Hat. destruct Hat as (Hsvc & Hfd & H10).
  apply (lrz_det_plain ms mo (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo) g (Z_to_bv 64 57) (Z_to_bv 64 0) K Hsvc eq_refl);
    [| intros; apply LINV_with_fds; assumption| exact HK].
  intros mr mat HI o. rewrite (syscall_spec_57 _ _ o) by (rewrite in_sysno_pending; reflexivity).
  rewrite in_a0_si, areg_msw, H10, fd32_id by (rewrite u64_lit; lia).
  rewrite (close_outcome _ _ (real mo mat) e o) by (rewrite m_fds_real; exact Hlk).
  rewrite m_fds_real, real_with_fds. reflexivity.
Qed.

Lemma lrz_impl_close : forall (Q : sret -> machine_state -> Prop) ms mo g (fd : Z) e K,
  impl segs (at_node segs) (enode (NClose fd) dec_close) (epost Q) ms ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some e ->
  (forall ms2, Q (SVal 0) ms2 -> LRZ ms2 (with_fds (fd_remove (m_fds mo) (Z_to_bv 64 fd)) mo) g K) ->
  LRZ ms mo g K.
Proof.
  intros Q ms mo g fd e K Himpl Hlk HK.
  apply (lrz_impl_enode (NClose fd) dec_close Q ms mo g K Himpl).
  intros ms1 Hat Hcont. apply (lrz_at_close ms1 mo g fd e K Hat Hlk).
  apply (Hcont _ (SVal 0) _ g K); [| exact HK].
  unfold dec_close. apply dec_plain_val; [lia | reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lrz_at_ioctl : forall ms mo g (fd req : Z) e K,
  at_node segs (NIoctl fd req) ms ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some e ->
  e <> FdUrandom ->     (* [comment removed for export] *)
  LRZ (nret ms (efferr ENOTTY)) mo g K ->
  LRZ ms mo g K.
Proof.
  intros ms mo g fd req e K Hat Hlk Hnd HK.
  cbn [at_node] in Hat. destruct Hat as (Hsvc & Hfd & -> & H10 & H11).
  apply (lrz_det_plain ms mo mo g (Z_to_bv 64 29) (errno_ret ENOTTY) K Hsvc eq_refl); [| auto| exact HK].
  intros mr mat HI o. rewrite (syscall_spec_29 _ _ o) by (rewrite in_sysno_pending; reflexivity).
  rewrite in_a0_si, in_a1_si, !areg_msw, H10, H11, fd32_id by (rewrite u64_lit; lia).
  apply (ioctl_tty_outcome (Z_to_bv 64 fd) _ _ (real mo mat) e o); [rewrite m_fds_real; exact Hlk| exact Hnd|]. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lrz_at_exit : forall ms mo g code,
  at_node segs (NExit code) ms -> 0 <= code < 256 ->
  LRZ ms mo g (t_exit (Z_to_bv 64 code) (m_fs mo)).
Proof.
  intros ms mo g code Hat Hc mr mat HI. cbn [at_node] in Hat. destruct Hat as [Hsvc H10].
  rewrite <- (m_fs_real mo mat). apply srealizes_of_realizes.
  rewrite <- (bv_and_255_small code Hc), <- H10. change (areg ms 10) with (ms_gpr (msw ms mr) 0).
  pose proof (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI)) as Hh. rewrite <- (real_halted mo mat) in Hh.
  destruct Hsvc as [Hs|Hs]; (eapply ShapeAlg.rz_exit; [exact Hh | rewrite ms_svc_pending_msw; exact Hs | ]); [apply is_exit_no_93 | apply is_exit_no_94].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cstr_access_len_aux_le : forall mp a fuel, (cstr_access_len_aux mp a fuel <= fuel)%nat.
Proof.
  intros mp a fuel. revert a. induction fuel as [|fuel IH]; intros a; cbn [cstr_access_len_aux]; [lia|].
  destruct (mp a) as [b|]; [| lia]. destruct (bv_eqb b (Z_to_bv 8 0)); [lia|]. specialize (IH (a + 1)%bv). lia.
Qed.

Section Openat.
  Variables (ms : machine_state) (mo : Model) (g : lghost) (path : list byte).
  Hypothesis Hat : at_node segs (NOpen path) ms.

  Let x8 := Z_to_bv 64 56.
  Let rin (mr : mem) := sys_input segs (msw ms mr) x8.
  Let fds := m_fds mo.

  Lemma lopen_at_facts :
    ms_svc_pending ms = Some x8 /\ areg ms 10 = AT_FDCWD /\
    Z.ldiff (bv_unsigned (areg ms 12)) open_ignored_flags = 0 /\ ~ In (Z_to_bv 8 0) path /\
    ms_rom ms = seg_rom segs /\ bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0]).
  Proof.
    cbn [at_node] in Hat. destruct Hat as (Hsvc & H10 & Hfl & Hnz & Hrom & Hb).
    refine (conj Hsvc (conj H10 (conj _ (conj Hnz (conj Hrom Hb))))). apply open_flags_at_node. exact Hfl.
  Qed.

  Lemma lopenat_head_at : forall mr mat o,
    syscall_spec (rin mr) (real mo mat) o <-> openat_spec AT_FDCWD32 (areg ms 11) (areg ms 12) (rin mr) (real mo mat) o.
  Proof.
    intros mr mat o. destruct lopen_at_facts as (Hsvc & H10 & _).
    unfold rin. rewrite (syscall_spec_56 _ _ o) by (rewrite in_sysno_pending; reflexivity).
    rewrite in_a0_si, in_a1_si, in_a2_si, !areg_msw, H10. reflexivity.
  Qed.

  Lemma lopen_flags_modeled_at : modeled_open_flags (areg ms 12) = true.
  Proof. destruct lopen_at_facts as (_ & _ & Hfl & _). exact (modeled_open_flags_rd _ Hfl). Qed.

  Lemma lpath_bytes_in : forall mr mat, LINV segs g mo mat (ms_mem ms) mr ->
    bytes_in (in_mem (rin mr)) (bv_unsigned (areg ms 11)) (path ++ [Z_to_bv 8 0]).
  Proof.
    intros mr mat HI. destruct lopen_at_facts as (_ & _ & _ & _ & Hrom & Hb).
    unfold rin. rewrite (in_mem_msw ms mr x8 Hrom). eapply bytes_in_real; [exact HI| exact Hb].
  Qed.

  Lemma lpath_cstr_at : forall mr mat, LINV segs g mo mat (ms_mem ms) mr ->
    (length path <= 4095)%nat -> read_cstr (in_mem (rin mr)) (areg ms 11) = CstrOk path.
  Proof.
    intros mr mat HI Hlen. destruct lopen_at_facts as (_ & _ & _ & Hnz & _). unfold read_cstr.
    rewrite <- (wa_unsigned_id (areg ms 11)). apply read_cstr_aux_bytes_in; [unfold path_max; lia | exact Hnz | exact (lpath_bytes_in mr mat HI)].
  Qed.

  Lemma lpath_toolong_at : forall mr mat, LINV segs g mo mat (ms_mem ms) mr ->
    (4096 <= length path)%nat -> read_cstr (in_mem (rin mr)) (areg ms 11) = CstrTooLong.
  Proof.
    intros mr mat HI Hlen. destruct lopen_at_facts as (_ & _ & _ & Hnz & _). unfold read_cstr.
    rewrite <- (wa_unsigned_id (areg ms 11)). pose proof (lpath_bytes_in mr mat HI) as Hb. apply bytes_in_app in Hb as [Hb _].
    apply (read_cstr_aux_toolong_bytes_in path_max path); [unfold path_max; lia | exact Hnz | exact Hb].
  Qed.

  (* [comment removed for export] *)
  Lemma lopen_reads_vis : forall mr mat, LINV segs g mo mat (ms_mem ms) mr ->
    forall a n, In (a, n) (open_reads (rin mr) (areg ms 11)) -> forall k, (k < n)%nat -> vis segs (ms_mem ms) (boff a k).
  Proof.
    intros mr mat HI a n [Hin|[]] k Hk. destruct lopen_at_facts as (_ & _ & _ & Hnz & Hrom & Hb3).
    pose proof (f_equal fst Hin) as Ha. pose proof (f_equal snd Hin) as Hn. cbn [fst snd] in Ha, Hn. subst a n. clear Hin.
    pose proof (lpath_bytes_in mr mat HI) as HB. unfold rin in Hk, HB. rewrite (in_mem_msw ms mr x8 Hrom) in Hk, HB.
    rewrite <- (wa_unsigned_id (areg ms 11)) in Hk |- *.
    set (q := Nat.min (length path) path_max).
    assert (Hq : (cstr_access_len_aux (mrd segs mr) (wa (bv_unsigned (areg ms 11))) path_max <= length path + 1)%nat).
    { destruct (Nat.le_gt_cases (length path) path_max) as [Hle|Hgt].
      - rewrite (cstr_len_prefix path); [| exact Hle|].
        + destruct (path_max - length path)%nat as [|f] eqn:Ef; cbn [cstr_access_len_aux]; [lia|].
          rewrite (bytes_in_boff _ _ _ (length path) HB) by (rewrite length_app; cbn; lia).
          rewrite nth_error_app2, Nat.sub_diag by lia. cbn [nth_error]. rewrite bv_eqb_refl. lia.
        + intros i Hi. exists (nth i path (Z_to_bv 8 0)). split.
          * rewrite (bytes_in_boff _ _ _ i HB) by (rewrite length_app; cbn; lia). rewrite nth_error_app1 by lia.
            apply nth_error_nth'. exact Hi.
          * intros E. apply Hnz. rewrite <- E. apply nth_In. exact Hi.
      - pose proof (cstr_access_len_aux_le (mrd segs mr) (wa (bv_unsigned (areg ms 11))) path_max). lia. }
    destruct Hb3 as (A0 & A1 & A3). rewrite length_app in A1. cbn [length] in A1.
    pose proof (A3 k ltac:(rewrite length_app; cbn; lia)) as Hr.
    destruct (nth_error (path ++ [Z_to_bv 8 0]) k) eqn:En; [| apply nth_error_None in En; rewrite length_app in En; cbn in En; lia].
    apply (vis_of_mrd segs (ms_mem ms) _ b). unfold boff. rewrite wa_add_nat, wa_unsigned by lia. exact Hr.
  Qed.

  Lemma lrz_at_openat_det : forall r K,
    (forall mr mat, LINV segs g mo mat (ms_mem ms) mr ->
       forall o, syscall_spec (rin mr) (real mo mat) o <-> o = Ok (with_copyins (open_reads (rin mr) (areg ms 11)) (mkEffect r [] [])) (real mo mat) []) ->
    LRZ (nret ms (eff0 r)) mo g K ->
    LRZ ms mo g K.
  Proof.
    intros r K Hiff HK. destruct lopen_at_facts as (Hsvc & _).
    apply (lrz_node_silent segs ms mo g x8 unit tt K Hsvc eq_refl).
    intros mr mat HI.
    set (eff := with_copyins (open_reads (rin mr) (areg ms 11)) (mkEffect r [] [])).
    assert (ACC : forall a n, In (a, n) (syscall_effect_accesses eff) -> forall k, (k < n)%nat -> vis segs (ms_mem ms) (boff a k)).
    { intros a n Hin. unfold eff in Hin.
      cbv beta iota delta [syscall_effect_accesses with_copyins eff_copyins eff_writes eff_ret eff_zeros eff_unmaps eff_copies write_accesses] in Hin.
      rewrite app_nil_r in Hin. exact (lopen_reads_vis mr mat HI a n Hin). }
    destruct (lmaterialize segs g mo mat (ms_mem ms) mr (syscall_effect_accesses eff) HI ACC) as [Hmat HI2].
    exists (fun _ => eff), (fun _ => mo), (fun _ => g), (fun _ => ms_mem ms),
      (fun _ => newly_materialized_pages (m_vm_lazy mo) mat (syscall_effect_accesses eff) ++ mat).
    split.
    - intros o. fold (rin mr). rewrite (Hiff mr mat HI o). split; [intros ->; exists tt; reflexivity| intros [[] ->]; reflexivity].
    - intros []. split; [exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI))|]. split; [exact Hmat|]. split.
      + unfold eff. rewrite nret_copyins'. unfold eff0. rewrite mem_nret_plain. cbn [ms_mem msw]. exact HI2.
      + unfold eff. rewrite nret_copyins'. unfold eff0. rewrite msw_nret_plain. exact HK.
  Qed.

  Lemma lrz_at_openat_toolong : forall K, (4096 <= length path)%nat ->
    LRZ (nret ms (efferr ENAMETOOLONG)) mo g K -> LRZ ms mo g K.
  Proof.
    intros K Hlen HK. apply lrz_at_openat_det with (r := errno_ret ENAMETOOLONG); [|exact HK].
    intros mr mat HI o. rewrite lopenat_head_at. apply (openat_toolong_outcome _ _ _ _ (real mo mat) lopen_flags_modeled_at).
    exact (lpath_toolong_at mr mat HI Hlen).
  Qed.

  Lemma lrz_at_openat_empty : forall K, path = [] ->
    LRZ (nret ms (efferr ENOENT)) mo g K -> LRZ ms mo g K.
  Proof.
    intros K Hp HK. apply lrz_at_openat_det with (r := errno_ret ENOENT); [|exact HK].
    intros mr mat HI o. rewrite lopenat_head_at. apply (openat_empty_outcome _ _ _ _ (real mo mat) lopen_flags_modeled_at).
    rewrite <- Hp. apply (lpath_cstr_at mr mat HI). rewrite Hp. cbn. lia.
  Qed.

  Lemma lrz_at_openat_absent : forall K, (length path <= 4095)%nat -> path <> [] -> path <> dot_path -> path <> dotdot_path -> path_has_slash path = false ->
    fs_lookup (m_fs mo) path = None ->
    LRZ (nret ms (efferr ENOENT)) mo g K -> LRZ ms mo g K.
  Proof.
    intros K Hlen Hne Hnd Hndd Hsl Hfs HK. apply lrz_at_openat_det with (r := errno_ret ENOENT); [|exact HK].
    destruct lopen_at_facts as (_ & _ & Hfl & _).
    intros mr mat HI o. rewrite lopenat_head_at.
    apply (openat_absent_outcome _ _ _ _ (real mo mat) lopen_flags_modeled_at eq_refl Hfl path);
      [exact (lpath_cstr_at mr mat HI Hlen) | exact Hne | exact Hnd | exact Hndd | exact Hsl | rewrite m_fs_real; exact Hfs].
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.

  Lemma lrz_at_openat_open : forall (mk : word -> Model -> Model) KA KB,
    (forall mr mat, LINV segs g mo mat (ms_mem ms) mr -> forall o,
        syscall_spec (rin mr) (real mo mat) o <->
        open_out (open_reads (rin mr) (areg ms 11)) (real mo mat) (fun fd => mk fd (real mo mat)) o) ->
    (forall fd mo1 mat1, mk fd (real mo1 mat1) = real (mk fd mo1) mat1) ->
    (forall fd mo1, m_halted (mk fd mo1) = m_halted mo1) ->
    (forall fd mo1 mat1 mv1 mr1 g1, LINV segs g1 mo1 mat1 mv1 mr1 -> LINV segs g1 (mk fd mo1) mat1 mv1 mr1) ->
    (forall e, In e openat_errnos -> LRZ (nret ms (efferr e)) mo g KA) ->
    LRZ (nret ms (eff0 (alloc_fd fds))) (mk (alloc_fd fds) mo) g KB ->
    LRZ ms mo g (t_alt2 KA KB).
  Proof.
    intros mk KA KB Hiff Hmk Hmkh HmkI HA HB. destruct lopen_at_facts as (Hsvc & _).
    apply (lrz_node_alt2 segs ms mo g x8 {e : Z | In e openat_errnos} unit
             (exist _ ENOMEM ENOMEM_in_openat_errnos) tt KA KB Hsvc eq_refl).
    intros mr mat HI.
    set (rd := open_reads (rin mr) (areg ms 11)).
    pose (effs := fun i : {e : Z | In e openat_errnos} + unit =>
                    match i with inl (exist _ e _) => with_copyins rd (efferr e) | inr _ => with_copyins rd (eff0 (alloc_fd fds)) end).
    pose (mos := fun i : {e : Z | In e openat_errnos} + unit => match i with inl _ => mo | inr _ => mk (alloc_fd fds) mo end).
    assert (ACC : forall i a n, In (a, n) (syscall_effect_accesses (effs i)) -> forall k, (k < n)%nat -> vis segs (ms_mem ms) (boff a k)).
    { intros i a n Hin. assert (Hin' : In (a, n) rd).
      { destruct i as [[e He]|[]]; cbv beta iota delta [effs syscall_effect_accesses with_copyins eff_copyins eff_writes eff_ret eff_zeros eff_unmaps eff_copies write_accesses efferr eff0] in Hin;
          rewrite app_nil_r in Hin; exact Hin. }
      exact (lopen_reads_vis mr mat HI a n Hin'). }
    assert (HIi : forall i, LINV segs g (mos i) mat (ms_mem ms) mr).
    { intros [[e He]|[]]; cbn [mos]; [exact HI| apply HmkI; exact HI]. }
    exists effs, mos, (fun _ => g), (fun _ => ms_mem ms),
      (fun i => newly_materialized_pages (m_vm_lazy (mos i)) mat (syscall_effect_accesses (effs i)) ++ mat).
    split.
    - intros o. fold (rin mr). rewrite (Hiff mr mat HI o). unfold open_out. fold rd.
      rewrite m_fds_real. fold fds. split.
      + intros [(e & He & ->)|(_ & ->)]; [exists (inl (exist _ e He)); reflexivity| exists (inr tt)].
        cbn [effs mos]. rewrite Hmk. reflexivity.
      + intros [[[e He]|[]] ->]; cbn [effs mos]; [left; exists e; split; [exact He| reflexivity]| right].
        split; [exact Hfree|]. rewrite Hmk. reflexivity.
    - intros i. destruct (lmaterialize segs g (mos i) mat (ms_mem ms) mr (syscall_effect_accesses (effs i)) (HIi i) (ACC i)) as [Hmat HI2].
      split; [destruct i as [[e He]|[]]; cbn [mos]; [| rewrite Hmkh]; exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI))|].
      split; [exact Hmat|].
      assert (Er : exists r, effs i = with_copyins rd (mkEffect r [] [])).
      { destruct i as [[e He]|[]]; cbn [effs]; eexists; reflexivity. }
      destruct Er as [r Er]. rewrite Er in HI2. rewrite Er, nret_copyins'. unfold eff0. split.
      + rewrite mem_nret_plain. cbn [ms_mem msw]. exact HI2.
      + rewrite nret_copyins'. unfold eff0. rewrite msw_nret_plain.
        destruct i as [[e He]|[]]; cbn [effs] in Er; cbn [mos].
        * apply (f_equal eff_ret) in Er. cbn [eff_ret with_copyins efferr eff0 errno_ret] in Er.
          change (eff_ret (efferr e) = r) in Er. rewrite <- Er. apply HA. exact He.
        * (* [comment removed for export] *)
          apply (f_equal eff_ret) in Er.
          assert (RW : forall R e0, eff_ret (with_copyins R e0) = eff_ret e0) by reflexivity. rewrite !RW in Er. clear RW.
          change (eff_ret (eff0 (alloc_fd fds)) = r) in Er. rewrite <- Er. exact HB.
  Qed.

  Lemma lrz_at_openat_dot : forall KA KB, path = dot_path ->
    (forall e, In e openat_errnos -> LRZ (nret ms (efferr e)) mo g KA) ->
    LRZ (nret ms (eff0 (alloc_fd fds))) (with_fds (fd_insert fds (alloc_fd fds) FdDir) mo) g KB ->
    LRZ ms mo g (t_alt2 KA KB).
  Proof.
    intros KA KB Hp HA HB. destruct lopen_at_facts as (_ & _ & Hfl & _).
    apply (lrz_at_openat_open (fun fd mo1 => with_fds (fd_insert (m_fds mo1) fd FdDir) mo1));
      [| reflexivity| reflexivity| intros; apply LINV_with_fds; assumption| exact HA| exact HB].
    intros mr mat HI o. rewrite lopenat_head_at. apply (openat_dot_outcome _ _ _ _ (real mo mat) lopen_flags_modeled_at eq_refl Hfl).
    rewrite <- Hp. apply (lpath_cstr_at mr mat HI). rewrite Hp. cbn. lia.
  Qed.

  Lemma lrz_at_openat_file : forall d KA KB, (length path <= 4095)%nat -> path <> [] -> path <> dot_path -> path <> dotdot_path -> path_has_slash path = false ->
    fs_lookup (m_fs mo) path = Some d ->
    (forall e, In e openat_errnos -> LRZ (nret ms (efferr e)) mo g KA) ->
    LRZ (nret ms (eff0 (alloc_fd fds))) (with_fds (fd_insert fds (alloc_fd fds) (FdFile path (Z_to_bv 64 0))) mo) g KB ->
    LRZ ms mo g (t_alt2 KA KB).
  Proof.
    intros d KA KB Hlen Hne Hnd Hndd Hsl Hfs HA HB. destruct lopen_at_facts as (_ & _ & Hfl & _).
    apply (lrz_at_openat_open (fun fd mo1 => with_fds (fd_insert (m_fds mo1) fd (FdFile path (Z_to_bv 64 0))) mo1));
      [| reflexivity| reflexivity| intros; apply LINV_with_fds; assumption| exact HA| exact HB].
    intros mr mat HI o. rewrite lopenat_head_at.
    apply (openat_file_outcome _ _ _ _ (real mo mat) lopen_flags_modeled_at eq_refl Hfl path d);
      [exact (lpath_cstr_at mr mat HI Hlen) | exact Hne | exact Hnd | exact Hndd | exact Hsl | rewrite m_fs_real; exact Hfs].
  Qed.
End Openat.

(* [comment removed for export] *)
Lemma lrz_impl_openat_err : forall (Q : sret -> machine_state -> Prop) ms mo g path (e : Z) K,
  impl segs (at_node segs) (enode (NOpen path) dec_open) (epost Q) ms ->
  1 <= e <= 4095 ->
  (forall ms1 K', at_node segs (NOpen path) ms1 -> LRZ (nret ms1 (efferr e)) mo g K' -> LRZ ms1 mo g K') ->
  (forall ms2, Q (SErr e) ms2 -> LRZ ms2 mo g K) ->
  LRZ ms mo g K.
Proof.
  intros Q ms mo g path e K Himpl He Hnode HK.
  apply (lrz_impl_enode (NOpen path) dec_open Q ms mo g K Himpl).
  intros ms1 Hat Hcont. apply (Hnode ms1 K Hat).
  apply (Hcont _ (SErr e) _ g K); [| exact HK].
  unfold dec_open. apply dec_plain_err. exact He.
Qed.

Lemma lrz_impl_openat_absent : forall (Q : sret -> machine_state -> Prop) ms mo g path K,
  impl segs (at_node segs) (enode (NOpen path) dec_open) (epost Q) ms ->
  (length path <= 4095)%nat -> path <> [] -> path <> dot_path -> path <> dotdot_path -> path_has_slash path = false -> fs_lookup (m_fs mo) path = None ->
  (forall ms2, Q (SErr ENOENT) ms2 -> LRZ ms2 mo g K) ->
  LRZ ms mo g K.
Proof.
  intros Q ms mo g path K Himpl Hlen Hne Hnd Hndd Hsl Hfs HK.
  apply (lrz_impl_openat_err Q ms mo g path ENOENT K Himpl ltac:(unfold ENOENT; lia)); [|exact HK].
  intros ms1 K' Hat HK'. apply (lrz_at_openat_absent ms1 mo g path Hat K' Hlen Hne Hnd Hndd Hsl Hfs HK').
Qed.

Lemma lrz_impl_openat_empty : forall (Q : sret -> machine_state -> Prop) ms mo g K,
  impl segs (at_node segs) (enode (NOpen []) dec_open) (epost Q) ms ->
  (forall ms2, Q (SErr ENOENT) ms2 -> LRZ ms2 mo g K) ->
  LRZ ms mo g K.
Proof.
  intros Q ms mo g K Himpl HK.
  apply (lrz_impl_openat_err Q ms mo g [] ENOENT K Himpl ltac:(unfold ENOENT; lia)); [|exact HK].
  intros ms1 K' Hat HK'. apply (lrz_at_openat_empty ms1 mo g [] Hat K' eq_refl HK').
Qed.

Lemma lrz_impl_openat_toolong : forall (Q : sret -> machine_state -> Prop) ms mo g path K,
  impl segs (at_node segs) (enode (NOpen path) dec_open) (epost Q) ms ->
  (4096 <= length path)%nat ->
  (forall ms2, Q (SErr ENAMETOOLONG) ms2 -> LRZ ms2 mo g K) ->
  LRZ ms mo g K.
Proof.
  intros Q ms mo g path K Himpl Hlen HK.
  apply (lrz_impl_openat_err Q ms mo g path ENAMETOOLONG K Himpl ltac:(unfold ENAMETOOLONG; lia)); [|exact HK].
  intros ms1 K' Hat HK'. apply (lrz_at_openat_toolong ms1 mo g path Hat K' Hlen HK').
Qed.

Lemma lrz_impl_openat_file : forall (Q : sret -> machine_state -> Prop) ms mo g path d KA KB,
  impl segs (at_node segs) (enode (NOpen path) dec_open) (epost Q) ms ->
  (length path <= 4095)%nat -> path <> [] -> path <> dot_path -> path <> dotdot_path -> path_has_slash path = false -> fs_lookup (m_fs mo) path = Some d ->
  fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
  3 <= bv_unsigned (alloc_fd (m_fds mo)) <= 4096 ->
  (forall e ms2, In e openat_errnos -> Q (SErr e) ms2 -> LRZ ms2 mo g KA) ->
  (forall ms2, Q (SVal (bv_unsigned (alloc_fd (m_fds mo)))) ms2 ->
     LRZ ms2 (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) (FdFile path (Z_to_bv 64 0))) mo) g KB) ->
  LRZ ms mo g (t_alt2 KA KB).
Proof.
  intros Q ms mo g path d KA KB Himpl Hlen Hne Hnd Hndd Hsl Hfs Hfree Hfd HA HB.
  apply (lrz_impl_enode (NOpen path) dec_open Q ms mo g (t_alt2 KA KB) Himpl).
  intros ms1 Hat Hcont.
  apply (lrz_at_openat_file ms1 mo g path Hat Hfree d KA KB Hlen Hne Hnd Hndd Hsl Hfs).
  - intros e He. pose proof (openat_errnos_range e He) as Her.
    apply (Hcont _ (SErr e) _ g KA); [unfold dec_open; apply dec_plain_err; exact Her |].
    intros ms2 HQ. exact (HA e ms2 He HQ).
  - rewrite <- (Z_to_bv_bv_unsigned (alloc_fd (m_fds mo))) at 1.
    apply (Hcont _ (SVal (bv_unsigned (alloc_fd (m_fds mo)))) _ g KB); [| exact HB].
    unfold dec_open. apply dec_plain_val; [|rewrite (proj2 (Z.leb_le 3 _)), (proj2 (Z.leb_le _ 4096)) by lia; reflexivity].
    pose proof (bv_unsigned_in_range 64 (alloc_fd (m_fds mo))). lia.
Qed.

Lemma lrz_impl_openat_dot : forall (Q : sret -> machine_state -> Prop) ms mo g KA KB,
  impl segs (at_node segs) (enode (NOpen dot_path) dec_open) (epost Q) ms ->
  fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
  3 <= bv_unsigned (alloc_fd (m_fds mo)) <= 4096 ->
  (forall e ms2, In e openat_errnos -> Q (SErr e) ms2 -> LRZ ms2 mo g KA) ->
  (forall ms2, Q (SVal (bv_unsigned (alloc_fd (m_fds mo)))) ms2 ->
     LRZ ms2 (with_fds (fd_insert (m_fds mo) (alloc_fd (m_fds mo)) FdDir) mo) g KB) ->
  LRZ ms mo g (t_alt2 KA KB).
Proof.
  intros Q ms mo g KA KB Himpl Hfree Hfd HA HB.
  apply (lrz_impl_enode (NOpen dot_path) dec_open Q ms mo g (t_alt2 KA KB) Himpl).
  intros ms1 Hat Hcont.
  apply (lrz_at_openat_dot ms1 mo g dot_path Hat Hfree KA KB eq_refl).
  - intros e He. pose proof (openat_errnos_range e He) as Her.
    apply (Hcont _ (SErr e) _ g KA); [unfold dec_open; apply dec_plain_err; exact Her |].
    intros ms2 HQ. exact (HA e ms2 He HQ).
  - rewrite <- (Z_to_bv_bv_unsigned (alloc_fd (m_fds mo))) at 1.
    apply (Hcont _ (SVal (bv_unsigned (alloc_fd (m_fds mo)))) _ g KB); [| exact HB].
    unfold dec_open. apply dec_plain_val; [|rewrite (proj2 (Z.leb_le 3 _)), (proj2 (Z.leb_le _ 4096)) by lia; reflexivity].
    pose proof (bv_unsigned_in_range 64 (alloc_fd (m_fds mo))). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lat_node_writev_facts : forall ms (fd : Z) bufs,
  at_node segs (NWritev fd bufs) ms ->
  ms_svc_pending ms = Some (Z_to_bv 64 66) /\ (fd = 1 \/ fd = 2) /\ areg ms 10 = Z_to_bv 64 fd
  /\ areg ms 12 = Z_to_bv 64 (Z.of_nat (length bufs)) /\ (length bufs <= 1024)%nat /\ Z.of_nat (length (concat bufs)) < 2^63
  /\ ms_rom ms = seg_rom segs
  /\ exists iovs, bv_unsigned (areg ms 11) + 16 * Z.of_nat (length bufs) <= TASK_SIZE   (* [comment removed for export] *)
                  /\ Forall (fun iv => bv_unsigned (fst iv) + bv_unsigned (snd iv) <= TASK_SIZE) iovs
                  /\ bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs)
                  /\ Forall2 (iov_ok (mrd segs (ms_mem ms))) iovs bufs.
Proof.
  intros ms fd bufs Hat. cbn [at_node] in Hat.
  destruct Hat as (Hsvc & Hfd & H10 & H12 & Hcnt & Hlen & Hrom & iovs & Htask & Hbtask & Harr & Hbufs).
  repeat (split; [assumption|]). exists iovs. split; [exact Htask|]. split; [exact Hbtask|]. split; [exact Harr|].
  clear Harr H12 Hcnt Htask Hbtask. revert Hlen. induction Hbufs as [| iov bs iovs' bss' [Hl Hb] _ IH]; intros Hlen; [constructor|].
  cbn [concat] in Hlen. rewrite length_app in Hlen.
  constructor; [| apply IH; lia]. split; [exact Hl|]. split; [lia|]. exact Hb.
Qed.

Lemma lrz_at_writev_wall : forall ms mo g (fd : Z) bufs K,
  at_node segs (NWritev fd bufs) ms ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (1 <= length bufs)%nat ->
  let bs := concat bufs in
  1 <= Z.of_nat (length bs) <= 67108864 ->   (* [comment removed for export] *)
  K [] ->
  (forall k, (1 <= k <= length bs)%nat ->
     LRZ (nret ms (eff0 (Z_to_bv 64 (Z.of_nat k)))) mo g (t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn k bs)) K)) ->
  LRZ ms mo g (t_emit (map (WriteEv (Z_to_bv 64 fd)) bs) K).
Proof.
  intros ms mo g fd bufs K Hat Hlk Hlen bs [Hb1 Hbmax] HK0 HK.
  destruct (lat_node_writev_facts _ _ _ Hat) as (Hsvc & Hfd & H10 & H12 & Hcnt & Hlen63 & Hrom & iovs & Htask & Hbtask & Harr & Hbufs).
  assert (Hnb : (1 <= length bs)%nat) by lia.
  pose proof (Forall2_length Hbufs) as Hleneq.
  eapply lrz_conseq; [| apply t_alt_wall; [exact HK0| exact Hnb]].
  apply (lrz_node segs ms mo g (Z_to_bv 64 66) (wr_index bs) (wr_full bs Hnb)
           (fun i => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) bs))
           (fun i => t_emit (map (WriteEv (Z_to_bv 64 fd)) (skipn (proj1_sig i) bs)) K) Hsvc eq_refl).
  intros mr mat HI.
  pose proof (bytes_in_real _ _ _ _ _ _ _ _ HI Harr) as Harr'.
  pose proof (Forall2_iov_ok_real _ _ _ _ _ _ _ _ HI Hbufs) as Hbufs'.
  pose proof (writev_outcome_i (sys_input segs (msw ms mr) (Z_to_bv 64 66)) (real mo mat) fd (areg ms 11) iovs bufs
                ltac:(rewrite in_sysno_pending; apply u64_lit; lia)
                ltac:(rewrite in_a0_si, areg_msw; exact H10)
                ltac:(lia)
                ltac:(rewrite m_fds_real; exact Hlk)
                ltac:(rewrite in_a1_si, areg_msw; reflexivity)
                ltac:(rewrite in_a2_si, areg_msw, Hleneq; exact H12)
                ltac:(lia)
                ltac:(rewrite (in_mem_msw ms mr _ Hrom); exact Harr')
                ltac:(rewrite (in_mem_msw ms mr _ Hrom); exact Hbufs')
                ltac:(rewrite <- Hleneq in Htask; exact Htask) Hbtask
                ltac:(fold bs; lia) ltac:(fold bs; lia)) as Hiff.
  cbv zeta in Hiff. fold bs in Hiff.
  set (CA := copy_iovecs_accesses _ _ _) in Hiff.
  pose (effs := fun i : wr_index bs =>
          mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [] [] [] (CA ++ iov_prefix_accesses iovs (proj1_sig i))).
  assert (ACC : forall i x n, In (x, n) (syscall_effect_accesses (effs i)) -> forall kk, (kk < n)%nat -> vis segs (ms_mem ms) (boff x kk)).
  { intros [k Hk] x n Hin. cbv beta iota delta [effs proj1_sig syscall_effect_accesses eff_copyins eff_writes write_accesses] in Hin.
    rewrite app_nil_r in Hin. unfold CA in Hin.
    exact (writev_accesses_vis segs (ms_mem ms) (areg ms 11) iovs bufs _ k x n Harr Hbufs Hin). }
  exists effs, (fun _ => mo), (fun _ => g), (fun _ => ms_mem ms),
    (fun i => newly_materialized_pages (m_vm_lazy mo) mat (syscall_effect_accesses (effs i)) ++ mat).
  split.
  - intros o. rewrite Hiff. split.
    + intros (k & Hk & ->). exists (exist _ k Hk). reflexivity.
    + intros [[k Hk] ->]. exists k. split; [exact Hk| reflexivity].
  - intros i. destruct (lmaterialize segs g mo mat (ms_mem ms) mr (syscall_effect_accesses (effs i)) HI (ACC i)) as [Hmat HI2].
    split; [exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI))|]. split; [exact Hmat|].
    assert (Em : forall ms0, nret ms0 (effs i) = nret ms0 (mkEffect (Z_to_bv 64 (Z.of_nat (proj1_sig i))) [] [])) by (intros ms0; reflexivity).
    rewrite !Em. split.
    + rewrite mem_nret_plain. cbn [ms_mem msw]. exact HI2.
    + rewrite msw_nret_plain. destruct i as [k Hk]. apply HK. exact Hk.
Qed.

(* [comment removed for export] *)
Lemma lrz_at_writev_zero : forall ms mo g (fd : Z) bufs K,
  at_node segs (NWritev fd bufs) ms ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (1 <= length bufs)%nat ->
  concat bufs = [] ->
  LRZ (nret ms (eff0 (Z_to_bv 64 0))) mo g K ->
  LRZ ms mo g K.
Proof.
  intros ms mo g fd bufs K Hat Hlk Hlen Hnil HK.
  destruct (lat_node_writev_facts _ _ _ Hat) as (Hsvc & Hfd & H10 & H12 & Hcnt & Hlen63 & Hrom & iovs & Htask & Hbtask & Harr & Hbufs).
  pose proof (Forall2_length Hbufs) as Hleneq. rewrite <- Hleneq in H12, Hlen, Hcnt, Htask.
  pose proof (iovs_total_ok _ _ _ Hbufs) as Htot. rewrite Hnil in Htot. cbn in Htot.
  assert (Hwn : word_to_nat (Z_to_bv 64 (Z.of_nat (length iovs))) = length iovs).
  { unfold word_to_nat. rewrite u64_lit by lia. apply Nat2Z.id. }
  apply (lrz_node_silent segs ms mo g (Z_to_bv 64 66) unit tt K Hsvc eq_refl).
  intros mr mat HI.
  pose proof (bytes_in_real _ _ _ _ _ _ _ _ HI Harr) as Harr'.
  pose proof (Forall2_iov_ok_real _ _ _ _ _ _ _ _ HI Hbufs) as Hbufs'.
  set (rin := sys_input segs (msw ms mr) (Z_to_bv 64 66)).
  set (eff := with_copyins (copy_iovecs_accesses (in_mem rin) (areg ms 11) (length iovs)) (mkEffect (Z_to_bv 64 0) [] [])).
  assert (ACC : forall x n, In (x, n) (syscall_effect_accesses eff) -> forall kk, (kk < n)%nat -> vis segs (ms_mem ms) (boff x kk)).
  { intros x n Hin. unfold eff in Hin.
    cbv beta iota delta [syscall_effect_accesses with_copyins eff_copyins eff_writes eff_ret eff_zeros eff_unmaps eff_copies write_accesses] in Hin.
    apply (writev_accesses_vis segs (ms_mem ms) (areg ms 11) iovs bufs (in_mem rin) 0%nat x n Harr Hbufs).
    apply in_app_or in Hin as [Hin|[]]. apply in_or_app. left. exact Hin. }
  destruct (lmaterialize segs g mo mat (ms_mem ms) mr (syscall_effect_accesses eff) HI ACC) as [Hmat HI2].
  exists (fun _ => eff), (fun _ => mo), (fun _ => g), (fun _ => ms_mem ms),
    (fun _ => newly_materialized_pages (m_vm_lazy mo) mat (syscall_effect_accesses eff) ++ mat).
  split.
  - intros o. fold rin. rewrite (syscall_spec_66 _ _ o) by (unfold rin; rewrite in_sysno_pending; apply u64_lit; lia).
    unfold rin at 1 2 3. rewrite in_a0_si, in_a1_si, in_a2_si, !areg_msw, H10, H12, fd32_id by (rewrite u64_lit; lia).
    rewrite (writev_chan_zero_outcome _ _ _ _ (real mo mat) o (Z_to_bv 64 fd) iovs).
    + unfold eff. rewrite Hwn. split; [intros ->; exists tt; reflexivity| intros [[] ->]; reflexivity].
    + rewrite m_fds_real. exact Hlk.
    + apply w_is0_pos. rewrite u64_lit; lia.
    + unfold iovcnt32, abi_low32. rewrite u64_lit by lia. rewrite Z.mod_small by lia. reflexivity.
    + apply w_is0_pos. rewrite u64_lit; lia.
    + unfold IOV_MAX. rewrite u64_lit; lia.
    + rewrite Hwn. unfold rin. rewrite (in_mem_msw ms mr _ Hrom). rewrite <- (wa_unsigned_id (areg ms 11)).
      apply copy_iovecs_aux_bytes_in; [exact Harr'|].
      eapply Forall_impl; [|exact (Forall2_iov_ok_lens _ _ _ Hbufs)]. intros [b l] Hb. cbn [snd] in *. rewrite Hnil in Hb. cbn in Hb. lia.
    + apply access_okb_intro_Z; rewrite u64_lit by lia; lia.
    + unfold iovs_access_okb. apply forallb_forall. intros [b l] Hin.
      rewrite Forall_forall in Hbtask. specialize (Hbtask _ Hin). cbn [fst snd] in *.
      apply access_okb_intro. exact Hbtask.
    + exact Htot.
    + vm_compute. discriminate.
  - intros []. split; [exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ _ HI))|]. split; [exact Hmat|]. split.
    + unfold eff. rewrite nret_copyins'. unfold eff0. rewrite mem_nret_plain. cbn [ms_mem msw]. exact HI2.
    + unfold eff. rewrite nret_copyins'. unfold eff0. rewrite msw_nret_plain. exact HK.
Qed.

End WithSegs.
End LRzAt.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Syscall.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import RelSpec ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil PropExec MState Mem Exec ITree Nodes Decode SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NodesSound.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require RzNodesImpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.RzNodesImpl.RzNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import RzNodesImpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SO_model SO_rz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LMeasure LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LRz.
Import LRzAt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.
Context {ACEIL : Ceil}.   (* [comment removed for export] *)
Local Abbreviation impl := (ITree.impl segs (at_node segs)).
Local Abbreviation LRZ := (LRz.LRZ segs).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition lrzt {A} (t : itree node (exc A)) (mo : Model) (g : lghost) (out : list event) (R : A -> Prop) : Prop :=
  forall (Q : A -> machine_state -> Prop) (ms : machine_state) (K : TSet),
    impl t (epost Q) ms ->
    K [] ->
    (forall a ms', Q a ms' -> R a -> LRZ ms' mo g K) ->
    LRZ ms mo g (t_emit out K).

Lemma lrz_emit_nil : forall ms mo g K, LRZ ms mo g K -> LRZ ms mo g (t_emit [] K).
Proof.
  intros ms mo g K H mr mat HI. pose proof (H mr mat HI) as Hs.
  eapply srz_conseq; [exact Hs|]. apply t_eq_sym. apply t_emit_nil_eq. exact (srealizes_nonempty _ _ _ Hs).
Qed.

Lemma lrzt_ret : forall {A} (a : A) mo g (R : A -> Prop), R a -> lrzt (ITree.Ret (Ok a)) mo g [] R.
Proof.
  intros A a mo g R Ha Q ms K Hi HK Hc. cbn in Hi. apply lrz_emit_nil.
  eapply lrz_evt; [exact Hi|]. intros ms' HQ. apply (Hc a ms'); [exact HQ| exact Ha].
Qed.

Lemma lrzt_mono : forall {A} (t : itree node (exc A)) mo g out (R R' : A -> Prop),
  lrzt t mo g out R -> (forall a, R a -> R' a) -> lrzt t mo g out R'.
Proof. intros A t mo g out R R' H HR Q ms K Hi HK Hc. apply (H Q ms K Hi HK). intros a ms' HQ Ha. apply (Hc a ms'); auto. Qed.

Lemma lrzt_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo g o1 o2 (R1 : A -> Prop) (R2 : B -> Prop),
  lrzt t mo g o1 R1 -> (forall a, R1 a -> lrzt (f a) mo g o2 R2) -> lrzt (ebind t f) mo g (o1 ++ o2) R2.
Proof.
  intros A B t f mo g o1 o2 R1 R2 Ht Hf Q ms K Hi HK Hc.
  eapply lrz_conseq; [| apply t_eq_sym; apply t_emit_app].
  unfold ebind in Hi. apply (impl_bind_inv segs) in Hi.
  apply (Ht (fun a ms' => impl (f a) (epost Q) ms') ms (t_emit o2 K)).
  - eapply impl_mono; [exact Hi|]. intros [|a] ms'; cbn; [intros _; exact I| intros H; exact H].
  - apply t_emit_has_nil.
  - intros a ms' Hfa Ha. apply (Hf a Ha Q ms' K Hfa HK Hc).
Qed.

(* [comment removed for export] *)
Lemma lrzt_mbind : forall {St A B} (m : M St A) (f : A -> M St B) (s : St) mo g o1 o2 (R1 : A * St -> Prop) (R2 : B * St -> Prop),
  lrzt (m s) mo g o1 R1 -> (forall a s', R1 (a, s') -> lrzt (f a s') mo g o2 R2) -> lrzt (mbind m f s) mo g (o1 ++ o2) R2.
Proof.
  intros St A B m f s mo g o1 o2 R1 R2 Hm Hf. unfold mbind. eapply lrzt_ebind; [exact Hm|]. intros [a s'] H. apply Hf. exact H.
Qed.

Lemma lrzt_mbind_nil_l : forall {St A B} (m : M St A) (f : A -> M St B) (s : St) mo g o (R1 : A * St -> Prop) (R2 : B * St -> Prop),
  lrzt (m s) mo g [] R1 -> (forall a s', R1 (a, s') -> lrzt (f a s') mo g o R2) -> lrzt (mbind m f s) mo g o R2.
Proof. intros. change o with ([] ++ o). eapply lrzt_mbind; eauto. Qed.

Lemma lrzt_mbind_nil_r : forall {St A B} (m : M St A) (f : A -> M St B) (s : St) mo g o (R1 : A * St -> Prop) (R2 : B * St -> Prop),
  lrzt (m s) mo g o R1 -> (forall a s', R1 (a, s') -> lrzt (f a s') mo g [] R2) -> lrzt (mbind m f s) mo g o R2.
Proof. intros. rewrite <- (app_nil_r o). eapply lrzt_mbind; eauto. Qed.

Lemma lrzt_mret : forall {St A} (a : A) (s : St) mo g (R : A * St -> Prop), R (a, s) -> lrzt (mret a s) mo g [] R.
Proof. intros. unfold mret. apply lrzt_ret. exact H. Qed.

Lemma lrzt_mupd : forall {St} (f : St -> St) (s : St) mo g (R : unit * St -> Prop), R (tt, f s) -> lrzt (mupd f s) mo g [] R.
Proof. intros. unfold mupd. apply lrzt_ret. exact H. Qed.

Lemma lrzt_mget : forall {St} (s : St) mo g (R : St * St -> Prop), R (s, s) -> lrzt (mget s) mo g [] R.
Proof. intros. unfold mget. apply lrzt_ret. exact H. Qed.

(* [comment removed for export] *)
Lemma lrzt_unr_false : forall {A} mo g out (R : A -> Prop), False -> lrzt (ITree.Ret Unr) mo g out R.
Proof. intros A mo g out R []. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lrzt_ioctl : forall {St} (st : St) mo g (fd : Z) e (R : sret * St -> Prop),
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some e ->
  e <> FdUrandom ->     (* [comment removed for export] *)
  (forall err, R (SErr err, st)) ->
  lrzt (msys (NIoctl fd TIOCGWINSZ) dec_ioctl st) mo g [] R.
Proof.
  intros St st mo g fd e R Hlk Hnd HR Q ms K Hi HK Hc. unfold msys, enode in Hi. cbn [ITree.impl] in Hi.
  apply lrz_emit_nil. eapply lrz_evt; [exact Hi|]. intros ms1 [Hat Hk].
  eapply lrz_at_ioctl; [exact Hat| exact Hlk| exact Hnd|].
  specialize (Hk (efferr ENOTTY)). unfold dec_ioctl in Hk. rewrite dec_plain_err in Hk by (unfold ENOTTY; lia).
  cbn [ITree.impl epost] in Hk.
  eapply lrz_evt; [exact Hk|]. intros ms2 HQ. apply (Hc _ _ HQ). apply HR.
Qed.

(* [comment removed for export] *)
Lemma lrzt_wv_loop : forall {St} (st : St) mo g (fd : Z) (fuel : nat) (iov : list (list Z)),
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (length iov = 1%nat \/ length iov = 2%nat) ->
  wv_total iov < Z.of_nat fuel -> wv_total iov <= 67108864 ->   (* [comment removed for export] *)
  lrzt (mloop fuel (wv_body fd) iov st) mo g (map (WriteEv (Z_to_bv 64 fd)) (to_bytes (concat iov))) (fun p => snd p = st).
Proof.
  intros St st mo g fd fuel. induction fuel as [|fuel IH]; intros iov Hlk Hsh Hfuel Hmax.
  { pose proof (wv_total_nonneg iov). lia. }
  intros Q ms K Hi HK Hc.
  cbn [mloop] in Hi. cbn -[mloop dec_wv wv_total wv_advance to_bytes] in Hi.
  eapply lrz_evt; [exact Hi|]. intros ms1 [Hat Hk].
  assert (Hlen : (1 <= length (map to_bytes iov))%nat) by (rewrite length_map; lia).
  pose proof (wv_total_nonneg iov) as T0.
  assert (TOT : Z.of_nat (length (concat (map to_bytes iov))) = wv_total iov).
  { rewrite to_bytes_concat, to_bytes_length'. reflexivity. }
  destruct (Z.eq_dec (wv_total iov) 0) as [Z0|NZ].
  - (* [comment removed for export] *)
    eapply lrz_at_writev_zero; [exact Hat| exact Hlk| exact Hlen| |].
    { apply length_zero_iff_nil. lia. }
    specialize (Hk (eff0 (Z_to_bv 64 0))). rewrite (dec_wv_val (wv_total iov) 0) in Hk by lia.
    rewrite Z0 in Hk. cbn -[mloop dec_wv wv_total wv_advance to_bytes] in Hk.
    replace (concat iov) with (@nil Z).
    2:{ symmetry. apply length_zero_iff_nil. unfold wv_total, zlength in Z0. lia. }
    cbn [to_bytes map]. apply lrz_emit_nil.
    eapply lrz_evt; [exact Hk|]. intros ms2 HQ. apply (Hc _ _ HQ). reflexivity.
  - rewrite <- to_bytes_concat.
    eapply lrz_at_writev_wall; [exact Hat| exact Hlk| exact Hlen| lia| exact HK|].
    intros k Hk1. assert (K1 : 1 <= Z.of_nat k <= wv_total iov) by lia.
    specialize (Hk (eff0 (Z_to_bv 64 (Z.of_nat k)))). rewrite (dec_wv_val (wv_total iov) (Z.of_nat k)) in Hk by lia.
    cbn -[mloop dec_wv wv_total wv_advance to_bytes] in Hk.
    destruct (Z.eq_dec (Z.of_nat k) (wv_total iov)) as [E|NE];
      [rewrite (proj2 (Z.eqb_eq _ _) E) in Hk | rewrite (proj2 (Z.eqb_neq _ _) NE) in Hk];
      cbn -[mloop dec_wv wv_total wv_advance to_bytes] in Hk.
    + (* [comment removed for export] *)
      replace (skipn k (concat (map to_bytes iov))) with (@nil byte).
      2:{ symmetry. apply skipn_all2. lia. }
      cbn [map]. apply lrz_emit_nil.
      eapply lrz_evt; [exact Hk|]. intros ms2 HQ. apply (Hc _ _ HQ). reflexivity.
    + (* [comment removed for export] *)
      rewrite to_bytes_concat, <- to_bytes_skipn.
      replace (skipn k (concat iov)) with (concat (wv_advance iov (Z.of_nat k))).
      2:{ rewrite wv_advance_concat by lia. f_equal. lia. }
      apply (IH (wv_advance iov (Z.of_nat k)) Hlk (wv_advance_shape _ _ Hsh)
               ltac:(rewrite wv_advance_total by lia; lia) ltac:(rewrite wv_advance_total by lia; lia) Q _ K Hk HK Hc).
Qed.

(* [comment removed for export] *)
Lemma lrzt_stdio_writev : forall {St} (st : St) mo g (fd : Z) (buf s : list Z),
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  zlength buf + zlength s <= 67108864 ->   (* [comment removed for export] *)
  lrzt (stdio_writev fd buf s st) mo g (map (WriteEv (Z_to_bv 64 fd)) (to_bytes (buf ++ s))) (fun p => snd p = st).
Proof.
  intros St st mo g fd buf s Hlk Hmax. unfold stdio_writev.
  replace (buf ++ s) with (concat (wv_init buf s)) by (unfold wv_init; destruct buf; cbn; rewrite ?app_nil_r; reflexivity).
  apply lrzt_wv_loop; [exact Hlk| apply wv_init_shape| rewrite wv_total_init; unfold zlength; lia| rewrite wv_total_init; exact Hmax].
Qed.
End WithSegs.
