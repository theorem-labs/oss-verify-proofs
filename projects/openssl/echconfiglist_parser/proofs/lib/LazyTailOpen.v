(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (RomBase.sys_rob robustness premises on the fd, openat, ioctl and writev nodes; the channel-reader premise on writev; C-string path reads bounded below TASK_SIZE; copy_iovecs_accesses now lists each iovec entry's own access). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/echconfiglist_parser/lib/LazyFdNodes.v; 233 of its 373 lines of code are new or changed and 1001 lines of the source are left out; taken from projects/openssl/echconfiglist_parser/proofs/lib/LazyFdNodes.v, lines 7-25, 480-492, 521-630 and 639-782, as in the LPS 727298f3 update. *)
(* Theorem Labs, 2026-11 (LPS 727298f3): the openat nodes of LazyFdNodes.v (Section OpenatLazy,
   lines 479-783) for a walk over the binary's segments followed by a tail that is neither
   executable nor writable (the launch's vDSO/vvar pair).  The lazy view, the fetch and the path
   facts stay over the binary's segments; the restricted states carry the larger list's read-only
   backing, through which the system call reads the path; a step invariant is carried to every
   continuation. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  Scfg SimInv ExitSim PropExec CatExec CatSim MmapSim AllocSim FileSim RelSpec
  ShapeAlg Nodes AgentLib AgentNodes Gap04 RefNodes RefNodesDir Hoare LibWritev SReach
  LazyRestrict LazyRestrictRun LazyRestrictAlg LazyLedger LazySR LazyNodes LazyFdNodes.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require RomBase RomWrite RomStable.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import LazyTail.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section OpenatLazyTail.
  Variables segs tail : list Segment.
  Hypothesis Hnx : forall s, In s tail -> seg_executable s = false.
  Hypothesis Hnw : forall s, In s tail -> seg_writable s = false.
  Context {SC : StepCfg}.
  Variable I : config -> Prop.
  Hypothesis HI : forall c evs c', I c -> sstep_cfg (segs ++ tail) the_scfg c evs (SNext c') -> I c'.
  Variables (L S Zr : list (word * word)) (msF : machine_state) (regs : bvmap 5 word) (pc : word)
            (mem : word -> option byte) (mo : Model).
  Variable w : bv 32.
  Hypothesis HF : fetch_word segs pc = Some w.
  Hypothesis HE : is_ecall w = true.
  Hypothesis Hok : lzok segs L S Zr (mkCfg msF mo).
  Hypothesis HIc : I (mkCfg msF mo).
  Hypothesis Hr : restrict L S msF = mkst regs pc mem (seg_rom (segs ++ tail)).
  Hypothesis H17 : getr regs 17 = Z_to_bv 64 56.
  Hypothesis H10 : getr regs 10 = AT_FDCWD.
  Hypothesis Hfl : Z.ldiff (bv_unsigned (getr regs 12)) open_ignored_flags = 0%Z.

  Let post (r : word) := mkst (regupd regs 10 r) (v_addi pc 4) mem (seg_rom (segs ++ tail)).
  Let fds := m_fds mo.

  (* The system call's input is the same over both lists: the tail adds no writable byte
     (Common/Cfg/RomStable.v:433). *)
  Lemma ltO_sys_input : forall ms x8, sys_input (segs ++ tail) ms x8 = sys_input segs ms x8.
  Proof. intros ms x8. apply RomStable.sys_input_app_nw; first [exact Hnw | exact Hnx]. Qed.

  (* so robustness over the binary's list is robustness over the larger list
     (the argument of Common/Cfg/RomStable.v:503) *)
  Lemma ltO_sys_rob : forall c, RomBase.sys_rob segs c -> RomBase.sys_rob (segs ++ tail) c.
  Proof.
    intros c H r x8 Hrr Hs o. rewrite !ltO_sys_input. exact (H r x8 Hrr Hs o).
  Qed.

  (* A read the binary's list serves is served the same by the larger list
     (Common/Cfg/RomStable.v:335, as Common/Cfg/RunTailLazy.v:308 does for one byte). *)
  Lemma ltO_rdn_app : forall m a n bs,
    rdn segs m a n = Some bs -> rdn (segs ++ tail) m a n = Some bs.
  Proof.
    intros m a n bs H. rewrite <- ov_rdn in H |- *.
    exact (RomStable.ov_read_bytes_app_nx segs tail n m a bs H).
  Qed.

  (* The pending state's facts (LazyFdNodes.v:503-563), each taking the pending state and its
     restriction equation, with the larger list's backing. *)
  Lemma ltO_pend_gpr : forall msF1,
    restrict L S msF1 = epend regs pc mem (seg_rom (segs ++ tail)) (getr regs 17) ->
    forall k, ms_gpr msF1 k = ms_gpr (epend regs pc mem (seg_rom (segs ++ tail)) (getr regs 17)) k.
  Proof.
    intros msF1 Hr1 k. unfold ms_gpr.
    replace (ms_regs msF1) with (ms_regs (restrict L S msF1)) by reflexivity. rewrite Hr1. reflexivity.
  Qed.

  Lemma ltO_pend_mem : forall msF1,
    restrict L S msF1 = epend regs pc mem (seg_rom (segs ++ tail)) (getr regs 17) ->
    restrict_mem L S (ms_mem msF1) = mem.
  Proof.
    intros msF1 Hr1. transitivity (ms_mem (restrict L S msF1)); [reflexivity|]. rewrite Hr1. reflexivity.
  Qed.

  Lemma ltO_pend_rom : forall msF1,
    restrict L S msF1 = epend regs pc mem (seg_rom (segs ++ tail)) (getr regs 17) ->
    ms_rom msF1 = seg_rom (segs ++ tail).
  Proof.
    intros msF1 Hr1. transitivity (ms_rom (restrict L S msF1)); [reflexivity|]. rewrite Hr1. reflexivity.
  Qed.

  (* the call reads memory through the overlay, then the larger list's backing *)
  Lemma ltO_pend_in_mem : forall msF1,
    restrict L S msF1 = epend regs pc mem (seg_rom (segs ++ tail)) (getr regs 17) ->
    in_mem (sys_input segs msF1 (getr regs 17)) = mrb (segs ++ tail) (ms_mem msF1).
  Proof.
    intros msF1 Hr1. rewrite in_mem_si. apply functional_extensionality. intros a.
    unfold ms_read_byte, mrb. rewrite (ltO_pend_rom msF1 Hr1). reflexivity.
  Qed.

  Lemma ltO_openat_spec_head : forall msF1,
    restrict L S msF1 = epend regs pc mem (seg_rom (segs ++ tail)) (getr regs 17) ->
    forall o, syscall_spec (sys_input segs msF1 (getr regs 17)) mo o
      <-> openat_spec AT_FDCWD32 (getr regs 11) (getr regs 12) (sys_input segs msF1 (getr regs 17)) mo o.
  Proof.
    intros msF1 Hr1 o.
    rewrite (syscall_spec_56 _ mo o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
    rewrite in_arg0_si, in_arg1_si, in_arg2_si, !(ltO_pend_gpr msF1 Hr1),
      ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, H10.
    reflexivity.
  Qed.

  Lemma ltO_open_flags_modeled : modeled_open_flags (getr regs 12) = true.
  Proof. exact (modeled_open_flags_rd _ Hfl). Qed.

  (* The path read: the path facts are over the binary's list (path_at_lazy, LazyFdNodes.v:497);
     unrestricted at that list, then served the same by the larger list. *)
  Lemma ltO_path_full : forall msF1,
    restrict L S msF1 = epend regs pc mem (seg_rom (segs ++ tail)) (getr regs 17) ->
    forall p, path_at_lazy segs regs mem p ->
    rdn (segs ++ tail) (ms_mem msF1) (getr regs 11) (length p + 1) = Some (p ++ [Z_to_bv 8 0])
    /\ range_visible (hiddenb L S) (getr regs 11) (length p + 1)
    /\ read_cstr (in_mem (sys_input segs msF1 (getr regs 17))) (getr regs 11) = CstrOk p
    /\ open_reads (sys_input segs msF1 (getr regs 17)) (getr regs 11) = [(getr regs 11, (length p + 1)%nat)].
  Proof.
    intros msF1 Hr1 p (Hlen & Hnz & Hrd & Hts).
    rewrite <- (ltO_pend_mem msF1 Hr1) in Hrd.
    destruct (rdn_restrict segs L S (ms_mem msF1) (getr regs 11) (length p + 1) (p ++ [Z_to_bv 8 0])
                (lzok_ranges Hok) Hrd) as [HrdS Hvis].
    pose proof (ltO_rdn_app (ms_mem msF1) (getr regs 11) (length p + 1) (p ++ [Z_to_bv 8 0]) HrdS) as HrdF.
    split; [exact HrdF|]. split; [exact Hvis|].
    assert (Hlt : (length p < path_max)%nat) by (change path_max with 4096%nat; lia).
    split.
    - rewrite (ltO_pend_in_mem msF1 Hr1).
      exact (read_cstr_of_rdn (segs ++ tail) (ms_mem msF1) (getr regs 11) p Hlen Hnz Hts HrdF).
    - unfold open_reads. rewrite (ltO_pend_in_mem msF1 Hr1).
      rewrite (cstr_len_of_rdn (segs ++ tail) p path_max (ms_mem msF1) (getr regs 11) Hlt Hnz Hts HrdF).
      reflexivity.
  Qed.

  (* an openat whose path read does not fault reads the same over a larger backing
     (Common/Cfg/RomWrite.v:46) *)
  Lemma ltO_openat_rob : forall msF1,
    restrict L S msF1 = epend regs pc mem (seg_rom (segs ++ tail)) (getr regs 17) ->
    ms_svc_pending msF1 = Some (getr regs 17) ->
    read_cstr (in_mem (sys_input segs msF1 (getr regs 17))) (getr regs 11) <> CstrFault ->
    RomBase.sys_rob segs (mkCfg msF1 mo).
  Proof.
    intros msF1 Hr1 Hsvc1 Hnf.
    apply (RomWrite.openat_rob segs msF1 mo (getr regs 17) Hsvc1); [rewrite H17; apply u64_lit; lia |].
    rewrite (ltO_pend_gpr msF1 Hr1), ms_gpr_epend1. exact Hnf.
  Qed.

  (* One determined return (LazyFdNodes.v:566), through rz_fd_det_lazy_tail. *)
  Lemma ltO_openat_ret : forall msF1,
    lzok segs L S Zr (mkCfg msF1 mo) -> I (mkCfg msF1 mo) ->
    restrict L S msF1 = epend regs pc mem (seg_rom (segs ++ tail)) (getr regs 17) ->
    ms_svc_pending msF1 = Some (getr regs 17) ->
    forall (n : nat) r K,
    read_cstr (in_mem (sys_input segs msF1 (getr regs 17))) (getr regs 11) <> CstrFault ->
    (forall o, syscall_spec (sys_input segs msF1 (getr regs 17)) mo o
               <-> o = Ok (with_copyins [(getr regs 11, n)] (mkEffect r [] [])) mo []) ->
    range_visible (hiddenb L S) (getr regs 11) n ->
    (forall msF' mo', lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
       restrict L S msF' = post r -> hid_same L S msF1 msF' -> I (mkCfg msF' mo') ->
       realizes (segs ++ tail) (mkCfg msF' mo') K) ->
    realizes (segs ++ tail) (mkCfg msF1 mo) K.
  Proof.
    intros msF1 Hok1 HI1 Hr1 Hsvc1 n r K Hnf Hspec Hvis Hc.
    eapply (rz_fd_det_lazy_tail segs tail Hnx Hnw I HI L S Zr msF1 mo (getr regs 17)
              (with_copyins [(getr regs 11, n)] (mkEffect r [] [])) mo);
      [exact Hok1 | exact HI1 | exact Hsvc1 | exact (ltO_openat_rob msF1 Hr1 Hsvc1 Hnf) | exact Hspec
      | reflexivity | exact (lzok_halted Hok) | | |].
    - unfold syscall_effect_accesses, with_copyins. cbn. intros a k [Hin|[]]. injection Hin as <- <-. exact Hvis.
    - intros a Ha. rewrite apply_effect_ret_copyins_mem. reflexivity.
    - intros mo' Hok' Hsame Hhs HI'. apply (Hc _ mo' Hok' Hsame); [| exact Hhs | exact HI'].
      unfold post.
      rewrite <- (restrict_adv_ret (segs ++ tail) L S msF1 regs pc mem (getr regs 17) r [(getr regs 11, n)] Hr1).
      reflexivity.
  Qed.

  (* The open node with an error branch and a new-descriptor branch (LazyFdNodes.v:583), its node
     taken over the larger list and the invariant carried by HI on the node's step. *)
  Lemma ltO_open_lazy : forall msF1,
    lzok segs L S Zr (mkCfg msF1 mo) -> I (mkCfg msF1 mo) ->
    restrict L S msF1 = epend regs pc mem (seg_rom (segs ++ tail)) (getr regs 17) ->
    ms_svc_pending msF1 = Some (getr regs 17) ->
    forall (n : nat) (mk : word -> Model) KA KB,
    read_cstr (in_mem (sys_input segs msF1 (getr regs 17))) (getr regs 11) <> CstrFault ->
    injected_family_off the_scfg (sys_input segs msF1 (getr regs 17)) = false ->
    (forall o, syscall_spec (sys_input segs msF1 (getr regs 17)) mo o <-> open_out [(getr regs 11, n)] mo mk o) ->
    (forall fd, m_vm (mk fd) = m_vm mo) -> (forall fd, m_halted (mk fd) = None) ->
    fd_lookup (m_fds mo) (alloc_fd (m_fds mo)) = None ->
    range_visible (hiddenb L S) (getr regs 11) n ->
    (forall e msF' mo', In e openat_errnos ->
       lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
       restrict L S msF' = post (errno_ret e) -> hid_same L S msF1 msF' -> I (mkCfg msF' mo') ->
       realizes (segs ++ tail) (mkCfg msF' mo') KA) ->
    (forall msF' mo',
       lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized (mk (alloc_fd (m_fds mo))) mo' ->
       restrict L S msF' = post (alloc_fd (m_fds mo)) -> hid_same L S msF1 msF' -> I (mkCfg msF' mo') ->
       realizes (segs ++ tail) (mkCfg msF' mo') KB) ->
    realizes (segs ++ tail) (mkCfg msF1 mo) (t_alt2 KA KB).
  Proof.
    intros msF1 Hok1 HI1 Hr1 Hsvc1 n mk KA KB Hnf Hon Hspec Hvm Hmk Hfr Hvis HA HB.
    pose (effs := fun i : open_I mo => match i with
            | inl (exist _ e _) => with_copyins [(getr regs 11, n)] (mkEffect (errno_ret e) [] [])
            | inr _ => with_copyins [(getr regs 11, n)] (mkEffect (alloc_fd (m_fds mo)) [] []) end).
    pose (ms1 := fun i : open_I mo => match i with inl _ => mo | inr _ => mk (alloc_fd (m_fds mo)) end).
    assert (Hacc : forall i, syscall_effect_accesses (effs i) = [(getr regs 11, n)]).
    { intros [[e He]|[]]; reflexivity. }
    assert (Hmemi : forall i a, hiddenb L S a = true -> ms_mem (apply_effect msF1 (effs i)) a = ms_mem msF1 a).
    { intros [[e He]|[]] a Ha; unfold effs; rewrite apply_effect_ret_copyins_mem; reflexivity. }
    assert (Hvisl : ranges_visible (hiddenb L S) [(getr regs 11, n)]).
    { intros a k [Hin|[]]. injection Hin as <- <-. exact Hvis. }
    assert (Hstep : forall i, exists mo', materialize_model_accesses (ms1 i) (syscall_effect_accesses (effs i)) = Some mo'
               /\ same_but_materialized (ms1 i) mo'
               /\ lzok segs L S Zr (mkCfg (advance_past_svc (apply_effect msF1 (effs i))) mo')
               /\ hid_same L S msF1 (advance_past_svc (apply_effect msF1 (effs i)))).
    { intros i. rewrite Hacc. rewrite <- (Hacc i).
      apply (lzok_after_fd_op segs L S Zr msF1 mo (ms1 i) (effs i) Hok1).
      - destruct i as [[e He]|[]]; [reflexivity | apply Hvm].
      - destruct i as [[e He]|[]]; [exact (lzok_halted Hok) | apply Hmk].
      - rewrite Hacc. exact Hvisl.
      - exact (Hmemi i). }
    (* one model per branch, chosen from the materialization *)
    assert (Hch : exists f : open_I mo -> Model, forall i,
               materialize_model_accesses (ms1 i) (syscall_effect_accesses (effs i)) = Some (f i)
               /\ same_but_materialized (ms1 i) (f i)
               /\ lzok segs L S Zr (mkCfg (advance_past_svc (apply_effect msF1 (effs i))) (f i))
               /\ hid_same L S msF1 (advance_past_svc (apply_effect msF1 (effs i)))).
    { exists (fun i => match materialize_model_accesses (ms1 i) (syscall_effect_accesses (effs i)) with Some m => m | None => mo end).
      intros i. destruct (Hstep i) as (mo' & E & H1 & H2 & H3). rewrite E. auto. }
    destruct Hch as (f & Hf).
    (* the node over the larger list: its input is the binary list's input *)
    assert (Hspec' : forall o, syscall_spec (sys_input (segs ++ tail) msF1 (getr regs 17)) mo o
                               <-> open_out [(getr regs 11, n)] mo mk o).
    { intros o. rewrite ltO_sys_input. exact (Hspec o). }
    assert (Hnode : ShapeAlg.node_ok (segs ++ tail) (mkCfg msF1 mo) (open_I mo) (fun _ => [])
                      (fun i => mkCfg (advance_past_svc (apply_effect msF1 (effs i))) (f i))).
    { apply (node_family_mat (segs ++ tail) msF1 mo (getr regs 17) (open_I mo) effs ms1 f (fun _ => []) _
               (lzok_halted Hok1) Hsvc1 Hspec').
      - intros [[e He]|[]]; [left; exists e; auto | right; auto].
      - intros i. rewrite ltO_sys_input. apply spurious_refusal_family_on. exact Hon.
      - intros o [(e & He & ->) | (Hlk & ->)]; [exists (inl (exist _ e He)) | exists (inr tt)]; reflexivity.
      - intros [[e He]|[]]; [exact (lzok_halted Hok) | apply Hmk].
      - intros i. exact (proj1 (Hf i)). }
    (* the invariant at every branch, from HI on the node's step *)
    assert (HIn : forall i, I (mkCfg (advance_past_svc (apply_effect msF1 (effs i))) (f i))).
    { intros i. destruct Hnode as [Hsn _]. exact (HI _ _ _ HI1 (Hsn i)). }
    apply (rz_alt2 (segs ++ tail) (mkCfg msF1 mo) {e : Z | In e openat_errnos} unit
             (fun i => mkCfg (advance_past_svc (apply_effect msF1 (effs i))) (f i)) KA KB
             (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
    - exact Hnode.
    - exact (ltO_sys_rob _ (ltO_openat_rob msF1 Hr1 Hsvc1 Hnf)).
    - intros [e He]. unfold effs, ms1 in Hf |- *. cbv beta iota. destruct (Hf (inl (exist _ e He))) as (_ & Hs & Ho & Hh).
      cbv beta iota in Hs, Ho, Hh.
      apply (HA e _ _ He Ho Hs); [| exact Hh | exact (HIn (inl (exist _ e He)))].
      unfold post.
      rewrite <- (restrict_adv_ret (segs ++ tail) L S msF1 regs pc mem (getr regs 17) (errno_ret e) [(getr regs 11, n)] Hr1).
      reflexivity.
    - intros []. unfold effs, ms1 in Hf |- *. cbv beta iota. destruct (Hf (inr tt)) as (_ & Hs & Ho & Hh).
      cbv beta iota in Hs, Ho, Hh.
      apply (HB _ _ Ho Hs); [| exact Hh | exact (HIn (inr tt))].
      unfold post.
      rewrite <- (restrict_adv_ret (segs ++ tail) L S msF1 regs pc mem (getr regs 17) (alloc_fd (m_fds mo)) [(getr regs 11, n)] Hr1).
      reflexivity.
  Qed.

  (* A path of 4096 non-NUL bytes: -ENAMETOOLONG (LazyFdNodes.v:651). *)
  Theorem rz_openat_toolong_lazy_tail : forall bs K,
    rdn segs mem (getr regs 11) 4096 = Some bs -> ~ In (Z_to_bv 8 0) bs ->
    (bv_unsigned (getr regs 11) + 4096 <= TASK_SIZE)%Z ->
    (forall msF' mo', lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
       restrict L S msF' = post (errno_ret ENAMETOOLONG) -> hid_same L S msF msF' ->
       I (mkCfg msF' mo') ->
       realizes (segs ++ tail) (mkCfg msF' mo') K) ->
    realizes (segs ++ tail) (mkCfg msF mo) K.
  Proof using Hnx Hnw HI HF HE Hok HIc Hr H17 H10 Hfl.
    intros bs K Hrd Hnz Hts Hc.
    eapply (rz_sys_lazy_tail segs tail Hnx Hnw I HI); [exact Hok | exact HIc | exact Hr | exact HF | exact HE |].
    intros msF1 Hok1 Hr1 Hsvc1 Hhs1 HI1.
    pose proof (rdn_length _ _ _ _ _ Hrd) as Hlen.
    rewrite <- (ltO_pend_mem msF1 Hr1) in Hrd.
    destruct (rdn_restrict segs L S (ms_mem msF1) (getr regs 11) 4096 bs (lzok_ranges Hok) Hrd) as [HrdS Hvis].
    pose proof (ltO_rdn_app (ms_mem msF1) (getr regs 11) 4096 bs HrdS) as HrdF.
    apply (ltO_openat_ret msF1 Hok1 HI1 Hr1 Hsvc1 4096%nat (errno_ret ENAMETOOLONG) K).
    - rewrite (ltO_pend_in_mem msF1 Hr1),
        (read_cstr_toolong_of_rdn (segs ++ tail) (ms_mem msF1) (getr regs 11) bs Hlen Hnz Hts HrdF).
      discriminate.
    - intros o. rewrite (ltO_openat_spec_head msF1 Hr1).
      rewrite (openat_toolong_outcome _ _ _ _ mo ltO_open_flags_modeled o).
      + unfold open_reads. change path_max with 4096%nat.
        rewrite (ltO_pend_in_mem msF1 Hr1),
          (cstr_len_toolong_of_rdn (segs ++ tail) 4096 bs (ms_mem msF1) (getr regs 11) Hlen Hnz
             ltac:(intros _; first [change (Z.of_nat 4096) with 4096%Z; exact Hts | lia]) HrdF).
        reflexivity.
      + rewrite (ltO_pend_in_mem msF1 Hr1).
        exact (read_cstr_toolong_of_rdn (segs ++ tail) (ms_mem msF1) (getr regs 11) bs Hlen Hnz Hts HrdF).
    - exact Hvis.
    - intros msF' mo' Hok' Hsame Hr' Hhs' HI'. apply (Hc msF' mo' Hok' Hsame Hr');
        [eapply hid_same_trans; eassumption | exact HI'].
  Qed.

  (* The empty path: -ENOENT (LazyFdNodes.v:681). *)
  Theorem rz_openat_empty_lazy_tail : forall K,
    path_at_lazy segs regs mem [] ->
    (forall msF' mo', lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
       restrict L S msF' = post (errno_ret ENOENT) -> hid_same L S msF msF' ->
       I (mkCfg msF' mo') ->
       realizes (segs ++ tail) (mkCfg msF' mo') K) ->
    realizes (segs ++ tail) (mkCfg msF mo) K.
  Proof using Hnx Hnw HI HF HE Hok HIc Hr H17 H10 Hfl.
    intros K Hp Hc.
    eapply (rz_sys_lazy_tail segs tail Hnx Hnw I HI); [exact Hok | exact HIc | exact Hr | exact HF | exact HE |].
    intros msF1 Hok1 Hr1 Hsvc1 Hhs1 HI1.
    destruct (ltO_path_full msF1 Hr1 [] Hp) as (HrdF & Hvis & Hcs & Hreads).
    apply (ltO_openat_ret msF1 Hok1 HI1 Hr1 Hsvc1 (length (@nil byte) + 1) (errno_ret ENOENT) K).
    - rewrite Hcs. discriminate.
    - intros o. rewrite (ltO_openat_spec_head msF1 Hr1).
      rewrite (openat_empty_outcome _ _ _ _ mo ltO_open_flags_modeled o Hcs), Hreads. reflexivity.
    - exact Hvis.
    - intros msF' mo' Hok' Hsame Hr' Hhs' HI'. apply (Hc msF' mo' Hok' Hsame Hr');
        [eapply hid_same_trans; eassumption | exact HI'].
  Qed.

  (* A plain name the file system does not hold: -ENOENT (LazyFdNodes.v:701). *)
  Theorem rz_openat_absent_lazy_tail : forall p K,
    path_at_lazy segs regs mem p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
    fs_lookup (m_fs mo) p = None ->
    (forall msF' mo', lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
       restrict L S msF' = post (errno_ret ENOENT) -> hid_same L S msF msF' ->
       I (mkCfg msF' mo') ->
       realizes (segs ++ tail) (mkCfg msF' mo') K) ->
    realizes (segs ++ tail) (mkCfg msF mo) K.
  Proof using Hnx Hnw HI HF HE Hok HIc Hr H17 H10 Hfl.
    intros p K Hp Hne Hsl Hnd Hfs Hc.
    eapply (rz_sys_lazy_tail segs tail Hnx Hnw I HI); [exact Hok | exact HIc | exact Hr | exact HF | exact HE |].
    intros msF1 Hok1 Hr1 Hsvc1 Hhs1 HI1.
    destruct (ltO_path_full msF1 Hr1 p Hp) as (HrdF & Hvis & Hcs & Hreads).
    apply (ltO_openat_ret msF1 Hok1 HI1 Hr1 Hsvc1 (length p + 1) (errno_ret ENOENT) K).
    - rewrite Hcs. discriminate.
    - intros o. rewrite (ltO_openat_spec_head msF1 Hr1).
      rewrite (openat_absent_outcome _ _ _ _ mo ltO_open_flags_modeled eq_refl Hfl p o Hcs Hne Hsl Hnd Hfs), Hreads.
      reflexivity.
    - exact Hvis.
    - intros msF' mo' Hok' Hsame Hr' Hhs' HI'. apply (Hc msF' mo' Hok' Hsame Hr');
        [eapply hid_same_trans; eassumption | exact HI'].
  Qed.

  Hypothesis Hfree : fd_lookup fds (alloc_fd fds) = None.
  Context {FM : FsMayFail SC}.

  (* "." or "..": a directory descriptor, or an injected error (LazyFdNodes.v:726). *)
  Theorem rz_openat_dot_lazy_tail : forall p KA KB,
    path_at_lazy segs regs mem p -> path_is_dirref p = true ->
    (forall e msF' mo', In e openat_errnos ->
       lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
       restrict L S msF' = post (errno_ret e) -> hid_same L S msF msF' ->
       I (mkCfg msF' mo') ->
       realizes (segs ++ tail) (mkCfg msF' mo') KA) ->
    (forall msF' mo',
       lzok segs L S Zr (mkCfg msF' mo') ->
       same_but_materialized (with_fds (fd_insert fds (alloc_fd fds) FdDir) mo) mo' ->
       restrict L S msF' = post (alloc_fd fds) -> hid_same L S msF msF' ->
       I (mkCfg msF' mo') ->
       realizes (segs ++ tail) (mkCfg msF' mo') KB) ->
    realizes (segs ++ tail) (mkCfg msF mo) (t_alt2 KA KB).
  Proof using Hnx Hnw HI HF HE Hok HIc Hr H17 H10 Hfl Hfree FM.
    intros p KA KB Hp Hdr HA HB.
    eapply (rz_sys_lazy_tail segs tail Hnx Hnw I HI); [exact Hok | exact HIc | exact Hr | exact HF | exact HE |].
    intros msF1 Hok1 Hr1 Hsvc1 Hhs1 HI1.
    destruct (ltO_path_full msF1 Hr1 p Hp) as (HrdF & Hvis & Hcs & Hreads).
    apply (ltO_open_lazy msF1 Hok1 HI1 Hr1 Hsvc1 (length p + 1) (fun fd => with_fds (fd_insert fds fd FdDir) mo) KA KB).
    - rewrite Hcs. discriminate.
    - apply family_off_openat_false. rewrite in_sysno_si, H17. apply u64_lit. lia.
    - intros o. rewrite (ltO_openat_spec_head msF1 Hr1).
      rewrite (openat_dot_outcome _ _ _ _ mo ltO_open_flags_modeled eq_refl Hfl p o Hcs Hdr), Hreads. reflexivity.
    - intros fd. reflexivity.
    - intros fd. cbv delta [fds]. rewrite with_fds_halted'. exact (lzok_halted Hok).
    - exact Hfree.
    - exact Hvis.
    - intros e msF' mo' He Hok' Hsame Hr' Hhs' HI'. apply (HA e msF' mo' He Hok' Hsame Hr');
        [eapply hid_same_trans; eassumption | exact HI'].
    - intros msF' mo' Hok' Hsame Hr' Hhs' HI'. apply (HB msF' mo' Hok' Hsame Hr');
        [eapply hid_same_trans; eassumption | exact HI'].
  Qed.

  (* A plain name the file system holds: a file descriptor at offset 0, or an injected error
     (LazyFdNodes.v:755). *)
  Theorem rz_openat_file_lazy_tail : forall p d KA KB,
    path_at_lazy segs regs mem p -> p <> [] -> path_has_slash p = false -> path_is_dirref p = false ->
    fs_lookup (m_fs mo) p = Some d ->
    (forall e msF' mo', In e openat_errnos ->
       lzok segs L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' ->
       restrict L S msF' = post (errno_ret e) -> hid_same L S msF msF' ->
       I (mkCfg msF' mo') ->
       realizes (segs ++ tail) (mkCfg msF' mo') KA) ->
    (forall msF' mo',
       lzok segs L S Zr (mkCfg msF' mo') ->
       same_but_materialized (with_fds (fd_insert fds (alloc_fd fds) (FdFile p (Z_to_bv 64 0))) mo) mo' ->
       restrict L S msF' = post (alloc_fd fds) -> hid_same L S msF msF' ->
       I (mkCfg msF' mo') ->
       realizes (segs ++ tail) (mkCfg msF' mo') KB) ->
    realizes (segs ++ tail) (mkCfg msF mo) (t_alt2 KA KB).
  Proof using Hnx Hnw HI HF HE Hok HIc Hr H17 H10 Hfl Hfree FM.
    intros p d KA KB Hp Hne Hsl Hnd Hfs HA HB.
    eapply (rz_sys_lazy_tail segs tail Hnx Hnw I HI); [exact Hok | exact HIc | exact Hr | exact HF | exact HE |].
    intros msF1 Hok1 Hr1 Hsvc1 Hhs1 HI1.
    destruct (ltO_path_full msF1 Hr1 p Hp) as (HrdF & Hvis & Hcs & Hreads).
    apply (ltO_open_lazy msF1 Hok1 HI1 Hr1 Hsvc1 (length p + 1)
             (fun fd => with_fds (fd_insert fds fd (FdFile p (Z_to_bv 64 0))) mo) KA KB).
    - rewrite Hcs. discriminate.
    - apply family_off_openat_false. rewrite in_sysno_si, H17. apply u64_lit. lia.
    - intros o. rewrite (ltO_openat_spec_head msF1 Hr1).
      rewrite (openat_file_outcome _ _ _ _ mo ltO_open_flags_modeled eq_refl Hfl p d o Hcs Hne Hsl Hnd Hfs), Hreads.
      reflexivity.
    - intros fd. reflexivity.
    - intros fd. cbv delta [fds]. rewrite with_fds_halted'. exact (lzok_halted Hok).
    - exact Hfree.
    - exact Hvis.
    - intros e msF' mo' He Hok' Hsame Hr' Hhs' HI'. apply (HA e msF' mo' He Hok' Hsame Hr');
        [eapply hid_same_trans; eassumption | exact HI'].
    - intros msF' mo' Hok' Hsame Hr' Hhs' HI'. apply (HB msF' mo' Hok' Hsame Hr');
        [eapply hid_same_trans; eassumption | exact HI'].
  Qed.
End OpenatLazyTail.
