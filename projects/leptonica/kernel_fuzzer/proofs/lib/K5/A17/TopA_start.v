(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (asan_startup_gen for every kernel valid_input admits, with one start-up certificate per CONFIG_RSEQ value, over the launch record and its launch facts, valid_input's channel-reader conjunct read where the dropped in_sigpipe_default conjunct was, the run's target_alloc_limit restated as AsanInit.LIMIT for init_cfg_eq, and argH0_high given the entry pc; init_cfg_gen over the whole ProcInput with the vDSO run state; cs_ok_inp removed, the input no longer being taken apart; module paths qualified as K5.AS.PropExec where a twin module shadows them). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem Require Vdso.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import PropExec.
Local Instance topa_fx : K5.AS.PropExec.FPState := K5.AS.PropExec.fx0.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import ShapeAlg SpinAlg AgentLib AsanAcct.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS17 Require Import AsanAcctImages.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS17 Require Import AsanPlanImages.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import AsanInit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS17 Require Import AsanTablesA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import AsanNodesIface AsanNodesMmA AsanNodesMmB.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS17 Require Import SumsAsanClose.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS Require Import AsanNodesStartX.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AS17 Require Import AsanNodesStartXAsan AsanSmearA AsanHeapSortA AsanStartup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint holes_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SCase _ _ a b => (holes_only a && holes_only b)%bool
  | SAlt2 a b => (holes_only a && holes_only b)%bool
  | _ => false
  end.

(* [comment removed for export] *)
Lemma sd_holes_only : forall (HOLES : nat -> env -> Fs.Fs -> TSet) (D : TSet) (E : env) (fs : Fs.Fs) (T : TSet) (s : shape),
  (forall h, t_eq (HOLES h E fs) T) -> holes_only s = true -> t_eq (sd HOLES D E fs s) T.
Proof.
  intros HOLES D E fs T s HH. induction s as [| c | fd ps s' IH | a IHa b IHb | e mid a IHa b IHb | h | ];
    cbn [holes_only sd]; intros Hs; try discriminate.
  - apply andb_prop in Hs as [H1 H2]. intros tr. unfold t_alt2. rewrite (IHa H1 tr), (IHb H2 tr). tauto.
  - apply andb_prop in Hs as [H1 H2]. destruct (bv_unsigned (edenot E e) <=? mid); [exact (IHa H1) | exact (IHb H2)].
  - exact (HH h).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* The initial model of the run's input, with the launch's vDSO draw *)
Lemma init_cfg_gen : forall segs (apc : N) ph sp brk0 mbase rdraw lim inp,
  init_config segs apc ph sp brk0 mbase rdraw lim inp
  = cfg_of segs (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp) (Z.of_N apc)
           (wrap_mem inp mbase ph (Z_to_bv 64 (Z.of_N apc)) sp rdraw)
           (with_vdso (Vdso.vdso_run_init (ed_vdso rdraw)) (init_model (segments_reserved segs) brk0 mbase sp lim inp)).
Proof.
  intros segs apc ph sp brk0 mbase rdraw lim inp.
  unfold init_config, cfg_of. rewrite init_mkst. reflexivity.
Qed.

Section StartupGen.
  (* the certificates and the hand-off tables, ONE PER CONFIG_RSEQ VALUE [b]: [kb_rseq] is free
     under [Run.valid_input] (LPS 75d69e00 Run.v:4575-4581), so the start-up is checked from
     [asan_a_init (rseq_z b)] for each [b] and the run's own flag picks the certificate *)
  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  Variable HS_asan : bool -> nat -> option acs.
  Variable startup_plan : bool -> plan.
  Variable startup_shape : bool -> shape.
  Variables KC0 BFUEL FUEL : nat.
  Hypothesis startup_cert : forall b,
    check ASEGS IT0 ASAN_A NX0 AsanInit.LIMIT XN0 XE0 XB0 (HS_asan b) KC0 BFUEL FUEL None (asan_a_init (rseq_z b)) (startup_plan b)
    = COk (startup_shape b).
  Hypothesis Hshape : forall b, holes_only (startup_shape b) = true.

  (* the hand-off states, read against the main program *)
  Variable T : list (list byte) -> Fs.Fs -> TSet.
  Hypothesis T_nil : forall argv fs, T argv fs [].
  Hypothesis T_holes : forall (b : bool) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
    valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_launch inp ->
    entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
    holes_stmt ASEGS ASAN_A NX0 AsanInit.LIMIT (HS_asan b)
               (SINV0 APH Asan.M.init_pc sp rdraw brk0 mbase inp) (argH0 sp rdraw inp)
               (fun _ _ fs' => T (in_argv inp) fs') (in_fs inp).

  (* the start-up over the image's own segments, for EVERY kernel [Run.valid_input] admits: the
     kernel of record comes from [Run.valid_input_recorded_kernel], and the certificate is the one
     at the run's own [kb_rseq].  It WAS stated under [in_kernel inp = default_kernel], which
     [kb_rseq = false] refutes. *)
  Theorem asan_startup_gen : forall en inp,
    valid_entry (mkImage ASEGS Asan.M.init_pc APH) en inp -> valid_input inp ->
    srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
                                 target_alloc_limit inp)
              (T (in_argv inp) (in_fs inp)).
  Proof using IT0_ok startup_cert Hshape T_nil T_holes.
    intros en inp Hve Hvi.
    pose proof (valid_input_recorded_kernel inp Hvi) as Hrec.
    set (b := kb_rseq (in_kernel inp)).
    destruct en as [sp brk0 mbase rdraw].
    rewrite (valid_entry_sv48 _ _ _ (valid_input_va_size _ Hvi)) in Hve. destruct Hve as (Hsp & Hbrk & Hmb & Hfit & Hlau).
    (* LPS 727298f3 (model 5040944): [Run.valid_input] no longer pins [in_sigpipe_default], so the
       channel reader is the conjunct right after the launch facts *)
    destruct Hvi as (Hva & Hvenv & _ & _ & _ & (Huid & _) & _ & _ & _ & Hab & Hsv & _ & Hlaunch & Hcr & _).
    cbn [en_sp en_brk en_mmap_base en_draw] in *.
    set (SINV := SINV0 APH Asan.M.init_pc sp rdraw brk0 mbase inp).
    set (argH := argH0 sp rdraw inp).
    set (HOLES := fun (_ : nat) (_ : env) (fs' : Fs.Fs) => T (in_argv inp) fs').
    assert (HC : cs_ok ASEGS ASAN_A NX0 AsanInit.LIMIT SINV argH (in_fs inp)
                       (E0 sp rdraw brk0 mbase inp) (asan_a_init (rseq_z b)) (R0 sp)
                       (FULL0 APH Asan.M.init_pc sp rdraw mbase inp)
                       (model0 ASEGS sp rdraw brk0 mbase inp))
      by (eapply init_cs_ok; first [exact asan_img_facts | reflexivity | eassumption]).
    (* the theorem names the run's limit [target_alloc_limit]; [init_cfg_eq] states it as
       [AsanInit.LIMIT], the same constant, which [rewrite] does not unfold *)
    match goal with |- srealizes _ ?c _ =>
      change c with (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw AsanInit.LIMIT inp) end.
    rewrite (init_cfg_eq ASEGS ASAN_A APH Asan.M.init_pc sp rdraw brk0 mbase inp eq_refl).
    assert (AH : forall E a, argH E a = true -> CEIL <= bv_unsigned a)
      (* [argH0_high] is stated over [Section Init]'s [apc : N], which its conclusion does not
         mention, so the entry pc is named here (as in AS17/AsanStartup.v) *)
      by (intros E a H; eapply argH0_high; first [eassumption | exact Asan.M.init_pc]).
    pose proof (argH0_agree sp rdraw inp) as AA.
    pose proof (SINV0_frame APH Asan.M.init_pc sp rdraw brk0 mbase inp) as SF.
    pose proof (SINV0_agree APH Asan.M.init_pc sp rdraw brk0 mbase inp) as SA.
    assert (XS : forall x, x_stmt ASEGS ASAN_A NX0 AsanInit.LIMIT SINV argH (in_fs inp) x)
      by (eapply asan_node_x_sound_all; first [eassumption | exact (fun E M H => H) | exact SF | exact SA]).
    assert (HOLES_agree : forall h E E' fs', env_agree NX0 E E' -> HOLES h E fs' = HOLES h E' fs') by (intros; reflexivity).
    assert (HOLES_nil : forall h E fs', HOLES h E fs' []) by (intros h E fs'; exact (T_nil (in_argv inp) fs')).
    pose proof (T_holes b sp rdraw brk0 mbase inp Hsp Hva Hvenv Hlaunch Hlau) as HOLES_sound.
    apply (srz_conseq ASEGS _ (sd HOLES t_nil (E0 sp rdraw brk0 mbase inp) (in_fs inp) (startup_shape b))).
    - exact (check_sound ASEGS IT0 IT0_ok ASAN_A NX0 AsanInit.LIMIT (HS_asan b) XN0 XE0 XB0
              asan_wx asan_in_hull asan_hull_ok asan_shadow_ok SINV argH AH AA SF SA
              HOLES HOLES_agree HOLES_nil (in_fs inp) KC0
              (AsanNodesMmB.node_sys_sound ASEGS ASAN_A NX0 AsanInit.LIMIT SINV argH (in_fs inp) asan_res_len asan_hull_ok asan_shadow_ok AA SF SA)
              (AsanNodesMmB.node_brk2_sound ASEGS ASAN_A NX0 AsanInit.LIMIT SINV argH (in_fs inp) asan_in_hull asan_res_hull asan_hull_ok asan_shadow_ok AH SF)
              (AsanNodesMmB.node_brk2s_sound ASEGS ASAN_A NX0 AsanInit.LIMIT SINV argH (in_fs inp) asan_in_hull asan_res_hull asan_hull_ok asan_shadow_ok AH SF)
              (node_mmap2_sound_OBL ASEGS ASAN_A NX0 AsanInit.LIMIT SINV argH (in_fs inp) asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA asan_hull_cover)
              (node_mmapin_sound_OBL ASEGS ASAN_A NX0 AsanInit.LIMIT SINV argH (in_fs inp) asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA asan_hull_cover)
              (node_mprotect2_sound_OBL ASEGS ASAN_A NX0 AsanInit.LIMIT SINV argH (in_fs inp) asan_in_hull asan_res_len asan_res_hull asan_hull_ok asan_shadow_ok AH AA SF SA asan_hull_cover)
              (AsanNodesMmB.node_exit_sound ASEGS ASAN_A NX0 AsanInit.LIMIT SINV argH (in_fs inp))
              XS
              (node_join_sound ASEGS ASAN_A NX0 AsanInit.LIMIT SINV argH (in_fs inp))
              (XN0_sound _ _ _ _ _ _ _) (XE0_sound _ _ _ _ _ _ _) (XB0_sound _ _ _ _ _ _ _)
              HOLES_sound FUEL BFUEL None (startup_plan b) (asan_a_init (rseq_z b)) (startup_shape b) (startup_cert b)
              _ _ _ _ t_nil HC I eq_refl).
    - apply sd_holes_only; [intros h tr; reflexivity | exact (Hshape b)].
  Qed.
End StartupGen.
