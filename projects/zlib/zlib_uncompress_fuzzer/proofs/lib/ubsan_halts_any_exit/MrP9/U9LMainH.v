(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import ModelAmb.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem Require Import Vdso.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_zlib_uncompress_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Frame
  Spec ShapeLaws DrawDefs U9Startup U9MainEntry U9Usage U9OpenFail U9LPilotOOM.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Lib Require RunConst.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.MrP9 Require U9HeapPre U9LRdTop U9LRdDir U9RdAI U9RdLeaf U9RdLeafHdr.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition rsegs := Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments.
Definition rpc := Tgt_zlib_uncompress_fuzzer_ubsan.M.init_pc.
Definition rph := Tgt_zlib_uncompress_fuzzer_ubsan.M.phdrs.

Lemma ref_list_byte_eqb_eq : forall p q, list_byte_eqb p q = true <-> p = q.
Proof.
  induction p as [|a p IH]; destruct q as [|b q]; cbn; try (split; congruence).
  rewrite Bool.andb_true_iff, IH. unfold bv_eqb. rewrite Z.eqb_eq.
  split.
  - intros [H1 ->]. f_equal. apply bv_eq. exact H1.
  - intros H. injection H. intros -> ->. auto.
Qed.

Definition rc_of (sp : word) (draw : EntryDraw) (Hsp : valid_sp sp) : RunConst.runConstT.
Proof.
  refine (RunConst.RunConst (bv_unsigned sp - 8388608) (bv_unsigned (secret_w draw)) (canary_w draw) _ _ _ _).
  - destruct Hsp as (A & _ & _). unfold sp_window_lo in A. lia.
  - destruct Hsp as (_ & B & _). unfold sp_window_hi in B. lia.
  - destruct Hsp as (_ & _ & C). rewrite Zminus_mod, C. reflexivity.
  - pose proof (bv_unsigned_in_range _ (secret_w draw)) as X. change (bv_modulus 64) with (2 ^ 64)%Z in X. exact X.
Defined.

(* the launch premises (valid_launch, LOK, the channel reader) replace entry_stack_fits;
   ref_startup (S0 form) hands main the start model with_tid (with_vdso (vdso_run_init (ed_vdso draw))
   (init_model ..)), which is every branch's model0 by conversion. No ProcInput destructuring: the read chain's AmbIn
   and file system are the launch's (ModelAmb.amb_of inp (the run's vDSO run inside) and in_fs inp). *)
Theorem u9_realizes_spec_tp :
  (forall (RCx : RunCtx) (rc : RunConst.runConstT), @U9HeapPre.target_phase_h_stmt RCx rc) ->  (* the target phase for every run *)
  forall sp brk mbase (draw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk rsegs brk ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp -> in_channel_reader inp = true ->
    realizes (run_segments rsegs inp sp mbase)
      (init_config (run_segments rsegs inp sp mbase) rpc rph sp brk mbase draw source_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).
Proof.
  intros TPH sp brk mbase draw inp Hsp Hbrk Hva Hve Hfs Hvl Hlau Hcr.
  change source_alloc_limit with LIM.
  apply (ref_startup sp brk mbase draw LIM inp _ Hsp Hbrk Hva Hve Hvl Hlau).
  intros tid regs mem Htid ME.
  pose (rc := rc_of sp draw Hsp).
  destruct (in_argv inp) as [|a0s [|path [|x l]]] eqn:Hav.
  - pose proof (ref_usage_w sp inp draw tid regs mem brk mbase LIM (eq_rect_r valid_argv Hva Hav) Hvl Hlau Hcr Hsp Htid ME
                  ltac:(rewrite Hav; cbn; lia)) as H.
    rewrite Hav in H. exact H.
  - pose proof (ref_usage_w sp inp draw tid regs mem brk mbase LIM (eq_rect_r valid_argv Hva Hav) Hvl Hlau Hcr Hsp Htid ME
                  ltac:(rewrite Hav; cbn; lia)) as H.
    rewrite Hav in H. exact H.
  - cbn [spec].
    destruct (Nat.leb_spec0 4096 (length path)) as [Hlong|Hshort].
    + exact (ref_open_fail_toolong_w sp a0s path inp draw tid regs mem brk mbase LIM Hav Hva Hvl Hlau Hcr Hsp Htid ME Hlong).
    + destruct (list_byte_eqb path []) eqn:Hemp.
      * apply ref_list_byte_eqb_eq in Hemp.
        exact (ref_open_fail_empty_w sp a0s path inp draw tid regs mem brk mbase LIM Hav Hva Hvl Hlau Hcr Hsp Htid ME Hemp).
      * assert (Hne : path <> []) by (intros E; apply ref_list_byte_eqb_eq in E; rewrite E in Hemp; discriminate).
        destruct (list_byte_eqb path dot_path) eqn:Hdot.
        --
           apply ref_list_byte_eqb_eq in Hdot. subst path.
           replace (0x148f8 : word) with (Z_to_bv 64 0x148f8) by (apply bv_eq; reflexivity).
           (* the start model is model0 sp inp draw tid brk mbase by conversion (S8PilotOOM) *)
           exact (U9LRdDir.dir_phase_h (rc := rc) sp a0s inp draw tid regs mem brk mbase Hav Hva Hve Hvl Hlau Hcr Hsp Htid ME Hbrk
                    eq_refl eq_refl eq_refl U9RdAI.AI (U9RdAI.rule_malloc_first_proof (rc := rc))).
        -- assert (Hnd : path <> dot_path)
             by (intros E; apply ref_list_byte_eqb_eq in E; rewrite E in Hdot; discriminate).
           destruct (fs_lookup (in_fs inp) path) as [data|] eqn:Hlk.
           ++
              replace (0x148f8 : word) with (Z_to_bv 64 0x148f8) by (apply bv_eq; reflexivity).
              set (stdin0 := ModelAmb.amb_of inp (vdso_run_init (ed_vdso draw))).
              exact (U9LRdTop.read_phase_h (rc := rc) sp a0s path inp draw tid regs mem brk mbase data
                       Hav Hva Hve Hvl Hlau Hcr Hsp Htid ME Hbrk Hlk Hne Hnd ltac:(lia) eq_refl eq_refl eq_refl
                       U9RdAI.AI U9RdAI.AIm
                       (U9RdAI.rule_malloc_first_proof (rc := rc)) (U9RdAI.rule_malloc_grow_proof (rc := rc))
                       (U9RdAI.rule_free_grow_proof (rc := rc)) U9RdAI.AIm_perm U9RdAI.AI_vm U9RdAI.AI_end
                       (TPH _ rc)
                       (U9RdLeaf.leaf_oom1 (rc := rc) sp Hsp path stdin0 (in_fs inp) tid data Htid)
                       (U9RdLeaf.leaf_oom (rc := rc) sp Hsp path stdin0 (in_fs inp) tid data Htid)
                       (U9RdLeaf.leaf_refused (rc := rc) sp Hsp path stdin0 (in_fs inp) tid data Htid)
                       (U9RdLeafHdr.leaf_short (rc := rc) sp Hsp eq_refl inp draw tid data Htid U9RdAI.AI)
                       (U9RdLeafHdr.leaf_overrun (rc := rc) sp Hsp eq_refl inp draw tid data Htid U9RdAI.AI)).
           ++ exact (ref_open_fail_absent_w sp a0s path inp draw tid regs mem brk mbase LIM Hav Hva Hvl Hlau Hcr Hsp Htid ME
                       ltac:(lia) Hne Hnd Hlk).
  - pose proof (ref_usage_w sp inp draw tid regs mem brk mbase LIM (eq_rect_r valid_argv Hva Hav) Hvl Hlau Hcr Hsp Htid ME
                  ltac:(rewrite Hav; cbn; lia)) as H.
    rewrite Hav in H. exact H.
Qed.
