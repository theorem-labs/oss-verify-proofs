(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: a_boot quantifies the execfn and the kernel build, takes valid_launch and the launch placement (entry_launch_ok_va), and passes them with the mmap-base premise to asan_boot; the main phase's holes take the same launch input (a_holes_of); a_boot quantifies the input's SIGPIPE-default flag, which Run.valid_input leaves free. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg AMainEntry AHandoff.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require ShapeAlg SpinAlg AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanImages AsanInit AsanBoot.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation ASEGS := AS.AsanPlanImages.ASEGS (only parsing).
Local Notation APH := AS.AsanPlanImages.APH (only parsing).

(* [comment removed for export] *)
Lemma t_die_has_nil : forall msg fs, t_die msg fs [].
Proof. intros. unfold t_die. apply t_emit_has_nil. Qed.

Lemma spec04_has_nil : forall argv fs, spec04 argv fs [].
Proof.
  intros argv fs. unfold spec04, spec.
  destruct argv as [|a0 [|path [|x r]]]; try apply t_die_has_nil.
  destruct (4096 <=? length path)%nat; [apply t_die_has_nil|].
  destruct (list_byte_eqb path []); [apply t_die_has_nil|].
  destruct (list_byte_eqb path dot_path); [left; apply t_die_has_nil|].
  destruct (fs_lookup fs path); [left; apply t_die_has_nil| apply t_die_has_nil].
Qed.

Theorem a_boot : a_main_stmt ->
  forall (sp brk0 mbase : word) (rdraw : EntryDraw) (argv envp : list (list byte)) (ifs : Fs.Fs) (stdin : InputStream)
         (uid gid hw : word) (groups : list word) (net : NetQueue) (nof sigm : word) (abt : bool)
         (urnd : InputStream) (tmp : Fs.Fs) (xfn : list byte) (kb : KernelBuild) (sgd : bool),   (* kb is QUANTIFIED here, never pinned: AsanInit.inp builds the kernel field as (recorded_kernel kb), which fixes the eight fields Run.recorded_kernel pins and leaves kb_thp, kb_aslr, kb_guard, kb_rnd_bits and kb_rseq free *)
    valid_sp sp -> valid_brk ASEGS brk0 -> valid_mmap_base mbase ->
    valid_argv argv -> valid_envp envp -> valid_fs (fs_seed_tmp ifs tmp) -> entry_stack_fits sp argv envp -> valid_id uid -> valid_hwcap hw ->
    (* [comment removed for export] *)
    valid_launch (AS.AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd) ->
    entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
      (AS.AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd) ->
    AS.SpinAlg.srealizes ASEGS
      (init_config ASEGS Asan.M.init_pc APH sp brk0 mbase rdraw AS.AsanInit.LIMIT
                   (AS.AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd))
      (spec04 argv (fs_seed_tmp ifs tmp)).   (* [comment removed for export] *)
Proof.
  intros HM sp brk0 mbase rdraw argv envp ifs stdin uid gid hw groups net nof sigm abt urnd tmp xfn kb sgd Hsp Hbrk Hmb Hva Hve Hfs Hfit Huid Hhw Hlaunch Hlau.
  apply (AS.AsanBoot.asan_boot Asan.M.init_pc sp rdraw brk0 mbase argv envp (fs_seed_tmp ifs tmp) stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd
           eq_refl eq_refl Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw Hlaunch Hlau (fun _ fs' => spec04 argv fs')).
  - intros; reflexivity.
  - intros; apply spec04_has_nil.
  - exact (a_holes_of HM sp rdraw brk0 mbase argv envp (fs_seed_tmp ifs tmp) stdin uid gid hw groups net nof sigm abt ifs urnd tmp xfn kb sgd
             eq_refl Hsp Hbrk Hmb Hva Hve Hfs Hfit Huid Hhw Hlaunch Hlau).
Qed.
