(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg AMainEntry AHandoff.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.AS Require ShapeAlg SpinAlg AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound BothPlanImages AsanInit BothBoot.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation BSEGS := AS.BothPlanImages.BSEGS (only parsing).
Local Notation BPH := AS.BothPlanImages.BPH (only parsing).

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
         (urnd : InputStream) (tmp : Fs.Fs),   (* [comment removed for export] *)
    valid_sp sp -> valid_brk BSEGS brk0 -> valid_mmap_base mbase ->
    valid_argv argv -> valid_envp envp -> valid_fs (fs_seed_tmp ifs tmp) -> entry_stack_fits sp argv envp -> valid_id uid -> valid_hwcap hw ->
    AS.SpinAlg.srealizes BSEGS
      (init_config BSEGS AsanUbsan.M.init_pc BPH sp brk0 mbase rdraw AS.AsanInit.LIMIT
                   (AS.AsanInit.inp argv envp stdin uid gid hw groups net nof sigm abt ifs urnd tmp))
      (spec04 argv (fs_seed_tmp ifs tmp)).   (* [comment removed for export] *)
Proof.
  intros HM sp brk0 mbase rdraw argv envp ifs stdin uid gid hw groups net nof sigm abt urnd tmp Hsp Hbrk Hmb Hva Hve Hfs Hfit Huid Hhw.
  apply (AS.BothBoot.both_boot sp rdraw brk0 mbase argv envp (fs_seed_tmp ifs tmp) stdin uid gid hw groups net nof sigm abt ifs urnd tmp eq_refl
           Hsp Hbrk Hva Hve Hfit Huid Hhw (fun _ fs' => spec04 argv fs')).
  - intros; reflexivity.
  - intros; apply spec04_has_nil.
  - exact (a_holes_of HM sp brk0 mbase rdraw argv envp (fs_seed_tmp ifs tmp) uid hw Hsp Hbrk Hmb Hva Hve Hfs Hfit Huid Hhw).
Qed.
