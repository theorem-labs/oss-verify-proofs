(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec ShapeAlg ShapeLaws SpinAlg Scfg Spec HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsIface AsIfaceX AsDriverLaws ECH_Iface AsDrvDefs AsMainPre AsInstance F_time AInstFacts.
Import ListNotations.
Import OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma spec_has_nil : forall argv fs, spec argv fs [].
Proof.
  intros argv fs. unfold spec.
  destruct argv as [|a0 [|p [|x l]]]; try (apply t_emit_has_nil).
  destruct (4096 <=? length p)%nat; [apply t_emit_has_nil|].
  destruct (list_byte_eqb p []); [apply t_emit_has_nil|].
  destruct (list_byte_eqb p dot_path); [apply t_alt2_has_nil_l; apply t_emit_has_nil|].
  destruct (fs_lookup fs p); [apply t_alt2_has_nil_l|]; apply t_emit_has_nil.
Qed.

Section Top.
  (* [comment removed for export] *)
  Variable P_main : word -> word -> word -> EntryDraw -> ProcInput -> config -> Prop.
  Hypothesis STARTUP :
    forall (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (T : TSet),
      valid_sp sp0 -> valid_brk asegs brk0 -> valid_mmap_base mbase ->
      valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> entry_stack_fits sp0 (in_argv inp) (in_envp inp) ->
      valid_id (in_uid inp) -> valid_hwcap (in_hwcap inp) ->
      T [] ->
      (forall c, P_main sp0 brk0 mbase rdraw inp c -> realizes asegs c T) ->
      srealizes asegs (init_config asegs AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp0 brk0 mbase rdraw target_alloc_limit inp) T.
  (* [comment removed for export] *)
  Variable L : alib.
  (* [comment removed for export] *)
  Hypothesis INSTANCE : as_instance_stmt P_main L.
  (* [comment removed for export] *)
  Hypothesis L_OK : forall (HCEIL : HeapCeil), alib_ok L.
  Hypothesis FZ_a : forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_x H -> ainst_facts H -> fuzz_stmt H L.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis TR : forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps H -> asan_driver_laws H -> alib_ok L -> fuzz_stmt H L ->
      as_target_run_stmt H L.
  Hypothesis MAIN : forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps H -> asan_driver_laws H -> as_target_run_stmt H L ->
      (ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H) -> as_main_realizes_stmt H L.

  Theorem as_realizes_spec :
    forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
      valid_sp sp -> valid_brk asegs brk -> valid_mmap_base mbase ->
      entry_stack_fits sp (in_argv inp) (in_envp inp) ->
      valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> valid_creds inp -> valid_hwcap (in_hwcap inp) ->
      srealizes asegs (init_config asegs AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
                (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hva Hve Hfs [Huid _] Hhw.
    apply STARTUP; try assumption; [apply spec_has_nil|].
    intros c PM. destruct (INSTANCE sp brk mbase rnd inp c PM) as (HC & H & s0 & regs & mem & B & tid & can & HHx & TM & DL & LIVE & PRE & EFS).
    pose proof (proj1 HHx) as HH.
    destruct c as [msF mo]. cbn [cfg_ms cfg_model] in PRE, EFS. rewrite <- EFS.
    apply (MAIN HC H HH DL (TR HC H HH DL (L_OK HC) (FZ_a HC H HHx TM)) LIVE sp (in_argv inp) s0 msF mo regs mem B tid can Hva);
      [rewrite EFS; exact Hfs | exact PRE].
  Qed.
End Top.
