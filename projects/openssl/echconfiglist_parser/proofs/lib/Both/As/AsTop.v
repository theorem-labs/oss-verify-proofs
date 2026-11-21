(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the top theorems of Section Top take the channel-reader and launch premises of Run.valid_input and Run.valid_entry, and the library as a function of the heap-ceiling record, L : HeapCeil -> alib, since its state carries the resolved vdso_func value hvdso); the top realizes the spec over the run's segment list run_segments asegs inp sp mbase from the run's own start, because the target calls time() and enters the launch's vDSO pair: STARTUP is as_chain_run's shape, with the main entry's continuation over asegs ++ vdso_segments (in_kernel inp) sp mbase from that list's read-only backing, and TR and MAIN take the run's driver laws over the tail RunTail.run_tail_of (in_kernel inp) sp mbase and, for MAIN, the three tail statements, which the instance now carries. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec ShapeAlg ShapeLaws SpinAlg Scfg Spec HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsIface AsIfaceX AsDriverLaws ECH_Iface AsDrvDefs AsMainPre AsMainTop AsInstance F_time AInstFacts.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomBase RunTail.
Import ListNotations.
Import OSSVerify.Proofs.openssl.echconfiglist_parser.lib.PropExec.
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
      (* 08b1429: [Run.valid_input]'s reader clause, seeding [cs_ok]'s [co_rdr] *)
      in_channel_reader inp = true ->
      (* #38: [Run.valid_input]'s launch clause and [Run.valid_entry]'s fifth conjunct,
         which the start-up invariant is read under ([AsanInit.init_cs_ok]) *)
      valid_launch inp ->
      entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp ->
      T [] ->
      (* the main entry's continuation, over the run's segment list from the configuration with
         that list's read-only backing ([Both/AsHole/EAsChainRun.as_chain_run]'s [MAINR]) *)
      (forall c, P_main sp0 brk0 mbase rdraw inp c ->
         realizes (asegs ++ vdso_segments (in_kernel inp) sp0 mbase)
           (RomBase.cwrom c (seg_rom (asegs ++ vdso_segments (in_kernel inp) sp0 mbase))) T) ->
      realizes (run_segments asegs inp sp0 mbase)
        (init_config (run_segments asegs inp sp0 mbase) AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp0 brk0 mbase rdraw target_alloc_limit inp) T.
  (* [comment removed for export] *)
  Variable L : HeapCeil -> alib.
  (* [comment removed for export] *)
  Hypothesis INSTANCE : as_instance_stmt P_main L.
  (* [comment removed for export] *)
  Hypothesis L_OK : forall (HCEIL : HeapCeil), alib_ok (L HCEIL).
  Hypothesis FZ_a : forall (HCEIL : HeapCeil) (H : asr), asan_rt_hyps_x H -> ainst_facts H -> fuzz_stmt H (L HCEIL).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis TR : forall (HCEIL : HeapCeil) (RT : RunTail.RunTail) (H : asr) (vlo vb vhi : Z),
      asan_rt_hyps H -> asan_driver_laws_run (@RunTail.rt_tail RT) vlo vb vhi H ->
      alib_ok (L HCEIL) -> fuzz_stmt H (L HCEIL) ->
      as_target_run_stmt H (L HCEIL).
  (* the main phase takes the three tail statements at the instance: at the run instance
     [AsSRRun.KHr] they are [Both/As/AsTailsRun.v]'s lifts, not [AsMainTails]' *)
  Hypothesis MAIN : forall (HCEIL : HeapCeil) (RT : RunTail.RunTail) (H : asr) (vlo vb vhi : Z),
      asan_rt_hyps H -> asan_driver_laws_run (@RunTail.rt_tail RT) vlo vb vhi H -> as_target_run_stmt H (L HCEIL) ->
      (ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H) ->
      atail_usage_stmt H (L HCEIL) -> atail_open_stmt H (L HCEIL) -> atail_rderr_stmt H (L HCEIL) ->
      as_main_realizes_stmt H (L HCEIL).

  Theorem as_realizes_spec :
    forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
      valid_sp sp -> valid_brk asegs brk -> valid_mmap_base mbase ->
      entry_stack_fits sp (in_argv inp) (in_envp inp) ->
      valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> valid_creds inp -> valid_hwcap (in_hwcap inp) ->
      in_channel_reader inp = true ->
      valid_launch inp ->
      entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp ->
      realizes (run_segments asegs inp sp mbase)
               (init_config (run_segments asegs inp sp mbase) AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
               (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hva Hve Hfs [Huid _] Hhw Hrdr Hlaunch Hlau.
    apply STARTUP; try assumption; [apply spec_has_nil|].
    intros c PM.
    destruct (INSTANCE sp brk mbase rnd inp c PM)
      as (HC & H & vlo & vb & vhi & s0 & regs & mem & B & tid & can & HHx & TM & DLR & LIVE & (TUS & TOP & TRD) & PRE & EFS).
    pose proof (proj1 HHx) as HH.
    (* the run's tail is the launch's vDSO pair, the list the main phase walks over
       ([Common/Cfg/RunTail.run_tail_of]), as RefTop's [ref_realizes_spec_lim] binds it *)
    pose (RT := RunTail.run_tail_of (in_kernel inp) sp mbase).
    change (vdso_segments (in_kernel inp) sp mbase) with (@RunTail.rt_tail RT) in DLR |- *.
    destruct c as [msF mo]. cbn [cfg_ms cfg_model] in PRE, EFS. rewrite <- EFS.
    apply (MAIN HC RT H vlo vb vhi HH DLR
             (TR HC RT H vlo vb vhi HH DLR (L_OK HC) (FZ_a HC H HHx TM)) LIVE TUS TOP TRD
             sp (in_argv inp) s0 msF mo regs mem B tid can Hva);
      [rewrite EFS; exact Hfs | exact PRE].
  Qed.
End Top.
