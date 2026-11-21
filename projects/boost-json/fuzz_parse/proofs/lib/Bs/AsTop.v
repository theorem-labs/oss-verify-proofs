(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: statements written out as text, the launch facts valid_launch, entry_launch_ok_va and the channel reader. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec ShapeAlg ShapeLaws SpinAlg Scfg Spec HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import FP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsIface AsDriverLaws AsDrvDefs Fuzz_stmt AsMainPre AsTargetRun AsMainTop AsInstance
  N6_iface AsMainTails.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nil37Corelib7Numbers7BinNumsi34Npos3h5LinuxProcessSemanticsfLinuxProcessSem2Fsk32Fs3h5LinuxProcessSemanticsfLinuxProcessSem5Staten35event69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~q94spec35stdpp9bitvectorbdefinitionsu72bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib2FP~~~~~~hg94frm069OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hka6fp_csrhka3fx0n37in_argv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~hq05asegsn37in_envpn35in_fsk38valid_fs3h5LinuxProcessSemanticsfLinuxProcessSem3Runig1h0entry_stack_fitsig1binit_configig1avalid_argvig19valid_brkig1bvalid_credsig1avalid_envpig1bvalid_hwcapig1fvalid_mmap_baseig18valid_sp3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutir79EntryDrawn39ProcInputn38in_hwcapn3h2target_alloc_limit69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~ji5dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SpinAlg~~~~~~jmd9srealizes69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~jr47init_pcjr45phdrsig16configig18valid_idn36in_uid69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~ki14TSetki18realizes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsInstance~~~~~~kn0h0as_instance_stmt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~ks5casan_rt_hypsks53asr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9Fuzz_stmt~~~~~~lh99fuzz_stmt69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~lm58HeapCeil" s.   (* [comment removed for export] *)
Import ListNotations.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Local Existing Instance fx0.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma spec_has_nil : ltac2:(zQ "70!h8!he!jc!me!q1!u0!hg4>4argv@1$0@1$0@1$6@1$2#8>2fs$3@3$5^2^1@1$1$4").
Proof.
  intros argv fs. unfold spec.
  destruct argv as [|a0 [|p [|x l]]]; try (apply t_emit_has_nil).
  destruct (4096 <=? length p)%nat; [apply t_emit_has_nil|].
  destruct (list_byte_eqb p []); [apply t_emit_has_nil|].
  destruct (list_byte_eqb p dot_path); [apply t_alt2_has_nil_l; apply t_emit_has_nil|].
  destruct (fs_lookup fs p); [apply t_alt2_has_nil_l|]; apply t_emit_has_nil.
Qed.

(* [comment removed for export] *)
Lemma frm0_fx0 : ltac2:(zQ "30!hk2!ho5!hof@1$0@1$1$2").
Proof. reflexivity. Qed.

Section Top.
  (* [comment removed for export] *)
  Variable P_main : ltac2:(zQ "50!jc!hg4!kg2!iub!iv8>0@1$1@1$0#k0>0@1$1@1$0#k0>0@1$1@1$0#k0>0$3>0$4>0$2P").
  (* LPS 727298f3 port: written out (a CDef statement is never re-encoded), with the three
     launch facts [BsStartupTop.as_startup_srealizes] takes at the revision: [valid_launch],
     [entry_launch_ok_va] and the channel reader.  The rest is the decoded old statement. *)
  Hypothesis STARTUP : forall (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (T : TSet),
    valid_sp sp0 -> valid_brk asegs brk0 -> valid_mmap_base mbase ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> entry_stack_fits sp0 (in_argv inp) (in_envp inp) ->
    valid_id (in_uid inp) -> valid_hwcap (in_hwcap inp) ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp -> in_channel_reader inp = true ->
    T [] -> (forall c : config, P_main sp0 brk0 mbase rdraw inp c -> realizes asegs c T) ->
    srealizes asegs (init_config asegs AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp0 brk0 mbase rdraw target_alloc_limit inp) T.
  (* [comment removed for export] *)
  Hypothesis INSTANCE : ltac2:(zQ "20!kr0!hof@2$0$1?6P_main").
  (* [comment removed for export] *)
  Hypothesis FUZZ : ltac2:(zQ "40!lg2!lh2!ll8!lq0>2HC$3>1H$1>0@2$0^2^1@2$2^3^2").

  (* LPS 727298f3 port: written out, with the launch facts [STARTUP] passes on. *)
  Theorem as_realizes_spec : forall (sp brk mbase : word) (rnd : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk asegs brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    valid_creds inp -> valid_hwcap (in_hwcap inp) ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) inp -> in_channel_reader inp = true ->
    srealizes asegs (init_config asegs AsanUbsan.M.init_pc AsanUbsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).
  Proof.
    intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hva Hve Hfs [Huid _] Hhw Hvl Hlau Hrdr.
    apply STARTUP; try assumption; [apply spec_has_nil|].
    intros c PM. ndestruct (INSTANCE sp brk mbase rnd inp c PM) as (HC & H & s0 & regs & mem & B & tid & can & HH & DL & LIVE & PRE & EFS).
    destruct c as [msF mo]. cbn [cfg_ms cfg_model] in PRE, EFS. rewrite <- EFS.
    apply (as_main_realizes H HH DL (@memcpy_icpt_ok HC) (as_target_run H HH DL (@memcpy_icpt_ok HC) (FUZZ HC H HH)) LIVE
             (atail_usage H DL) (atail_open H DL) (atail_rderr H DL) frm0_fx0 sp (in_argv inp) s0 msF mo regs mem B tid can Hva);
      [rewrite EFS; exact Hfs | exact PRE].
  Qed.
End Top.
