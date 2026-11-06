(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec ShapeAlg ShapeLaws SpinAlg Scfg Spec HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import FP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsIface AsDriverLaws AsDrvDefs Fuzz_stmt AsMainPre AsTargetRun AsMainTop AsInstance
  N6_iface AsMainTails.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nil37Corelib7Numbers7BinNumsi34Npos3h5LinuxProcessSemanticsfLinuxProcessSem2Fsk32Fs3h5LinuxProcessSemanticsfLinuxProcessSem5Staten35event69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~q94spec35stdpp9bitvectorbdefinitionsu72bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib2FP~~~~~~hg94frm069OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hka6fp_csrhka3fx0n37in_argv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~hq05asegsn37in_envpn35in_fsk38valid_fs3h5LinuxProcessSemanticsfLinuxProcessSem3Runig1h0entry_stack_fitsig1binit_configig1avalid_argvig19valid_brkig1bvalid_credsig1avalid_envpig1bvalid_hwcapig1fvalid_mmap_baseig18valid_sp3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutir79EntryDrawn39ProcInputn38in_hwcapn3h2target_alloc_limit69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~ji5dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SpinAlg~~~~~~jmd9srealizes69OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~jr47init_pcjr45phdrsig16configig18valid_idn36in_uid69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~khc4TSetkhc8realizes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsInstance~~~~~~kmbh0as_instance_stmt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~ks0casan_rt_hypsks03asr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9Fuzz_stmt~~~~~~lh49fuzz_stmt69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~lm08HeapCeil" s.   (* [comment removed for export] *)
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
  Variable P_main : ltac2:(zQ "50!jc!hg4!jvd!iub!iv8>0@1$1@1$0#k0>0@1$1@1$0#k0>0@1$1@1$0#k0>0$3>0$4>0$2P").
  Hypothesis STARTUP : ltac2:(zQ "hc0!htb!jc!hg4!hp6!hu4!jlc!he!jvd!iid!ik2!il1!ilf!inb!io9!kg7!ip8!iqb!iub!iv8!q1!jg4!kh3!jgf!kl7!klf!jq7!ju9!jv4>3sp0@1$2@1$1#k0>4brk0@1$2@1$1#k0>5mbase@1$2@1$1#k0>5rdraw$h1>3inp$h2>1T$h7>0@1$h0^6>0@2$b$0^6>0@1$f^6>0@1$a@1$3^5>0@1$c@1$4^6>0@3$8^b@1$3^7@1$4^7>0@1$e@1$h5^8>0@1$d@1$h4^9>0@1^9@1$6$h3>0>1c$7>0@6?6P_main^h0^f^e^d^c^1@4$h8$0$5^2^c@4$h9$0$5@9$9$0$ha$hb^h0^f^e^d$h6^c^b").
  (* [comment removed for export] *)
  Hypothesis INSTANCE : ltac2:(zQ "20!kqb!hof@2$0$1?6P_main").
  (* [comment removed for export] *)
  Hypothesis FUZZ : ltac2:(zQ "40!kvd!lgd!ll3!lpb>2HC$3>1H$1>0@2$0^2^1@2$2^3^2").

  Theorem as_realizes_spec : ltac2:(zQ "h90!jc!hp6!htb!hg4!hu4!hue!hv6!iid!ik2!il1!ilf!imc!inb!io9!ip8!iqb!iub!iv8!jg4!jgf!jlc!u0!jq7!ju9!jv4>2sp@1$3@1$0#k0>3brk@1$3@1$0#k0>5mbase@1$3@1$0#k0>3rnd$h0>3inp$h1>0@1$f^5>0@2$a$2^5>0@1$e^5>0@3$7^8@1$1^4@1$4^4>0@1$9@1$1^5>0@1$c@1$4^6>0@1$6@1$5^7>0@1$b^8>0@1$d@1$h2^9@4$h6$2$h4@9$8$2$h7$h8^e^d^c^b$h3^a@2$h5@1$1^a@1$5^a").
  Proof.
    intros sp brk mbase rnd inp Hsp Hbrk Hmb Hfit Hva Hve Hfs [Huid _] Hhw.
    apply STARTUP; try assumption; [apply spec_has_nil|].
    intros c PM. ndestruct (INSTANCE sp brk mbase rnd inp c PM) as (HC & H & s0 & regs & mem & B & tid & can & HH & DL & LIVE & PRE & EFS).
    destruct c as [msF mo]. cbn [cfg_ms cfg_model] in PRE, EFS. rewrite <- EFS.
    apply (as_main_realizes H HH DL (@memcpy_icpt_ok HC) (as_target_run H HH DL (@memcpy_icpt_ok HC) (FUZZ HC H HH)) LIVE
             (atail_usage H DL) (atail_open H DL) (atail_rderr H DL) frm0_fx0 sp (in_argv inp) s0 msF mo regs mem B tid can Hva);
      [rewrite EFS; exact Hfs | exact PRE].
  Qed.
End Top.
