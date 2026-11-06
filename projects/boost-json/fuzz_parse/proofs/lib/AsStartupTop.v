(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec ShapeAlg SpinAlg Scfg AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit
  AsImages AsPlanImages AsHSTab AsStartup AsStartupPlan AsStartupHS1 AsStartupHSC AsStartupHSA AsStartupHSF AsStartupCerts AsMainState.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~03acs37Corelib4Init5Logick32eq37Corelib4Init9Datatypeslc4Somelc3natlc6option37Corelib7Numbers7BinNumsoa1Z69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsMainState~~~~~~q76A_MAIN69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsStartupHSF~~~~~~ue8HSF_asan02pc3h5LinuxProcessSemanticsfLinuxProcessSem5Statehjc7in_argvhjc7in_envphjc8in_hwcaphjc6in_uid69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsPlanImages~~~~~~hp63APHhjc5in_fs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsImages~~~~~~hu56ASAN_Hhp65ASEGS69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9AsStartup~~~~~~ij35HOLES69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanInit~~~~~~in85LIMITin85SINV0in85argH079OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~iseaholes_stmt69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ji03fx069OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~jm2dhunspell_scfgoa4Npos35stdpp9bitvectorbdefinitionsjr12bvlc3nil3h5LinuxProcessSemanticsfLinuxProcessSem3Runjta6configjtah0entry_stack_fitsjtabinit_configjtaavalid_argvjta9valid_brkjtaavalid_envpjtabvalid_hwcapjta8valid_idjtafvalid_mmap_basejta8valid_sp3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutkp79EntryDrawhjc9ProcInputhjc5eventq76P_main69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~kv74TSetkv78realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SpinAlg~~~~~~lk69srealizes69OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~lod7init_pchjch2target_alloc_limit" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Existing Instance fx0.

(* [comment removed for export] *)
Lemma HSF_asan_pc_main : ltac2:(zQ "90!je!l7!n4!nb!o1!q3!u5!hid!hj8>1h$3>2ch$0>0@3$1@1$4$0@1$7^2@2$2$0^1@3$1$5@1$8^2$6").
Proof. exact HSF_asan_pc. Qed.

Section Top.
  Variables sp0 brk0 mbase : word.
  Variable rdraw : ltac2:(zQ "10!ksb$0").
  Variable inp : ltac2:(zQ "10!kt8$0").
  Hypothesis Hsp : ltac2:(zQ "10!kob@1$0?3sp0").
  Hypothesis Hbrk : ltac2:(zQ "20!kk2!iia@2$0$1?4brk0").
  Hypothesis Hmb : ltac2:(zQ "10!kn8@1$0?5mbase").
  Hypothesis Hva : ltac2:(zQ "20!kj4!hma@1$0@1$1?3inp").
  Hypothesis Hve : ltac2:(zQ "20!kkf!hn5@1$0@1$1?3inp").
  Hypothesis Hfit : ltac2:(zQ "30!kh0!hma!hn5@3$0?3sp0@1$1?3inp@1$2?3inp").
  Hypothesis Huid : ltac2:(zQ "20!kmc!hoc@1$0@1$1?3inp").
  Hypothesis Hhw : ltac2:(zQ "20!kld!ho0@1$0@1$1?3inp").

  Variable T : ltac2:(zQ "10!lj2$0").
  Hypothesis T_nil : T [].
  Hypothesis MAIN : ltac2:(zQ "50!kg6!kue!iia!jp9!lja>1c$0>0@6$1?3sp0?4brk0?5mbase?5rdraw?3inp^1@4$4$2$3^2?1T").

  Lemma holes_ok : ltac2:(zQ "h00!hma!hn5!ho0!hoc!ht5!htc!ii0!iia!imf!hid!ir3!irc!is5!jh2!jlb!jp9@a$d$e$7$f$6$a$9@8$b$4?3sp0?5rdraw?4brk0@1$0?3inp@1$1?3inp@1$3?3inp@1$2?3inp@7$c$4?3sp0?5rdraw@1$0?3inp@1$1?3inp@1$3?3inp@1$2?3inp@1$8?1T@1$5?3inp").
  Proof.
    intros h ch Hh E R FULL model HC. unfold AsStartup.HOLES.
    apply srealizes_of_realizes. rewrite (HSF_asan_pc_main h ch Hh). apply MAIN.
    split; [exact (conj Hsp (conj Hbrk (conj Hmb (conj Hva (conj Hve (conj Hfit (conj Huid Hhw)))))))|].
    nexists h, ch, E, R, FULL, model. split; [exact Hh|]. split; [exact (HSF_asan_pc_main h ch Hh)|]. split; [reflexivity | exact HC].
  Qed.
End Top.

Theorem as_startup_srealizes : ltac2:(zQ "hd0!iia!jqa!jse!hma!hn5!jp9!jt4!kg6!kh0!ki5!kj4!kk2!kkf!kld!kmc!kn8!kob!ksb!kt8!ku5!ho0!hoc!kue!ht5!ir3!lj2!lja!lo0!ls2>3sp0@1$2@1$1#k0>4brk0@1$2@1$1#k0>5mbase@1$2@1$1#k0>5rdraw$h1>3inp$h2>1T$h9>0@1$h0^6>0@2$b$0^6>0@1$f^6>0@1$a@1$3^5>0@1$c@1$4^6>0@3$8^b@1$3^7@1$4^7>0@1$e@1$h5^8>0@1$d@1$h4^9>0@1^9@1$6$h3>0>1c$7>0@6$h6^h0^f^e^d^c^1@4$ha$0$5^2^c@4$hb$0$5@9$9$0$hc$h7^h0^f^e^d$h8^c^b").
Proof.
  (* [comment removed for export] *)
  intros sp0 brk0 mbase rdraw [argv envp fs stdin uid gid groups net nofile sigmask hw abterm vasz urnd tmp] T Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw T_nil MAIN.
  exact (as_startup_T sp0 rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw
           (in_fs (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw abterm vasz urnd tmp)) eq_refl
           startup_plan_xranges HS1_asan HSC_asan HSA_asan HSF_asan startup_plan AsStartupCert1.startup_shape   (* [comment removed for export] *)
           CERT_KC0 CERT_BFUEL CERT_FUEL AsStartupCert1.startup_cert AsStartupCert1.startup_shape_holes cert2 cert3 cert4
           T T_nil
           (holes_ok sp0 brk0 mbase rdraw (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw abterm vasz urnd tmp)
                     Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw T MAIN)).
Qed.

(* [comment removed for export] *)
Lemma LIMIT_eq : ltac2:(zQ "40!l7!q3!lsd!ir3@3$0$1$3$2").
Proof. reflexivity. Qed.
