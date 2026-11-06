(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec ShapeAlg SpinAlg Scfg AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit
  BothImages BothPlanImages AsHSTab BsStartup BsStartupPlan BsStartupHS1 BsStartupHSC BsStartupHSA BsStartupHSF BsStartupCerts BsMainState.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~03acs37Corelib4Init5Logick32eq37Corelib4Init9Datatypeslc4Somelc3natlc6option37Corelib7Numbers7BinNumsoa1Z02pc69OSSVerify6Proofsaboost_jsonafuzz_parse3libbBsMainState~~~~~~qb6A_MAIN69OSSVerify6Proofsaboost_jsonafuzz_parse3libcBsStartupHSF~~~~~~v28HSF_asan3h5LinuxProcessSemanticsfLinuxProcessSem5Statehjc7in_argvhjc7in_envphjc8in_hwcaphjc6in_uid69OSSVerify6Proofsaboost_jsonafuzz_parse3libeBothPlanImages~~~~~~hp63APHhjc5in_fs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanInit~~~~~~hu75LIMIThu75SINV0hu75argH079OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~ijdaholes_stmt69OSSVerify6Proofsaboost_jsonafuzz_parse3libaBothImages~~~~~~iof6BOTH_Hhp65ASEGS69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9BsStartup~~~~~~itf5HOLES69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ji43fx069OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~jm6dhunspell_scfgoa4Npos35stdpp9bitvectorbdefinitionsjr52bvlc3nil3h5LinuxProcessSemanticsfLinuxProcessSem3Runjte6configjteh0entry_stack_fitsjtebinit_configjteavalid_argvjte9valid_brkjteavalid_envpjtebvalid_hwcapjte8valid_idjtefvalid_mmap_basejte8valid_sp3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutkpb9EntryDrawhjc9ProcInputhjc5eventqb6P_main69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~kvb4TSetkvb8realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SpinAlg~~~~~~lka9srealizes69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~lp17init_pchjch2target_alloc_limit" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Existing Instance fx0.

(* [comment removed for export] *)
Lemma HSF_asan_pc_main : ltac2:(zQ "90!je!l7!n4!nb!o1!q3!q7!u9!hj1>1h$3>2ch$0>0@3$1@1$4$0@1$8^2@2$2$0^1@3$1$5@1$6^2$7").
Proof. exact HSF_asan_pc. Qed.

Section Top.
  Variables sp0 brk0 mbase : word.
  Variable rdraw : ltac2:(zQ "10!ksf$0").
  Variable inp : ltac2:(zQ "10!ktc$0").
  Hypothesis Hsp : ltac2:(zQ "10!kof@1$0?3sp0").
  Hypothesis Hbrk : ltac2:(zQ "20!kk6!it6@2$0$1?4brk0").
  Hypothesis Hmb : ltac2:(zQ "10!knc@1$0?5mbase").
  Hypothesis Hva : ltac2:(zQ "20!kj8!hma@1$0@1$1?3inp").
  Hypothesis Hve : ltac2:(zQ "20!kl3!hn5@1$0@1$1?3inp").
  Hypothesis Hfit : ltac2:(zQ "30!kh4!hma!hn5@3$0?3sp0@1$1?3inp@1$2?3inp").
  Hypothesis Huid : ltac2:(zQ "20!kn0!hoc@1$0@1$1?3inp").
  Hypothesis Hhw : ltac2:(zQ "20!km1!ho0@1$0@1$1?3inp").

  Variable T : ltac2:(zQ "10!lj6$0").
  Hypothesis T_nil : T [].
  Hypothesis MAIN : ltac2:(zQ "50!kga!it6!kv2!jpd!lje>1c$0>0@6$2?3sp0?4brk0?5mbase?5rdraw?3inp^1@4$4$1$3^2?1T").

  Lemma holes_ok : ltac2:(zQ "h00!hma!hn5!ho0!hoc!ht7!hte!ii2!iib!ij4!io1!isc!it6!jhb!hj1!jlf!jpd@a$9$e$b$f$a$6$d@8$7$4?3sp0?5rdraw?4brk0@1$0?3inp@1$1?3inp@1$3?3inp@1$2?3inp@7$8$4?3sp0?5rdraw@1$0?3inp@1$1?3inp@1$3?3inp@1$2?3inp@1$c?1T@1$5?3inp").
  Proof.
    intros h ch Hh E R FULL model HC. unfold BsStartup.HOLES.
    apply srealizes_of_realizes. rewrite (HSF_asan_pc_main h ch Hh). apply MAIN.
    split; [exact (conj Hsp (conj Hbrk (conj Hmb (conj Hva (conj Hve (conj Hfit (conj Huid Hhw)))))))|].
    nexists h, ch, E, R, FULL, model. split; [exact Hh|]. split; [exact (HSF_asan_pc_main h ch Hh)|]. split; [reflexivity | exact HC].
  Qed.
End Top.

Theorem as_startup_srealizes : ltac2:(zQ "hd0!it6!jqe!jt2!hma!hn5!jpd!jt8!kga!kh4!ki9!kj8!kk6!kl3!km1!kn0!knc!kof!ksf!ktc!ku9!ho0!hoc!ii2!ht7!kv2!lj6!lje!lo4!lsb>3sp0@1$2@1$1#k0>4brk0@1$2@1$1#k0>5mbase@1$2@1$1#k0>5rdraw$h1>3inp$h2>1T$h9>0@1$h0^6>0@2$b$0^6>0@1$f^6>0@1$a@1$3^5>0@1$c@1$4^6>0@3$8^b@1$3^7@1$4^7>0@1$e@1$h5^8>0@1$d@1$h4^9>0@1^9@1$6$h3>0>1c$7>0@6$h8^h0^f^e^d^c^1@4$ha$0$5^2^c@4$hb$0$5@9$9$0$hc$h7^h0^f^e^d$h6^c^b").
Proof.
  (* [comment removed for export] *)
  intros sp0 brk0 mbase rdraw [argv envp fs stdin uid gid groups net nofile sigmask hw abterm vasz urnd tmp] T Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw T_nil MAIN.
  exact (as_startup_T sp0 rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abterm vasz urnd tmp Hsp Hbrk Hva Hve Hfit Huid Hhw
           (in_fs (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw abterm vasz urnd tmp)) eq_refl
           startup_plan_xranges HS1_asan HSC_asan HSA_asan HSF_asan startup_plan BsStartupCert1.startup_shape   (* [comment removed for export] *)
           CERT_KC0 CERT_BFUEL CERT_FUEL BsStartupCert1.startup_cert BsStartupCert1.startup_shape_holes cert2 cert3 cert4
           T T_nil
           (holes_ok sp0 brk0 mbase rdraw (mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw abterm vasz urnd tmp)
                     Hsp Hbrk Hmb Hva Hve Hfit Huid Hhw T MAIN)).
Qed.

(* [comment removed for export] *)
Lemma LIMIT_eq : ltac2:(zQ "40!l7!q3!lt6!ii2@3$0$1$3$2").
Proof. reflexivity. Qed.
