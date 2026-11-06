(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg SpinAlg Nodes StoreOk AgentLib AgentNodes AllocNodes
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra RelSpec AsanRelSpec AsanNodesChk Scfg AsanCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick12eq37Corelib4Init9Datatypesla6optionla4Nonela4listla3natla4prod3h5LinuxProcessSemanticsfLinuxProcessSem3Runp65mkCfgp69sys_input3h5LinuxProcessSemanticsfLinuxProcessSem5Statet65Modelt6dSyscallEffectt68m_halted69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~hi78the_scfgla4Somela3nilk13not3h5LinuxProcessSemanticsfLinuxProcessSem5Monadhnd2Ok3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshr1dmachine_statehr1ems_svc_pendingp65SNextp6h0advance_past_svcp6capply_effectp6h4spurious_refusal_cfgp69sstep_cfg3h5LinuxProcessSemanticsfLinuxProcessSem5Specsilacsyscall_spect65eventt6h7syscall_effect_accessesk13andk12exhnd9Unmodeled69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanAcct~~~~~~it37node_okhnd7outcomek13iffla4unit69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7SpinAlg~~~~~~jj19srealizes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~jn84TSetp66configjn85t_alt5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm4Mmapjsdh0forget_vm_ranges69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AllocSim~~~~~~kh69brk_modelhr1daccess_reportla4boolla4truek11Ihr19MachineOkhr1afetch_wordhr18is_ecallhr1emachine_resulthr1dmemory_accesshr1emkAccessReporthr1dstep_accesses3h5LinuxProcessSemantics5Riscv7Preludekue5bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3libaAgentNodes~~~~~~lhd5epend69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~lm34getrlm34mksthf2BVhf4BvWf01Zhr16ms_gpr46Stdlib6ZArith6BinInt1Zls72lthf7Z_to_bvls73powhfbbv_unsignedt6fpage_round_up_Zt69TASK_SIZEt68m_vmmapst67map_hast69page_sizet67vm_maps69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7MmapSim~~~~~~mkdcmunmap_modelmkd6unfilllm36regupdlm36v_addils73addls72lels76modulot66vm_brkt67MemCopyt69mkEffectUjsdabrk_unmapsjsd9brk_zeroskh6h1brk_resolution_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanNodesLibE5Noacc~~~~~~nhc7brk_effnhcbbrk_res_cfg37Corelib4Init6Specifnnc3signnc9proj1_sigt68in_sysnop6dbrk_refusal_bp69refusal_bt6cvm_start_brkla4consla4pairt66VmMapst6cmkVmMapsFullt6avm_init_spt68vm_limitt6cvm_mmap_baset6bvm_noaccesst6bvm_reservedt6bwith_vmmapsjsdbbrk_grow_okmkd5zfillla5false69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsanRefNodes~~~~~~on25tid_I5h5LinuxProcessSemanticsfLinuxProcessSem3Sys6Kernel4Forkorah0PID_MAX_ENVELOPEt65m_tidt68with_tidk12ort64m_fsjn86t_exithf6bv_andjsdh5mmap_fixed_noaccess_bjsdfmmap_fixed_rw_bjsdfmmap_flags_corejsdemmap_modeled_bjsdfmmap_noaccess_bt6dmaps_subtractjsdh2mmap_fixed_rw_nextls73eqbjsdh5with_mmap_replacementnhch1fixedin_ok_vmmapsjsdh3with_mmap_destroyednhch8fixedin_destroyed_vmmapst69alloc_topt69errno_rett6cmap_containst6bregion_freejsdbmmap_errnosjsdh7mmap_fixed_rw_budget_oknhch7fixedin_destroyed_modelnhcefixedin_ok_effnhch0fixedin_ok_model69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7RelSpec~~~~~~qt4cmmap_err_out36Stdlib5Lists4Listrhe2In79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~rj72pc3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypernb7Segmentrj73acsrj7bis_ecall_at79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~rt15two64ls74land" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Noacc.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!o2!rr0@1$0$1").
Context {SC : StepCfg}.

(* [comment removed for export] *)

Lemma sstep_of_check_noacc : ltac2:(zQ "hc0!h9!jc!l5!n2!nb!o2!o9!of!s2!sa!hg4!hgc!hhc!hle!hma!hn1!hn7!hqb!hu8!hv9!igb!ih3!ii7!ij6!ike!io8!ip8!iq0>2ms$h2>5model$a>2x8@1$1@1$0#k0>3eff$b>2m'$a>3evs@1$5$ha>0@3$2@1$3@1$1@1$0#k0@1$c^5@1$4@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#k0@1$h3^7@2$e@1$1@1$0#k0^5>0@3$h9@3$9?4segs^8^6^7@4$h1$b^5^4^3>0@1$h0@4$h7@1$d?2SC@3$9?4segs^9^7^8^6>0@3$2@1$3@1$1@1$0#k0@1$c^6@1$4@1$1@1$0#k0>0@3$2@1$5@2$7@1$1@1$0#k0$6@1$hb^8@1$f@2$7@1$1@1$0#k0$6@5$h8?4segs@1$d?2SC@2$8^c^b^7@1$h4@2$8@1$h5@2$h6^c^9^8").
Proof.
  intros ms model x8 eff m' evs Hh Hsvc Hc Hns Hh' Hacc.
  apply (sstep_cfg_syscall segs the_scfg ms model x8 eff m' m' evs Hh Hsvc).
  - exact Hc.
  - exact Hns.
  - exact Hh'.
  - rewrite Hacc. apply materialize_model_accesses_nil.
Qed.

(* [comment removed for export] *)
Lemma node_chk_ev_noacc : ltac2:(zQ "he0!h9!jc!hgc!l5!sa!o2!hg4!io8!ip8!n2!hn7!hqb!nb!o9!of!irb!s2!ij6!hhc!hle!hma!hn1!is1!is6!hu8!hv9!ih3!ii7!iq0!jge>2ms$h8>5model$6>2x8@1$1@1$0#k0>1IT>4effs>0^1$2>3ms'>0^2$6>3evs>0^3@1$5$8>0@3$3@1$9@1$1@1$0#k0@1$h2^6@1$c@1$1@1$0#k0>0@3$3@1$9@1$1@1$0#k0@1$h9^8@2$h4@1$1@1$0#k0^6>0>1i^6@3$7@3$4?4segs^a^8^9@4$b$2@1^6^1@1^5^1@1^4^1>0>1i^7@1$a@4$h1@1$h3?2SC@3$4?4segs^b^9^a@1^7^1>0>3eff$2>2m'$6>2ev@1$5$8>0@3$7@3$4?4segs^e^c^d@4$b$2^3^2^1>0@1$a@4$h1@1$h3?2SC@3$4?4segs^f^d^e^4@2$h6^d\1i^d@2$f@3$3$2^6@1^d^1@2$f@3$3$6^5@1^c^1@3$3@1$5$8^4@1^b^1>0>3eff$2>2m'$6>2ev@1$5$8>0@3$7@3$4?4segs^f^d^e@4$b$2^3^2^1@3$3@1$9@1$1@1$0#k0@1$h2^3@1$c@1$1@1$0#k0>0@1$a@3$7@3$4?4segs^d^b^c@1$h7$2>0>1i^b@3$3@1$5@2$e@1$1@1$0#k0$d@1$hc@1^b^1@1$h5@2$e@1$1@1$0#k0$d@6$hd?4segs?2SC@2$h0^f^e^c^9\1i^c@2$h0@1$ha@2$hb^h0@1^c^1@1^b^1").
Proof.
  intros ms model x8 I effs ms' evs Hh Hsvc Hok Hnsp Hinv Hnoh Hnu Hacc. split.
  - intros i. apply (sstep_of_check_noacc ms model x8); [exact Hh | exact Hsvc | exact (Hok i) | exact (Hnsp i) | exact (Hnoh _ _ _ (Hok i)) | exact (Hacc i)].
  - intros e st Hss.
    destruct (sstep_cfg_svc_inv segs ms model x8 e st Hsvc Hss)
      as [(eff & model' & ev & Hc & [(m'' & Hh2 & -> & Hns & Hm & ->) | [(Hh2 & -> & Hns & Hm & ->) | [(code & Hh2 & _ & -> & ->) | (sig & Hk & -> & ->)]]])
         | (Hc & -> & ->)].
    + destruct (Hinv _ _ _ Hc Hns) as (i & -> & -> & ->).
      rewrite (Hacc i), materialize_model_accesses_nil in Hm. injection Hm as <-. exists i. split; reflexivity.
    + destruct (Hinv _ _ _ Hc Hns) as (i & -> & -> & ->). rewrite (Hacc i), materialize_model_accesses_nil in Hm. discriminate.
    + rewrite (Hnoh _ _ _ Hc) in Hh2. discriminate.
    + rewrite (m_killed_of_m_halted_none _ (Hnoh _ _ _ Hc)) in Hk. discriminate.
    + exfalso. exact (Hnu Hc).
Qed.

Lemma node_chk_noacc : ltac2:(zQ "he0!h9!jc!hgc!l5!sa!ip8!hg4!o2!hn1!io8!n2!hn7!hqb!nb!o9!of!irb!s2!ij6!hhc!hle!hma!is1!is6!hu8!hv9!ih3!ii7!iq0!jge>2ms$h8>5model$6>2x8@1$1@1$0#k0>1IT>4effs>0^1$2>3ms'>0^2$6>0@3$3@1$a@1$1@1$0#k0@1$h3^5@1$d@1$1@1$0#k0>0@3$3@1$a@1$1@1$0#k0@1$h9^7@2$h5@1$1@1$0#k0^5>0>1i^5@3$9@3$4?4segs^9^7^8@4$c$2@1^5^1@1^4^1@1$8$5>0>1i^6@1$b@4$h2@1$h4?2SC@3$4?4segs^a^8^9@1^6^1>0>3eff$2>2m'$6>3evs@1$7$5>0@3$9@3$4?4segs^d^b^c@4$c$2^3^2^1>0@1$b@4$h2@1$h4?2SC@3$4?4segs^e^c^d^4@2$h6^c\1i^c@2$h0@3$3$2^6@1^c^1@2$h0@3$3$6^5@1^b^1@3$3@1$7$5^4@1$8$5>0>3eff$2>2m'$6>2ev@1$7$5>0@3$9@3$4?4segs^e^c^d@4$c$2^3^2^1@3$3@1$a@1$1@1$0#k0@1$h3^3@1$d@1$1@1$0#k0>0@1$b@3$9@3$4?4segs^c^a^b@1$h7$2>0>1i^a@3$3@1$7@2$f@1$1@1$0#k0$e@1$hc@1^a^1@1$8@2$f@1$1@1$0#k0$e@6$hd?4segs?2SC@2$h1^e^d^b\0^b@1$8$5\1i^b@2$h1@1$ha@2$hb^f@1^b^1@1^a^1").
Proof.
  intros ms model x8 I effs ms' Hh Hsvc Hok Hnsp Hinv Hnoh Hnu Hacc.
  apply (node_chk_ev_noacc ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok); auto.
Qed.

(* [comment removed for export] *)
Lemma node_fam_noacc : ltac2:(zQ "i00!hgc!h9!jc!l5!ip8!hg4!o2!hn1!n2!hn7!hqb!sa!nb!o9!of!irb!jh9!s2!ij6!hhc!hle!hma!is1!ji4!is6!hu8!hv9!ih3!ii7!io8!iq0!jge>2ms$h9>5model$5>2x8@1$2@1$1#k0>1IT>4effs>0^1$0>3ms'>0^2$5>1R>0@1$h0$0P>0@3$3@1$8@1$2@1$1#k0@1$h3^6@1$c@1$2@1$1#k0>0@3$3@1$8@1$2@1$1#k0@1$ha^8@2$h5@1$2@1$1#k0^6>0>1o@1$h0$0@2$h7@3$hd@3$b?4segs^a^8^9^1@1^4^1>0>1i^7@1^5@4$a$0@1^7^1@1^6^1@1$7$4>0>1i^8@1$9@4$h2@1$h4?2SC@3$b?4segs^c^a^b@1^8^1>0>3eff$0>2m'$5>3evs@1$6$4>0@1^9@4$a$0^3^2^1>0@1$9@4$h2@1$h4?2SC@3$b?4segs^h0^e^f^4@2$h6^e\1i^e@2$f@3$3$0^6@1^e^1@2$f@3$3$5^5@1^d^1@3$3@1$6$4^4@1$7$4>0>3eff$0>2m'$5>2ev@1$6$4>0@1^a@4$a$0^3^2^1@3$3@1$8@1$2@1$1#k0@1$h3^3@1$c@1$2@1$1#k0>0@1$9@1^8@1$h8$0>0>1i^c@3$3@1$6@2$e@1$2@1$1#k0$d@1$he@1^c^1@1$7@2$e@1$2@1$1#k0$d@6$hf?4segs?2SC@2$h1^h0^f^d\0^d@1$7$4\1i^d@2$h1@1$hb@2$hc^h1@1^d^1@1^c^1").
Proof.
  intros ms model x8 I effs ms' R Hh Hsvc HR Hin Hns Hout Hnh Hnu Hacc.
  apply (node_chk_noacc ms model x8 I effs ms' Hh Hsvc).
  - intros i. apply HR. apply Hin.
  - exact Hns.
  - intros eff m' ev Hc Hs. apply HR in Hc. exact (Hout _ _ _ Hc Hs).
  - intros eff m' ev Hc. apply HR in Hc. exact (Hnh _ _ _ Hc).
  - intros Hc. apply HR in Hc. exact (Hnu Hc).
  - exact Hacc.
Qed.

(* [comment removed for export] *)
Lemma node_det_noacc : ltac2:(zQ "hf0!h9!jc!l5!hgc!o2!hg4!n2!jia!sa!ip8!nb!o9!of!irb!hn7!s2!io8!hhc!hma!hn1!ji4!hqb!is6!hu8!hv9!ih3!ii7!ij6!iq0!jge!hle>2ms$h7>5model$5>2x8@1$1@1$0#k0>4eff0$3>2m0$5>4evs0@1$4$9>0@3$2@1$6@1$1@1$0#k0@1$h1^5@1$a@1$1@1$0#k0>0@3$2@1$6@1$1@1$0#k0@1$h8^7@2$h2@1$1@1$0#k0^5>0>3eff$3>2m'$5>3evs@1$4$9@2$h4@3$h0@3$8?4segs^b^9^a@4$h5$3^3^2^1@2$d@3$2$3^3^8@2$d@3$2$5^2^7@3$2@1$4$9^1^6>0@1$e@4$hb@1$he?2SC@3$8?4segs^9^7^8^6>0@1$e@3$h0@3$8?4segs^a^8^9@1$h6$3>0@3$2@1$6@1$1@1$0#k0@1$h1^7@1$a@1$1@1$0#k0>0@3$2@1$4@2$c@1$1@1$0#k0$b@1$hc^9@1$h3@2$c@1$1@1$0#k0$b@6$hd?4segs?2SC@2$f^d^c$7\0$7^9\0$7@2$f@1$h9@2$ha^e^b^a").
Proof.
  intros ms model x8 eff0 m0 evs0 Hh Hsvc Hchk Hns Hnu Hh0 Hacc.
  apply (node_chk_ev_noacc ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
  - intros []. apply (proj2 (Hchk eff0 m0 evs0)). auto.
  - intros []. exact Hns.
  - intros eff m' ev Hc _. apply Hchk in Hc as (-> & -> & ->). exists tt. auto.
  - intros eff m' ev Hc. apply Hchk in Hc as (-> & -> & ->). exact Hh0.
  - exact Hnu.
  - intros []; exact Hacc.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_det_noacc : ltac2:(zQ "hf0!h9!jc!l5!hgc!hg4!o2!n2!sa!ip8!nb!o9!hn1!of!irb!hn7!s2!io8!hhc!jmb!hma!ji4!hqb!is6!hu8!hv9!ih3!ii7!ij6!iq0!hle!jr3>2ms$h7>5model$4>2x8@1$1@1$0#k0>4eff0$3>2m0$4>1T$he>0@3$2@1$6@1$1@1$0#k0@1$h1^5@1$9@1$1@1$0#k0>0@3$2@1$6@1$1@1$0#k0@1$h8^7@2$h3@1$1@1$0#k0^5>0>3eff$3>2m'$4>3evs@1$5$8@2$h4@3$h0@3$7?4segs^b^9^a@4$h5$3^3^2^1@2$d@3$2$3^3^8@2$d@3$2$4^2^7@3$2@1$5$8^1@1$b$8>0@1$e@4$hb@1$hd?2SC@3$7?4segs^9^7^8^6>0@1$e@3$h0@3$7?4segs^a^8^9@1$h6$3>0@3$2@1$6@1$1@1$0#k0@1$h1^7@1$9@1$1@1$0#k0>0@3$2@1$5@2$c@1$1@1$0#k0$a@1$hc^9@1$b@2$c@1$1@1$0#k0$a>0@4$h2?4segs?2SC@2$f@1$h9@2$ha^d^a^9^8@4$h2?4segs?2SC@2$f^e^d^9").
Proof.
  intros ms model x8 eff0 m0 T Hh Hsvc Hchk Hns Hnu Hh0 Hacc Hc.
  eapply srz_silent1; [eapply node_det_noacc; eassumption | exact Hc].
Qed.

(* [comment removed for export] *)
Lemma srz_cases : ltac2:(zQ "70!jrb!jmb!hn1!ip8!jge!jr3!js4>1c$0>1IT>2nx>0^1$0>1T>0^2$5>2i0^3>0@6$4?4segs?2SC^5^4\0^4@1$2$3^3>0>1i^5@4$1?4segs?2SC@1^5^1@1^4^1@4$1?4segs?2SC^7@2$6^6^4").
Proof.
  intros c I nx T i0 Hnode Hc.
  apply (srz_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
  - apply (srz_node segs c I (fun _ => []) nx T i0 Hnode Hc).
  - intros tr. split.
    + intros [i Hi]. exists i.
      exact (proj1 (t_emit_nil_eq (T i) (srealizes_nonempty segs _ _ (Hc i)) tr) Hi).
    + intros [i Hi]. exists i.
      exact (proj2 (t_emit_nil_eq (T i) (srealizes_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma forget_vm_ranges_halted : ltac2:(zQ "90!h9!jc!hhc!o2!n2!of!l5!hg4!kg1>6ranges@1$3@2$5@1$1@1$0#k0@1$1@1$0#k0>1m$7@3$6@1$4@1$1@1$0#k0@1$2@2$8^2^1@1$2^1").
Proof.
  induction ranges as [|[a n] r IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. apply vm_forget_range_halted.
Qed.

Lemma brk_model_halted : ltac2:(zQ "70!h9!jc!hhc!n2!l5!hg4!kl1>3req@1$1@1$0#k0>1r@1$1@1$0#k0>1m$5@3$4@1$3@1$1@1$0#k0@1$2@3$6^3^2^1@1$2^1").
Proof.
  intros. unfold brk_model, with_brk_next. cbv zeta.
  rewrite forget_vm_ranges_halted. apply with_vmmaps_halted.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stepacc_ecall_epend : ltac2:(zQ "h81!h9!jc!n2!l5!hu8!kle!hma!kmf!hn1!kn6!knd!ko1!koe!kpc!kq8!kra!ksb!ktd!lh4!lla!lpe!lq6!lqe!lr3&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4regs@2$h2@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>1w@1$1@1$0#i0>0@3$3@1$2@1$1@1$0#i0@2$c?4segs^4@2$6@1$1@1$0#i0^1>0@3$3$7@1$d^2$9@3$3@1$e@1$5$4@2$h1?4segs@5$h5?2fx^7^6^5^4@2$b@1$5$4@3$h0$4@6$h3?2fx^7^6^5^4@2$h4^7@3$h6@1$0#5+h1Kv$a@2$h7@1$0#5+h1@1$8$f").
Proof.
  intros regs pc mem rom w Hfetch Hecall.
  unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkst].
  rewrite Hfetch. cbv beta iota.
  unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. cbv beta iota.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma node_instr_noacc : ltac2:(zQ "h40!hu8!h9!jc!jia!l5!nb!hn1!n2!kle!s2!ko1!kq8!kra!ksb!hv9!ktd!hg4!ip8!hhc!jge>2ms$0>5model$h0>3ms'$0>0@3$4@1$7@1$2@1$1#k0@1$h2^2@1$5@1$2@1$1#k0>0@3$4@1$7@1$2@1$1#k0@1$e^4@1$5@1$2@1$1#k0>0@3$4@1$b@1$8$0@2$f?4segs^5@2$a@1$8$0@3$d$0^3@1$6$c@6$h3?4segs?2SC@2$9^6^5$3\0$3@1$6$h1\0$3@2$9^5^6").
Proof.
  intros ms model ms' Hh Hsvc Hstep.
  assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
  { unfold mi_account_step. rewrite Hstep. cbn [accessed_ranges access_value].
    rewrite materialize_model_accesses_nil. reflexivity. }
  split.
  - intros []. apply (sstep_cfg_instr segs the_scfg ms model ms' model Hh Hsvc Hacc).
  - intros e st Hss. exists tt. apply sstep_cfg_sub in Hss.
    inversion Hss; subst;
      match goal with
      | H : mi_account_step segs ms model = _ |- _ => rewrite Hacc in H; try discriminate; injection H as <- <-; split; reflexivity
      | H : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H; discriminate
      end.
Qed.

(* [comment removed for export] *)
Lemma epend_len : ltac2:(zQ "h25!h9!jc!knd!l5!lpe!lqe!lr3!n2!irb!lra!lrd!lla!ltf!lu5!hn7!lh4!luf!lv6&>0@1$1@1$0#k0@1$7@1$1@1$0#8&@3$5@1$0#5+h1Kv$2@2$6@1$0#5+h1&@2$4^7~1&@6$b?2fx^7^6^5^4~2&@2$a~3N1>4regs@2$f@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>3len$9>0@3$3@1$1@1$0#k0@2$4^5@3$5@1$0#5+bKv$2@2$6@1$0#5+b@2$d@1$0#k0^1>0@2$8@2$cZ^2@2$c^2@2$h0+2+k0@2$8@3$3$9@2$h1@1$0#k0~4^3@1$e@3$3@1$1@1$0#k0~4@2$d@1$0#k0Z").
Proof.
  intros regs pc mem rom len H11 Hlen. rewrite ms_gpr_epend1, H11. split.
  - apply u64_lit. lia.
  - intro Hc. apply (f_equal bv_unsigned) in Hc. rewrite u64_lit in Hc by lia.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hc. lia.
Qed.

(* [comment removed for export] *)

Lemma srz_sys_lazy : ltac2:(zQ "h61!h9!jc!n2!l5!s2!jmb!nb!hma!kmf!kn6!knd!koe!kpc!hg4!hhc!lh4!lla!lpe!lq6!jr3!lqe!lr3&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4regs@2$f@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>5model$d>1w@1$1@1$0#i0>1T$h3>0@3$3@1$2@1$1@1$0#k0@1$e^3@1$6@1$1@1$0#k0>0@3$3@1$2@1$1@1$0#i0@2$b?4segs^7@2$7@1$1@1$0#i0^3>0@3$3$8@1$c^4$9>0@4$5?4segs?2SC@2$4@6$h0?2fx^a^9^8^7@2$h1^a@3$h4@1$0#5+h1Kv$a@2$h5@1$0#5+h1^6^4@4$5?4segs?2SC@2$4@5$h2?2fx^b^a^9^8^7^5").
Proof.
  intros regs pc mem rom model w T Hh HF HE Hc.
  eapply srz_silent1; [| exact Hc].
  apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma srz_munmap_lazy : ltac2:(zQ "i62!h9!jc!l5!lu5!n2!knd!mg4!lqe!lr3!lpe!kmf!kn6!lra!s2!lq6!jmb!lv6!nb!hma!koe!kpc!hg4!mh6!hhc!mi2!mid!mj7!mk3!lh4!mo7!mp7!mq1!mqb!jr3!mr5!mrc!ltf!ms2&>0@1$1@1$0#k0@1$4@1$1@1$0#8&@3$7@1$0#5+aKv$5@2$8@1$0#5+a>4regs@2$hc@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>5model$h5>1w@1$1@1$0#i0>1a@1$1@1$0#k0>3len$c>1K$i1>0@3$2@1$4@1$1@1$0#i0@2$h3?4segs^8@2$h2@1$1@1$0#i0^4>0@3$2$a@1$h4^5$b>0@3$2@1$4@1$1@1$0#k0@1$h7^7@1$h1@1$1@1$0#k0>0@3$2@1$1@1$0#k0@2$9^c@3$7@1$0#5+h1Kv$5@2$8@1$0#5+h1@2$3@1$0#k0+t7>0@3$2@1$1@1$0#k0@2$9^d~1^7>0@3$2$c@2$i5@2$h0@1$0#k0^8$haZ>0@3$2@1$1@1$0#k0@2$9^f@3$7@1$0#5+bKv$5@2$8@1$0#5+b@2$3@1$0#k0^8>0@2$i4Z^9>0@2$i3@2$i2@2$h0@1$0#k0^b@1$6^a$h6>0@3$2$a@3$h9@1$hb@1$h8^e^c@2$3@1$0#k0@1$6^b$b>0@4$f?4segs?2SC@2$d@5$e?2fx@3$hf^h3~1@2$3@1$0#k0Z@2$i0^h2+4@3$he^d@2$3@1$0#k0@1$6^c^h1^h0@3$hd^d@2$3@1$0#k0@1$6^c^f^b@4$f?4segs?2SC@2$d@5$e?2fx^h4^h3^h2^h1^h0^c").
Proof.
  intros regs pc mem rom model w a len K HF HE Hh H17 H10 Hal H11 Hlen Hnw Hhas Hc.
  assert (Hlen' : (len < two_pow_64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE in Hnw. unfold two_pow_64. lia. }
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 215%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
  { unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
  assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
  { unfold page_round_up. rewrite Hu1. reflexivity. }
  assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hargs : munmap_args_ok ms model).
  { unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; try assumption.
    intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
  pose proof (fun o => munmap_outcome_si segs ms (getr regs 17) model o Hno Hargs) as Hsi.
  unfold munmap_eff in Hsi. rewrite H0, Hpr in Hsi.
  eapply (srz_det_noacc ms model (getr regs 17)
            (mkEffectU (Z_to_bv 64 0) [] [] [(a, Z_to_bv 64 (page_round_up_Z len))] [] [])
            (munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model));
    [exact Hh | reflexivity | | | | | reflexivity |].
  - intros eff m' evs. split.
    + intros Hck. apply Hsi in Hck. apply Ok_inj in Hck as (-> & -> & ->). repeat split; reflexivity.
    + (intros nd_i1; ndestruct nd_i1 as (-> & -> & ->)). apply Hsi. reflexivity.
  - (* [comment removed for export] *)
    apply not_spurious_none. rewrite in_sysno_sys_input, Hno. apply injected_arm_none_215.
  - intros Hck. apply Hsi in Hck. exact (Unmodeled_Ok _ _ _ Hck).
  - rewrite munmap_model_halted. exact Hh.
  - unfold ms. rewrite adv_unmaps1_epend. exact Hc.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition brk_eff : ltac2:(zQ "50!h9!hu8!hg4!hgc!jc>2ms$1>5model$2>1r@1$4@1$0#k0$3") := ltac2:(zQ "f0!h9!jc!hn1!of!mi2!msc!o2!o9!hu8!lrd!mt5!hg4!mtf!mub!mv9\2ms$8\5model$b\1r@1$1@1$0#k0@6$c^1@1$2@2$3@1$1@1$0#k0@1$6@1$1@1$0#8@3$e@2$9^3N0^1@1$5@1$4^2@2$d^1@1$5@1$4^2@1$2$a@1$2@2$3@1$1@1$0#k0$7").
Definition brk_res_cfg : ltac2:(zQ "40!h9!jc!hu8!hg4>2ms$2>5model$3>2x8@1$1@1$0#k0>1r@1$1@1$0#k0P") := ltac2:(zQ "c0!h9!jc!irb!hn7!hu8!lrd!ij6!sa!hg4!ng6!nm2!hle\2ms$4\5model$8\2x8@1$1@1$0#k0\1r@1$1@1$0#k0@2$2@3$9^3@2$5^4N0^1@1$3@4$6@1$b?2SC@3$7?4segs^4^2^3@3$a^4^3^1").

(* [comment removed for export] *)
Lemma node_brk_lazy : ltac2:(zQ "h84!h9!jc!nmd!l5!np1!n2!np8!s2!nb!hma!hn1!lra!hu8!lrd!hv9!ih3!ii7!hg4!ip8!hhc!kl1!jge!nm2!lv6&\1r@1$1@1$0#k0@4$2^7^6^5^1&@2$4@1$1@1$0#k0~0&\1r@1$1@1$0#k0@4$2^8^7^6^1&@3$6@1$1@1$0#k0~2^1>2ms$c>5model$h1>2x8@1$1@1$0#k0>0@3$3@1$5@1$1@1$0#k0@1$h3^2@1$8@1$1@1$0#k0>0@3$3@1$5@1$1@1$0#k0@1$e^4@2$9@1$1@1$0#k0^2>0@3$3$b@2$h7@1$0#k0^3+t6@6$h5?4segs?2SC@2$7^6^5~1\0~1@1$a$h2\1i~1@2$7@1$f@2$h0^7@3$h6^7^6~3@3$h4@2$d^7N0~3^6").
Proof.
  intros ms model x8 Hh Hsvc Hno.
  apply (node_chk_noacc ms model x8 {r : word | brk_res_cfg ms model x8 r}
           (fun i => brk_eff ms model (proj1_sig i))
           (fun i => brk_model (ms_gpr ms 0) (proj1_sig i) model) Hh Hsvc).
  - intros [r [Hr Hns0]]. cbn [proj1_sig].
    exact (brk_ok_intro segs ms x8 model r Hno Hr).
  - intros [r [Hr0 Hns]]. exact Hns.
  - intros eff m' evs Hc Hns.
    apply (brk_ok_iff segs ms x8 model eff m' evs Hno) in Hc as (Heff & -> & Hok & ->).
    assert (Hrc : brk_res_cfg ms model x8 (eff_ret eff)) by (split; [exact Hok | unfold brk_eff; rewrite <- Heff; exact Hns]).
    exists (exist _ (eff_ret eff) Hrc). cbn [proj1_sig]. unfold brk_eff. rewrite <- Heff. repeat split; reflexivity.
  - intros eff m' evs Hc.
    apply (brk_ok_iff segs ms x8 model eff m' evs Hno) in Hc as (_ & _ & _ & ->). rewrite brk_model_halted. exact Hh.
  - exact (brk_no_unmodeled segs ms x8 model Hno).
  - intros [r Hr]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_sysno : ltac2:(zQ "80!h9!l5!lra!lv6!hu8!sa!nq5!jc>2ms$4>2x8@1$7@1$0#k0>0@3$1$2@2$3@1$0#k0^1+t6@3$1$2@2$3@1$0#k0@1$6@3$5?4segs^3^2+t6").
Proof. intros ms x8 Hno. rewrite in_sysno_sys_input. exact Hno. Qed.

(* [comment removed for export] *)
Lemma brk_refusal_unfold : ltac2:(zQ "c0!h9!l5!jc!kmf!lra!hu8!lrd!nr0!ns0!sa!hg4!lv6>2ms$5>2x8@1$2@1$0#k0>5model$a>1r@1$2@1$0#k0>0@3$1$4@2$b@1$0#k0^3+t6@3$1$3@3$8@3$9?4segs^5^4^3^2@3$7^3@2$6^5N0^2").
Proof.
  intros ms x8 model r Hno. rewrite (refusal_b_brk _ model r (brk_sysno ms x8 Hno)), in_arg0_sys_input. reflexivity.
Qed.

Lemma srz_brk_query_lazy : ltac2:(zQ "ha2!h9!jc!l5!n2!knd!lqe!lr3!s2!lpe!lq6!jmb!lu5!nb!hma!kmf!kn6!koe!kpc!hg4!hhc!mi2!msc!lh4!mq1!mqb!jr3&>0@1$1@1$0#k0@1$3@1$1@1$0#8&@3$5@1$0#5+aKv$4@2$6@1$0#5+a>4regs@2$h6@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>5model$h2>1w@1$1@1$0#i0>1K$h9>0@3$2@1$3@1$1@1$0#i0@2$h0?4segs^6@2$d@1$1@1$0#i0^2>0@3$2$e@1$h1^3$f>0@3$2@1$3@1$1@1$0#k0@1$h3^5@1$c@1$1@1$0#k0>0@3$2@1$1@1$0#k0@2$8^a@3$5@1$0#5+h1Kv$4@2$6@1$0#5+h1@2$b@1$0#k0+t6>0@3$2@1$1@1$0#k0@2$8^b~1@2$b@1$0#k0Z>0@4$a?4segs?2SC@2$7@5$9?2fx@3$h7^c~1@1$h5@1$h4^8@2$h8^b+4^a^9^8^6@4$a?4segs?2SC@2$7@5$9?2fx^d^c^b^a^9^7").
Proof.
  intros regs pc mem rom model w K HF HE Hh H17 H10 Hc.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps model)).
  { intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
    unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
  assert (Hq : brk_res_cfg ms model (getr regs 17) (vm_brk (m_vmmaps model))).
  { split; [apply Hcases; reflexivity|].
    apply spurious_refusal_not_refusal. cbn [brk_eff eff_ret]. rewrite (brk_refusal_unfold ms _ model _ Hno).
    unfold brk_refusal_b. rewrite H0. unfold w_is0. rewrite bv_eqb_refl. reflexivity. }
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_res_cfg ms model (getr regs 17) r} => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hq); exact Ht]].
  eapply srz_cases; [exact (exist _ _ Hq) | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] |].
  intros [r [Hr Hns']]. cbn [proj1_sig]. unfold brk_eff.
  pose proof (proj1 (Hcases r) Hr) as Er. subst r.
  rewrite H0, brk_zeros_query, brk_unmaps_keep.
  rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
  unfold ms. rewrite adv_ret_epend. exact Hc.
Qed.

(* [comment removed for export] *)
Lemma srz_brk_grow_lazy : ltac2:(zQ "j14!h9!jc!lv6!l5!lu5!mr5!n2!knd!lqe!lr3!lra!s2!lq6!jmb!ltf!kmf!kn6!mj7!nsc!lpe!mq1!mqb!ms2!nb!hma!ntb!nu2!of!koe!kpc!hg4!nu9!hhc!mi2!nv2!msc!og1!oge!mk3!oh9!oi8!oj6!ok4!ol2!lh4!om1!jr3!mrc!luf&>0@1$1@1$0#k0@1$6@1$1@1$0#8&@3$8@1$0#5+aKv$7@2$9@1$0#5+a&@2$4@1$0#k0@2$5@2$2@1$0#k0^9^h0&@2$4@1$0#k0@2$5@2$2@1$0#k0^a^h1>4regs@2$ic@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>5model$he>1w@1$1@1$0#i0>1d$a>1K$ie>0@3$3@1$6@1$1@1$0#i0@2$hc?4segs^7@2$h8@1$1@1$0#i0^3>0@3$3$f@1$hd^4$h0>0@3$3@1$6@1$1@1$0#k0@1$i0^6@1$h7@1$1@1$0#k0>0@3$3@1$1@1$0#k0@2$h3^b@3$8@1$0#5+h1Kv$7@2$9@1$0#5+h1@2$4@1$0#k0+t6=1h$hf@1$i1^8=1b@1$1@1$0#k0@1$i3^1>0@3$3$a@2$h6@2$2@1$0#k0^1$h1Z>0@3$3$a@2$h6^9$h1Z>0@2$eZ^a>0@2$eZ@2$2@1$0#k0^4>0@2$e@2$5@2$2@1$0#k0^5^c@2$j0+2+k0>0@2$if@2$2@1$0#k0@1$h2^7@2$5@2$2@1$0#k0^6^d>0@3$3@1$1@1$0#k0@2$h3^h4~1@2$4@1$0#k0@2$5@2$2@1$0#k0^7^e>0@4$d?4segs?2SC@2$b@5$c?2fx@3$h4^h5~1^8@2$h5^h4+4^h3^h2^h1^e>0>0@3$3$f@3$ib^h2~2~2$h0@4$d?4segs?2SC@2$b@5$c?2fx@3$h4^h7~1~3@2$h5^h6+4@3$id^a@2$4@1$0#k0^h1^h5^h4@2$ia@8$i2@1$i9^b@3$h9@2$hb@1$1@1$0#k0@1$1@1$0#k0@4$ha@1$1@1$0#k0@1$1@1$0#k0^a@2$4@1$0#k0^h1@1$i6^b@1$i8^b@1$h2^b~3@1$i5^b@1$i7^b@1$i4^b^h3^h0@4$d?4segs?2SC@2$b@5$c?2fx^h7^h6^h5^h4^h3^h0").
Proof.
  intros regs pc mem rom model w d K HF HE Hh H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 HA HB.
  pose proof (u64_range b) as Hbr.
  set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
  assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> (r = b \/ (r = req /\ Mmap.brk_grow_ok model req req = true))).
  { intros r. rewrite H0. apply brk_r_ok_grow_cases; fold h; fold b; rewrite ?Hureq; lia. }
  assert (Hneq : req <> b).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E. unfold b in E. lia. }
  (* [comment removed for export] *)
  assert (Hi0 : exists r, brk_res_cfg ms model (getr regs 17) r).
  { destruct (Bool.bool_dec (Mmap.brk_grow_ok model req req) true) as [Hg|Hg]; [|apply Bool.not_true_is_false in Hg].
    - exists req. split; [apply Hcases; right; split; [reflexivity | exact Hg]|].
      apply spurious_refusal_not_refusal. cbn [brk_eff eff_ret]. rewrite (brk_refusal_unfold ms _ model _ Hno).
      unfold brk_refusal_b. rewrite H0. fold h b. rewrite (bv_eqb_neq _ _ Hneq). rewrite !andb_false_r. reflexivity.
    - exists b. split; [apply Hcases; left; reflexivity|].
      (intros nd_i2; ndestruct nd_i2 as (_ & _ & eff' & m' & evs' & Hspec & Hnr)).
      apply (brk_ok_iff segs ms _ model eff' m' evs' Hno) in Hspec as (Heff & _ & Hok & _).
      apply Hcases in Hok as [Hok | [Hok Hg']]; [| rewrite Hg in Hg'; discriminate].
      rewrite (brk_refusal_unfold ms _ model _ Hno) in Hnr. unfold brk_refusal_b in Hnr. rewrite H0, Hok in Hnr.
      fold h b in Hnr. rewrite bv_eqb_refl, (bv_eqb_neq _ _ Hneq) in Hnr.
      assert (E0 : w_is0 req = false).
      { unfold w_is0. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
        change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
      rewrite E0 in Hnr. unfold min_brk in Hnr. fold h in Hnr.
      rewrite (proj2 (Z.ltb_ge _ _)) in Hnr by (rewrite Hureq; lia). discriminate Hnr. }
  destruct Hi0 as [r0 Hr0].
  apply (srz_conseq segs _ (t_alt (fun i : {r : word | brk_res_cfg ms model (getr regs 17) r} => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ r0 Hr0); exact Ht]].
  eapply srz_cases; [exact (exist _ r0 Hr0) | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] |].
  intros [r [Hr Hns']]. cbn [proj1_sig]. unfold brk_eff. fold h.
  destruct (proj1 (Hcases r) Hr) as [-> | [-> Hg]].
  - fold b. rewrite brk_zeros_keep, brk_unmaps_keep.
    unfold b, h. rewrite brk_model_keep.
    unfold ms. rewrite adv_ret_epend. exact HA.
  - assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
    assert (Hreq0 : req <> Z_to_bv 64 0).
    { intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
    rewrite H0. fold b. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
    unfold brk_page_range.
    rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
    rewrite (page_round_up_Z_aligned (bv_unsigned req))
      by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
    rewrite (proj2 (Z.ltb_lt _ _) Hlt).
    replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
    rewrite Hureq. replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
    unfold req, b, h. rewrite (brk_model_grow_eq model d) by assumption.
    unfold ms. rewrite adv_zeros1_epend. apply HB. exact Hg.
Qed.

Lemma srz_brk_grow_blocked_lazy : ltac2:(zQ "i12!h9!jc!l5!lv6!n2!knd!lqe!lr3!kmf!s2!lpe!lq6!jmb!mrc!nb!hma!oma!kn6!koe!kpc!hg4!nu9!hhc!mi2!msc!nsc!ol2!lh4!mq1!mqb!jr3!ltf!lu5&>0@1$1@1$0#k0@1$4@1$1@1$0#8&@3$6@1$0#5+aKv$5@2$7@1$0#5+a>4regs@2$hb@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>5model$h4>1w@1$1@1$0#i0>3req@1$1@1$0#k0>2KA$he>0@3$2@1$4@1$1@1$0#i0@2$h2?4segs^7@2$f@1$1@1$0#i0^3>0@3$2$8@1$h3^4$h1>0@3$2@1$4@1$1@1$0#k0@1$h6^6@1$e@1$1@1$0#k0>0@3$2@1$1@1$0#k0@2$a^b@3$6@1$0#5+h1Kv$5@2$7@1$0#5+h1@2$i0@1$0#k0+t6=1h$h5@1$h7^8=1b@1$1@1$0#k0@1$h8^1>0@3$2@1$1@1$0#k0@2$a^e~1^8>0@2$hfZ@2$3@1$0#k0^9>0@2$d@2$3@1$0#k0@1$h9^4@2$3@1$0#k0^a>0@2$d@2$3@1$0#k0^4@2$3@1$0#k0^b>0@3$2$8@3$ha^e^c^c$h0>0@4$c?4segs?2SC@2$9@5$b?2fx@3$hc^h3~1^6@2$hd^h2+4^h1^h0^f^c@4$c?4segs?2SC@2$9@5$b?2fx^h4^h3^h2^h1^h0^d").
Proof.
  intros regs pc mem rom model w req KA HF HE Hh H17 h b H10 Hpos Hs Hb Hblk HA.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
  assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
  assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = b).
  { intros r. rewrite H0, (brk_r_ok_grow_cases model req r Hpos Hs Hb). fold h. fold b. split.
    - intros [-> | [-> Hg]]; [reflexivity | rewrite Hblk in Hg; discriminate].
    - intros ->. left. reflexivity. }
  assert (Hkeep : brk_res_cfg ms model (getr regs 17) b).
  { split; [apply Hcases; reflexivity|].
    (intros nd_i3; ndestruct nd_i3 as (_ & Hrb & eff' & m' & evs' & Hspec & Hnr)).
    apply (brk_ok_iff segs ms _ model eff' m' evs' Hno) in Hspec as (Heff & _ & Hok & _).
    apply Hcases in Hok. cbn [brk_eff eff_ret] in Hrb. rewrite Hok in Hnr. rewrite Hrb in Hnr. discriminate Hnr. }
  apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_res_cfg ms model (getr regs 17) r} => KA)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hkeep); exact Ht]].
  eapply srz_cases; [exact (exist _ b Hkeep) | eapply node_brk_lazy; [exact Hh | reflexivity | exact Hno] |].
  intros [r [Hr Hns']]. cbn [proj1_sig]. unfold brk_eff. fold h.
  pose proof (proj1 (Hcases r) Hr) as Er. subst r. fold b.
  rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep.
  unfold ms. rewrite adv_ret_epend. exact HA.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma node_set_tid_lazy : ltac2:(zQ "he5!h9!jc!hn1!lv6!of!l5!ltf!n2!or1!nb!irb!np8!s2!ov2!hma!o2!o9!lra!hu8!hv9!ih3!ii7!mt5!hg4!ip8!hhc!pg7!mtf!pgf!jge&@2$a@2$6Z@2$3@1$0#k0^1@2$6@2$3@1$0#k0^1$d&\1t@1$1@1$0#k0~0&@3$b@1$1@1$0#k0~1^1&@2$4@1$1@1$0#k0@1$1@1$0#k0&@1$2~3>2ms$h2>5model$h7>2x8@1$1@1$0#k0>0@3$5@1$7@1$1@1$0#k0@1$h9^2@1$9@1$1@1$0#k0>0@3$5@1$7@1$1@1$0#k0@1$h3^4@2$e@1$1@1$0#k0^2>0@3$5$h1@2$3@1$0#k0^3+m0>0@3$5@1$7@1$1@1$0#k0@1$ha^5@1$9@1$1@1$0#k0@6$hd?4segs?2SC@2$c^7^6$8\0$8@1$2$h8\1i$8@2$c@1$h4@2$h5^8@6$hb~2@1$2@2$4@1$1@1$0#k0@1$f@1$1@1$0#8~4~4@1$2$h6@1$2@2$4@1$1@1$0#k0$h0@2$hc~2^7").
Proof.
  intros ms model x8 Hh Hsvc Hno Htid.
  assert (Hsi : forall o, syscall_spec (sys_input segs ms x8) model o <->
     exists t, (0 < bv_unsigned t < PID_MAX_ENVELOPE)%Z /\ o = Ok (mkEffect t [] []) (with_tid t model) []).
  { intros o. rewrite (syscall_spec_96 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
    apply set_tid_fresh_outcome. exact Htid. }
  apply (node_fam_noacc ms model x8 tid_I
           (fun i => mkEffectU (proj1_sig i) [] [] [] [] [])
           (fun i => with_tid (proj1_sig i) model) _ Hh Hsvc Hsi).
  - intros [t Ht]. cbn [proj1_sig]. exists t. split; [exact Ht | reflexivity].
  - (* [comment removed for export] *)
    intros i. apply not_spurious_none. rewrite in_sysno_sys_input, Hno. apply injected_arm_none_96.
  - (intros eff m' ev nd_i4 _; ndestruct nd_i4 as (t & Ht & E)). apply Ok_inj in E as (-> & -> & ->).
    exists (exist _ t Ht). repeat split; reflexivity.
  - (intros eff m' ev nd_i5; ndestruct nd_i5 as (t & Ht & E)). apply Ok_inj in E as (-> & -> & ->). rewrite with_tid_halted. exact Hh.
  - (intros nd_i6; ndestruct nd_i6 as (t & _ & E)). exact (Unmodeled_Ok _ _ _ E).
  - intros [t Ht]. reflexivity.
Qed.

Lemma srz_set_tid_lazy : ltac2:(zQ "he1!h9!jc!n2!l5!nb!knd!s2!lq6!jmb!ltf!lqe!lr3!lv6!hma!kmf!kn6!irb!koe!kpc!hg4!hhc!pg7!pgf!ov2!lh4!lpe!mq1!mqb!jr3!lu5&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4regs@2$h8@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>5model$h3>1K$hc>1w@1$1@1$0#i0>0@3$3@1$2@1$1@1$0#i0@2$h1?4segs^6@2$d@1$1@1$0#i0^1>0@3$3$e@1$h2^2$f>0@3$3@1$2@1$1@1$0#k0@1$h4^5@1$4@1$1@1$0#k0>0@3$3@1$1@1$0#k0@2$h9^a@3$a@1$0#5+h1Kv$5@2$b@1$0#5+h1@2$hd@1$0#k0+m0>0@3$3@1$2@1$1@1$0#k0@1$h5^7@1$4@1$1@1$0#k0>0>3tid@1$1@1$0#k0>0@2$h0@2$9Z@2$c@1$0#k0^1@2$9@2$c@1$0#k0^1$h7@4$8?4segs?2SC@2$6@5$7?2fx@3$ha^e@3$a@1$0#5+aKv$5@2$b@1$0#5+a^2@2$hb^d+4^c^b@2$h6^2^a^9@4$8?4segs?2SC@2$6@5$7?2fx^d^c^b^a^9^8").
Proof.
  intros regs pc mem rom model K w HF HE Hh H17 Htid Hk.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  apply (srz_conseq segs _ (t_alt (fun _ : tid_I => K)));
    [| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
  eapply srz_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
                   | eapply node_set_tid_lazy; [exact Hh | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid] |].
  intros [t Ht]. cbn [proj1_sig].
  change (mkEffectU t [] [] [] [] []) with (mkEffect t [] []).
  rewrite apply_effect_no_write, adv_set_epend. apply Hk. exact Ht.
Qed.

(* [comment removed for export] *)
Lemma srz_exit_at_lazy : ltac2:(zQ "h93!h9!jc!l5!n2!knd!lpe!lqe!lr3!lu5!nb!hma!kmf!kn6!pha!koe!kpc!s2!hg4!phf!hhc!lh4!lq6!pi6!jmb!pj0&>0@1$1@1$0#k0@1$3@1$1@1$0#8&@3$6@1$0#5+h1Kv$4@2$7@1$0#5+h1&@2$5^a~1>4regs@2$h4@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>3mem~0>3rom~0>5model$h1>1w@1$1@1$0#i0>4code@1$1@1$0#k0>0@3$2@1$3@1$1@1$0#i0@2$e?4segs^6@2$a@1$1@1$0#i0^2>0@3$2$b@1$f^3$c>0@3$2@1$3@1$1@1$0#k0@1$h3^5@1$9@1$1@1$0#k0>0@2$d@3$2@1$1@1$0#k0~2@2$8@1$0#k0+le@3$2@1$1@1$0#k0~2@2$8@1$0#k0+ld>0@3$2@1$1@1$0#k0@2$5^b@3$6@1$0#5+aKv$4@2$7@1$0#5+a^5@4$h7?4segs?2SC@2$h0@5$h5?2fx^c^b^a^9^8@2$h6@3$h8@1$0#k0^6@2$8@1$0#k0+vf@1$h2^8").
Proof.
  intros regs pc mem rom model w code HF HE Hh H17 H10.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
  eapply srz_exit; [exact Hh | reflexivity |].
  destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma mmap_gates_core50 : ltac2:(zQ "e0!h9!lu5!l5!kmf!irb!oma!kn6!pj9!jc!lra!pl3!pm6!pn9!pob>5flags@1$8@1$0#k0>4prot@1$8@1$0#k0>0@3$2$9@1$b^2+j2@2$4@3$2$3@3$c^2^3@2$1@1$0#k0Z$5@2$4@3$2$3@3$d^2^3@2$1@1$0#k0Z$5@2$4@3$2$3@3$7@2$1@1$0#k0Z^3@2$1@1$0#k0Z$6@2$4@3$2$3@3$7@2$1@1$0#k0+3^3@2$1@1$0#k0Z$5@3$2$3@3$a@2$1@1$0#k0+3^3@2$1@1$0#k0Z$6").
Proof.
  intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b.
  rewrite Hc. repeat split; try (vm_compute; reflexivity).
  all: destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Definition fixedin_ok_vmmaps : ltac2:(zQ "40!h9!nu9!jc!lra>4prot$3>4addr@1$2@1$0#k0>1n@1$2@1$0#k0>1h$1$1") := ltac2:(zQ "h60!h9!jc!lv6!kmf!nu9!ntb!nu2!of!lra!ppe!nv2!msc!og1!oge!mk3!oh9!oi8!oj6!nsc!pqe!mr5!ps5\4prot$8\4addr@1$1@1$0#k0\1n@1$1@1$0#k0\1h$4M3\0$3$4@2$h5^4Z@8$a@1$h1^1@1$e^1@3$5@2$7@1$1@1$0#k0@1$1@1$0#k0@4$6@1$1@1$0#k0@1$1@1$0#k0^3^2@3$9@1$h0^1@2$2@1$0#k0^3@2$h4@2$2@1$0#k0^3@2$2@1$0#k0^2@1$h2^1@1$b^1@1$d^1@1$f^1@1$c^1@3$h3^1^3^2").

Definition fixedin_destroyed_vmmaps : ltac2:(zQ "30!h9!nu9!jc>4addr@1$2@1$0#k0>1n@1$2@1$0#k0>1h$1$1") := ltac2:(zQ "f1!h9!lv6!ppe!mr5!jc!nu9!nv2!msc!og1!oge!mk3!oh9!oi8!oj6!nsc&@2$3@2$1@1$0#k0^3@2$1@1$0#k0^2\4addr@1$4@1$0#k0\1n@1$4@1$0#k0\1h$5@8$6@1$d^1@3$2@1$a^1@2$1@1$0#k0^3~0@3$2@1$c^1@2$1@1$0#k0^3~0@1$e^1@1$7^1@1$9^1@1$b^1@1$8^1").

Definition fixedin_ok_model : ltac2:(zQ "40!h9!jc!hg4!lra>4prot$3>5flags@1$1@1$0#k0>4addr@1$1@1$0#k0>1n@1$1@1$0#k0>1m$2$2") := ltac2:(zQ "80!h9!jc!lra!hg4!mi2!ok4!psc!pu6\4prot$2\5flags@1$1@1$0#k0\4addr@1$1@1$0#k0\1n@1$1@1$0#k0\1m$3@4$6^4^3^2@2$5@4$7^5^3^2@1$4^1^1").
Definition fixedin_destroyed_model : ltac2:(zQ "30!h9!hg4!jc>4addr@1$2@1$0#k0>1n@1$2@1$0#k0>1m$1$1") := ltac2:(zQ "60!h9!jc!hg4!mi2!pvc!qh4\4addr@1$1@1$0#k0\1n@1$1@1$0#k0\1m$2@4$4^3^2@3$5^3^2@1$3^1^1").

(* [comment removed for export] *)
Definition fixedin_ok_eff : ltac2:(zQ "40!h9!jc!lra!hgc>4prot$2>4addr@1$1@1$0#k0>1n@1$1@1$0#k0$3") := ltac2:(zQ "e6!h9!jc!hn1!of!kmf!ntb!o2!o9!nu2!mt5!mtf!lra!hgc!ps5&@2$3@1$1@1$0#k0@1$6@1$1@1$0#8&@1$2~0&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~2&@4$8@1$1@1$0#k0@1$1@1$0#k0^2^1&@3$5~2~4~3\4prot$b\4addr@1$1@1$0#k0\1n@1$1@1$0#k0M4\0$4$c@2$d^3Z@6$a^2~1~3~5@1$2$9@1$2@2$3@1$1@1$0#k0$7@6$a^2~1~5~3@1$2$9@1$2@2$3@1$1@1$0#k0$7").

Lemma with_mmap_replacement_halted' : ltac2:(zQ "70!h9!jc!hhc!n2!l5!hg4!psc>5flags@1$1@1$0#k0>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1m$5@3$4@1$3@1$1@1$0#k0@1$2@4$6^4^3^2^1@1$2^1").
Proof.
  intros. unfold with_mmap_replacement, with_mmap_backing, vm_forget_range.
  destruct (mmap_noreserve_b flags); reflexivity.
Qed.
Lemma with_mmap_destroyed_halted' : ltac2:(zQ "80!h9!jc!hhc!n2!l5!hg4!nu9!pvc>1a@1$1@1$0#k0>1n@1$1@1$0#k0>1h$6>1m$5@3$4@1$3@1$1@1$0#k0@1$2@4$7^4^3^2^1@1$2^1").
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma mmap_fixedin_outcome_si : ltac2:(zQ "j22!h9!jc!l5!lra!hn1!lrd!of!hgc!lu5!lv6!kmf!kn6!pha!jh9!mi2!hqb!ip8!mg4!ltf!ntb!o2!o9!nu2!irb!is1!ji4!hu8!sa!io8!mt5!hg4!qj1!qjd!qk9!mtf!mj7!ql8!mk3!oj6!qm6!qn5!pm6!qp1!qqd!qrf!rge!rj1!mr5!mrc!ms2&@2$6@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>2ms$ha>2x8@1$1@1$0#k0>5model$he>4prot$3>5flags@1$1@1$0#k0>4addr@1$1@1$0#k0>3len$3>0@3$2$3@2$9@1$0#k0^6+te>0@2$c@3$2$3^5Z@3$2$3^5+3>0@3$2$3@1$i9^5+j2>0@3$2@1$1@1$0#k0@2$5^aN0^5>0@3$2$3@2$j1@2$9@1$0#k0^6$i3Z>0@2$h2Z@2$9@1$0#k0^7>0@3$2@1$1@1$0#k0@2$5^dN1@2$8@1$0#k0^7>0@2$h2Z^8>0@3$2@1$1@1$0#k0@2$5^fN2@2$8@1$0#k0^c>0@3$2@1$1@1$0#k0@2$5^h0N3^c>0@3$2@1$1@1$0#k0@2$5^h1N4@2$8@1$0#k0-1>0@3$2@1$1@1$0#k0@2$5^h2N5@2$8@1$0#k0Z>0@2$j0@2$if@2$9@1$0#k0^e@1$h1^d@1$hf@1$e^h1=1n@1$1@1$0#k0@2$8@1$0#k0@1$h1^e>0@3$2$a@3$i4@1$i6@1$e^h3^h0^1$b>0@3$2$a@3$i1@1$i5@1$e^h4^h1^2$b>0>0@3$2$3^h4+3@3$2$a@4$i8^h4^h6^h3^4$b>1o@1$d$7@2$h9@3$hc@3$hb?4segs^h9^h8^h7^1@2$c@2$id^h7^1@2$c@3$2@1$d$7^1@4$f$7@3$ib^h6^h4^5@5$ic^h6^h5^h4^5^h7@1$4$h0@2$h8$3\1e$3@2$h7@3$ie$3^1$i7@3$2@1$d$7^2@4$f$7@6$i2@1$i0^1@1$4@2$6@1$1@1$0#k0@1$h4@1$1@1$0#8~1@3$h3~0@4$h6@1$1@1$0#k0@1$1@1$0#k0^h5^6~1@1$4$hd@1$4@2$6@1$1@1$0#k0$h5@3$ia^h5^6^h8@1$4$h0").
Proof.
  intros ms x8 model prot flags addr len Hno Hprot Hcore H0 Hal Hpos H1 Hlen H2 H3 H4 H5 Htop n Hrf Hmc Hbud o.
  pose proof (u64_range (vm_init_sp (m_vmmaps model))) as Hcv. pose proof Htop as Htop'. unfold alloc_top, stack_max_size in Htop'.
  assert (Hlen' : (len < 2 ^ 64)%Z).
  { pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  assert (E1 : w_is0 (ms_gpr ms 1) = false).
  { unfold w_is0. apply bv_eqb_neq. intros Hz. rewrite Hz in Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hu1. lia. }
  ndestruct (mmap_gates_core50 flags (Z_to_bv 64 prot) Hcore) as (G1 & G2 & G3 & G4 & G5).
  rewrite (syscall_spec_222 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, in_arg3_sys_input, in_arg4_sys_input, in_arg5_sys_input.
  rewrite H0, H2, H3, H5.
  unfold fixedin_ok_eff, fixedin_ok_model, fixedin_ok_vmmaps, fixedin_destroyed_model. unfold n.
  destruct Hprot as [-> | ->].
  - (* [comment removed for export] *)
    rewrite (mmap_fixed_noaccess_outcome addr (ms_gpr ms 1) (Z_to_bv 64 0) flags (ms_gpr ms 4) (Z_to_bv 64 0) _ model o
               mmap_off_aligned_b_0 (mmap_anon_b_of_core flags _ Hcore eq_refl) E1 G1 G2 G3);
      rewrite ?Hu1; [reflexivity | exact Htop | exact Hal | exact Hpos | exact Hrf | exact Hmc].
  - (* [comment removed for export] *)
    rewrite (mmap_fixed_rw_commit_outcome addr (ms_gpr ms 1) (Z_to_bv 64 3) flags (ms_gpr ms 4) (Z_to_bv 64 0) _ model o
               mmap_off_aligned_b_0 (mmap_anon_b_of_core flags _ Hcore eq_refl) E1 G1 G2 G4 G5);
      rewrite ?Hu1; [| exact Htop | exact Hal | exact Hpos | exact Hrf | exact Hmc].
    cbn [Z.eqb]. split.
    + intros [He | [(_ & ->) | Hd]]; [left; exact He | right; left; reflexivity | right; right; exact Hd].
    + intros [He | [-> | Hd]]; [left; exact He | right; left; split; [exact (Hbud eq_refl) | reflexivity] | right; right; exact Hd].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma srz_mmap_fixedin_lazy {AF : AllocForced SC} :
  forall regs (pc : word) mem rom model w (prot : Z) (flags addr : word) (len : Z) KB,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None ->
  getr regs 17 = Z_to_bv 64 222 ->
  (prot = 0 \/ prot = 3)%Z -> mmap_flags_core flags = 50%Z ->
  getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
  getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
  (bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->   (* [comment removed for export] *)
  getr regs 12 = Z_to_bv 64 prot -> getr regs 13 = flags ->
  getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  region_free (vm_reserved (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  (prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
  srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4)
                             (if Z.eqb prot 0 then unfill addr n mem else zfill addr n mem) rom)
                       (fixedin_ok_model prot flags addr n model)) KB ->
  srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
  intros regs pc mem rom model w prot flags addr len KB HF HE Hh H17 Hprot Hcore H10 Hal Hpos H11 Hlen Htop H12 H13 H14 H15 n Hrf Hmc Hbud HB.
  pose proof (u64_range (vm_init_sp (m_vmmaps model))) as Hcv. pose proof (u64_range addr) as Har.
  pose proof Htop as Htop'. unfold alloc_top, stack_max_size in Htop'.
  eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
  set (ms := epend regs pc mem rom (getr regs 17)).
  assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs ms (getr regs 17))) = 222%Z) by (rewrite in_sysno_sys_input; exact Hno).
  assert (Hlen' : (len < 2 ^ 64)%Z) by (pose proof (page_round_up_Z_bounds len ltac:(lia)); lia).
  pose proof (mmap_fixedin_outcome_si ms (getr regs 17) model prot flags addr len Hno Hprot Hcore
                           ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
                           ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen
                           ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
                           ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13)
                           ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
                           ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)
                           Htop Hrf Hmc Hbud) as Hsi.
  cbv zeta in Hsi. fold n in Hsi.
  assert (Haddr_ne : addr <> errno_ret ENOMEM).
  { intros E. apply (f_equal bv_unsigned) in E. rewrite (errno_ret_unsigned ENOMEM) in E by (unfold ENOMEM; lia).
    unfold two_pow_64, ENOMEM in E. pose proof (page_round_up_Z_bounds len ltac:(lia)). lia. }
  (* [comment removed for export] *)
  assert (Hok : syscall_spec (sys_input segs ms (getr regs 17)) model
                  (Ok (fixedin_ok_eff prot addr n) (fixedin_ok_model prot flags addr n model) [])).
  { apply Hsi. right; left. reflexivity. }
  assert (Hokr : refusal_b (sys_input segs ms (getr regs 17)) model (eff_ret (fixedin_ok_eff prot addr n)) = false).
  { rewrite (refusal_b_mmap _ model _ Hno'). unfold fixedin_ok_eff. destruct (Z.eqb prot 0); cbn [eff_ret];
      apply bv_eqb_neq; exact Haddr_ne. }
  assert (Hspur : forall ws zs us cs ci,
            spurious_refusal_cfg the_scfg (sys_input segs ms (getr regs 17)) model (mkEffectU (errno_ret ENOMEM) ws zs us cs ci)).
  { intros ws zs us cs ci.
    apply (alloc_refusal_spurious _ model _ (fixedin_ok_eff prot addr n) (fixedin_ok_model prot flags addr n model) []).
    - apply family_off_mmap_true. exact Hno'.
    - cbn [eff_ret]. apply errno_is_refusal_mmap. exact Hno'.
    - exact Hok.
    - exact Hokr. }
  apply (srz_silent_all segs (mkCfg ms model) unit
           (fun _ => mkCfg (advance_past_svc (apply_effect ms (fixedin_ok_eff prot addr n))) (fixedin_ok_model prot flags addr n model)) KB tt).
  - apply (node_fam_noacc ms model (getr regs 17) unit (fun _ => fixedin_ok_eff prot addr n)
             (fun _ => fixedin_ok_model prot flags addr n model) _ Hh eq_refl Hsi).
    + intros []. right; left. reflexivity.
    + intros []. apply spurious_refusal_not_refusal. exact Hokr.
    + intros eff m' evs [He | [E | (e & He & E)]] Hns.
      * (* [comment removed for export] *)
        exfalso. apply Hns. apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->). apply Hspur.
      * apply Ok_inj in E as (-> & -> & ->). exists tt. repeat split; reflexivity.
      * (* [comment removed for export] *)
        exfalso. apply Hns. apply Ok_inj in E as (-> & -> & ->).
        assert (He' : e = ENOMEM) by (destruct He as [<-|[]]; reflexivity). subst e. apply Hspur.
    + (* [comment removed for export] *)
      intros eff m' evs [He | [E | (e & He & E)]].
      * apply mmap_err_out_enomem in He. apply Ok_inj in He as (-> & -> & ->). exact Hh.
      * apply Ok_inj in E as (-> & -> & ->).
        unfold fixedin_ok_model; rewrite with_mmap_replacement_halted', with_vmmaps_halted; exact Hh.
      * apply Ok_inj in E as (-> & -> & ->).
        unfold fixedin_destroyed_model. rewrite with_mmap_destroyed_halted'. exact Hh.
    + intros [He | [E | (e & He & E)]];
        [apply mmap_err_out_enomem in He; exact (Unmodeled_Ok _ _ _ He) | exact (Unmodeled_Ok _ _ _ E) | exact (Unmodeled_Ok _ _ _ E)].
    + intros []. unfold fixedin_ok_eff. destruct (Z.eqb prot 0); reflexivity.
  - intros []. unfold ms, fixedin_ok_eff. destruct (Z.eqb prot 0).
    + rewrite adv_unmaps1_epend. exact HB.
    + rewrite adv_zeros1_epend. exact HB.
Qed.

End Noacc.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Open Scope Z_scope.
Import AX2 AX2S AP APS.

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma is_ecall_at_sound : ltac2:(zQ "h50!h9!jc!irb!l5!rn5!kmf!kn6!hma!o2!n2!is1!rr0!koe!kpc!rrb!rs2!sh2!mr5!mrc!ltf!lu5>4SEGS@1$8$b>2cs$e>0@3$3$5@2$f^2^1$6@2$2@2$h2Z@1$4^2@2$2@2$h3@2$h1@1$4^2+4$h0@2$a@1$1@1$0#i0\1w@1$1@1$0#i0@2$2@3$3@1$9@1$1@1$0#i0@2$c^4@2$h4@1$0#k0@1$4^3@2$7@1$1@1$0#i0^1@3$3$5@1$d^1$6").
Proof.
  intros SEGS cs H. unfold is_ecall_at in H.
  apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4].
  apply Z.leb_le in H0. apply Z.ltb_lt in H4.
  destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hw; [|discriminate].
  repeat split; try assumption. exists w. auto.
Qed.

Lemma bv_and_255 : ltac2:(zQ "b0!h9!lu5!irb!l5!lra!sh2!shb!mrc!ltf!jc!pj0>2c0$4>0@2$2@2$7Z^1@2$8^1$5@3$3@1$9@1$0#k0@3$a@1$0#k0@2$1@1$0#k0^2@2$1@1$0#k0+vf@2$1@1$0#k0@2$6^2+vf").
Proof.
  intros c0 Hc. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by (unfold two64 in *; lia).
  change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
  symmetry. apply u64_lit. unfold two64 in *.
  pose proof (Z.mod_pos_bound c0 (2 ^ 8) ltac:(lia)). lia.
Qed.

Lemma Some_inj : forall {T : Type} (a b : T), Some a = Some b -> a = b.
Proof. intros T a b H. congruence. Qed.

Lemma v_addi_pc : ltac2:(zQ "a0!h9!mr5!lu5!l5!lra!sh2!mqb!mrc!ltf!jc>1p$4>0@2$7Z^1>0@2$8@2$1^2+4$5@3$3@1$9@1$0#k0@2$6@2$2@1$0#k0^3+4@2$2@1$0#k0@2$1^3+4").
Proof.
  intros p H0 H4. unfold v_addi. f_equal. unfold two64 in *. rewrite u64_lit by lia. reflexivity.
Qed.
End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CsOk.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
#[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH FS0).

(* [comment removed for export] *)

End CsOk.
(* [comment removed for export] *)
