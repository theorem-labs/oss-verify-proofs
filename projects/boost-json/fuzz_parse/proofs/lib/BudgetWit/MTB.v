(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: made from MainTop.v for the budget-premise witness: the same statements and proof scripts over BudgetWit.Rzb.realizes; only the name tables change. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, the launch's channel reader, the launch input as a ProcInput. *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts
  MmapSim AllocSim FileSim AgentLib SymExec2 SymExec2Sound SymRun SymDriveX MemSplit MuslStrlen
  Spec RefNodes LibTail LibDiagKn LibDiagKnMain RefStartup RefStartupFacts RefMainEntry RefMainEntryN
  RefStartupDefs RefUsageCS_defs RefUsageCS RefOpenFailCS_defs RefOpenFailCS RefReadErr_defs RefReadErr RefRefused RefHdrErr
  RefStdioDefs RefExitBase RefMainExit LibMainRet HeapCeil
  RegsEquivM MainEqv MainDefs MainArith MainWalk_defs MainMem MainHeap MainSegs MainOpen MainLoop
  MainHeapM DrvExitH DrvMainExitH.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells Arr Step Frame MState SysStep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require FP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe4Npos35stdpp9bitvectorbdefinitionsje2bv37Corelib4Init5Logicm02eq04bool04truem03iff69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~obdlist_byte_eqb06option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ta7mem_inv69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8MainDefs~~~~~~hhe7ro_none79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~hm45rsegshe1Z46Stdlib6ZArith6BinInt1Zhqd2lejebbv_unsigned3h5LinuxProcessSemanticsfLinuxProcessSem5Stateht9estack_max_size69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Frame~~~~~~ih99frame_mod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ile3stk69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8MainOpen~~~~~~iq16regA_whqd3sub03nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefcHeapSR_iface~~~~~~iv28hs_RHEAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~jk15block04prod03natm03andm02or37Corelib5Lists7ListDefjqa6Forallhqd3addhqd6of_nat69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9LibDiagKn~~~~~~jtc9cell_wf_b69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8MainLoop~~~~~~ki5bclient_cellki5bstatic_cell36Stdlib5Lists4Listkne7forallb99OSSVerify6Proofsaboost_jsonafuzz_parse3lib7MainTop3Top7TwoArgs5GenFX~~~~~~kpc5tstat69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8MainSegs~~~~~~kv16regL_wkv17regLe_wkpc5cs_okm02exki56mframe69OSSVerify6Proofsaboost_jsonafuzz_parse3libbRefMainExit~~~~~~ll9amain_frameje7Z_to_bv03fst79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJcHeapMF_iface~~~~~~lr48hs_RHEAP03snd69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~mg75hceiljk16RERRNOjk13mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~mlc6PStatekne2Inkpc6tstatMjtc7cell_okjtc8cells_ok03appkne4incl04pair04conskpcccells_keep_akpccstderr_dirtyhheaexit_cellskpc9exit_listhqd3mulhhe9ax1_cellskpccstdout_cellskpc7cells_a37Corelib4Init5Peanonkc2lekpc7cells_bhheaerrno_cell06length37Corelib4Init3Natno73mulobazero_lines01S04Somekv19buf_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ns33rdn69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~og5floaded_segmentshqd2lthqd3pow69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~olb4TSetob5t_die46Stdlib5Arith8PeanoNat3Natoq63ltbno73add3h5LinuxProcessSemanticsfLinuxProcessSem2Fsosf2Fshhe9hdr_callshhe7hdr_cfgolb6t_emitolb6t_exitob9MAX_INPUTob1Wob9exit_codeobbmsg_overrunob9msg_shortob6t_bodyhqd6to_nathheh2main_realizes_stmtiv23hsriv2cheap_sr_hypshheaheap_extralr43hmfhhebheap_extraM3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutps79EntryDraw3h5LinuxProcessSemantics5Riscv7Preludeqg85bvmap3h5LinuxProcessSemanticsfLinuxProcessSem3Runqj7avalid_argvqj7avalid_envpqj78valid_sp69OSSVerify6Proofsaboost_jsonafuzz_parse3libaRefStartup~~~~~~qobamain_entryiv2bhs_rauxv_okqj7h0entry_stack_fitsosf9fs_lookuphheftarget_run_stmt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib2FP~~~~~~rha4frm0ns36fp_csrm03not" s.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import MainTop.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.BudgetWit.Rzb OSSVerify.Proofs.boost_json.fuzz_parse.lib.BudgetWit.MOB OSSVerify.Proofs.boost_json.fuzz_parse.lib.BudgetWit.RUCB.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation RPH := Plain.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Top.
  Context {HCEIL : HeapCeil}.
  Variable HS : ltac2:(zQ "10!poc$0").
  Hypothesis HH : ltac2:(zQ "10!pp3@2$0?5HCEIL?2HS").
  Hypothesis HX : ltac2:(zQ "10!pq3@1$0?2HS").

  Let KRELh : forall s mo, hs_KREL HS s mo -> m_halted mo = None /\ m_vm_lazy mo = [].
  Proof. ndestruct HH as (_ & K & _). exact K. Qed.
  Let AOK : alloc_ok_of_live HS.
  Proof. ndestruct HH as (_ & _ & _ & A & _). exact A. Qed.
  Let RFR : RHEAP_frame HS.
  Proof. ndestruct HH as (_ & _ & _ & _ & A & _). exact A. Qed.
  Let RBR : RHEAP_block_range HS.
  Proof. ndestruct HH as (_ & _ & _ & _ & _ & A & _). exact A. Qed.
  Let AUF : rauxv_frame HS.
  Proof. ndestruct HH as (_ & _ & _ & _ & _ & _ & _ & _ & A & _). exact A. Qed.
  Let LBR : lb_remove_laws HS.
  Proof. ndestruct HH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & A & _). exact A. Qed.
  Variable HM : ltac2:(zQ "10!pr1$0").
  Hypothesis HXM : ltac2:(zQ "10!pr8@2$0?5HCEIL?2HM").
  Hypothesis HO : handover HS HM.
  Let KRELhM : forall s mo, HeapMF_iface.hs_KREL HM s mo -> m_halted mo = None /\ m_vm_lazy mo = [].
  Proof. exact (hm_krel_h HM HXM). Qed.

  Section UsageTop.
    Context {AMB : Amb}.
    Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
    Variable sp0 : word.
    Variables av envv : list (list byte).
    Variable rdraw : ltac2:(zQ "10!pvb$0").
    Variable tid : word.
    Variable regs0 : ltac2:(zQ "30!j7!qie!lb@2$1@1$0#5@1$2@1$0#k0").
    Variable mem0 : ltac2:(zQ "30!j7!lb!t2>0@1$1@1$0#k0@1$2@1$1@1$0#8").
    Variables (brk mbase : word) (lim : Z) (fs0 : Fs) (stdin0 : InputStream).
    Hypothesis Hva : ltac2:(zQ "10!qm3@1$0?2av").
    Hypothesis Hve : ltac2:(zQ "10!qn1@1$0?4envv").
    Hypothesis Hvsp : ltac2:(zQ "10!qnf@1$0?3sp0").
    Hypothesis Htid : ltac2:(zQ "50!j7!oke!hsb!jpf!ol4@2$3@2$1Z@2$2@1$0#k0?3tid@2$1@2$2@1$0#k0?3tid@2$4+2+h6").
    Hypothesis ME : @main_entry AMB (mkProcInputC av envv fs0 stdin0) mbase
                      (Z_to_bv 64 291460) sp0 rdraw tid regs0 mem0.
    Hypothesis Hvl : valid_launch (mkProcInputC av envv fs0 stdin0).
    Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) (mkProcInputC av envv fs0 stdin0).
    (* LPS 727298f3: the launch's channel reader ([Run.valid_input]); the usage message's write needs it *)
    Hypothesis Hrdr : in_channel_reader (mkProcInputC av envv fs0 stdin0) = true.
    Let Hio_Hargv : in_argv (mkProcInputC av envv fs0 stdin0) = av := eq_refl.
    Let Hio_Henvp : in_envp (mkProcInputC av envv fs0 stdin0) = envv := eq_refl.
    Let Hio_Hhw : in_hwcap (mkProcInputC av envv fs0 stdin0) = a_hwcap := eq_refl.
    Hypothesis Hargc : ltac2:(zQ "70!nnf!h8!jpa!n4!rm5!j7!lb@1$4@3$3$2@2$0@1$1@1$6@1$5#8?2avN2").
    Hypothesis Hfit : ltac2:(zQ "10!qu5@3$0?3sp0?2av?4envv").
    Let model0 : Model := MainDefs.model0 tid brk mbase sp0 lim (mkProcInputC av envv fs0 stdin0).
    (* LPS 727298f3: the two facts MainOpen's usage section takes about the start model *)
    Let Hh0 : m_halted model0 = None := eq_refl.
    Let Hlazy0 : m_vm_lazy model0 = [] := eq_refl.

    (* The launch lemmas' section premises, closed after [try exact ME] has fixed the input
       and the entry: [eapply L; try exact ME; me_close]. *)
    Local Ltac me_close :=
      try first [ exact Hvsp | exact Hva | exact Hve | exact Hlo | exact Hhi | exact Hvl | exact Hlau | reflexivity | lia ].

    Theorem ref_usage :
      realizes RSEGS (mkCfg (mkst regs0 (Z_to_bv 64 0x473d0) mem0 (seg_rom RSEGS)) model0) (t_die (msg_usage (hd [] av)) fs0).
    (* LPS 727298f3 port: written out.  The recorded proof applied [cat_argv_ptr] in the old
       stack layout; this is the text of boost-beast/http_request's lib/MainTop.v [ref_usage]
       over the revision's [cat_argv_ptr] (MOB's [seg_U], MainOpen's [arg0_facts], RUCB's [ref_usage_cs]), the launch
       lemmas instantiated from [ME]. *)
    Proof.
      pose proof (proj1 Hvsp : 0x7fff80000000 <= bv_unsigned sp0) as Hlo. pose proof (proj1 (proj2 Hvsp) : bv_unsigned sp0 <= 0x800000000000) as Hhi.
      apply (OSSVerify.Proofs.boost_json.fuzz_parse.lib.BudgetWit.MOB.seg_U sp0 av envv rdraw tid regs0 mem0 model0 (mkProcInputC av envv fs0 stdin0) mbase brk (Z_to_bv 64 291460)
               Hva Hve Hvsp Htid Hio_Hargv Hio_Henvp Hio_Hhw Hvl Hlau ME Hargc Hh0 Hlazy0).
      intros R M Q2 Q4 Q8 Q11 FM (Fra & [s0v Fs0] & F1 & F2 & F3 & F4 & F5 & F6 & F7) Margv.
      assert (RS : forall r, In r (OSSVerify.Proofs.boost_json.fuzz_parse.lib.BudgetWit.MOB.regU_w sp0) -> bv_unsigned (fst r) = bv_unsigned sp0 - 128 /\ snd r = 80).
      { intros r Hr. unfold OSSVerify.Proofs.boost_json.fuzz_parse.lib.BudgetWit.MOB.regU_w in Hr. cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd]. rewrite u_small by lia. split; reflexivity. }
      assert (ABOVE : forall x : word, bv_unsigned sp0 <= bv_unsigned x -> M x = mem0 x).
      { intros x Hx. apply (proj1 FM). apply outside_of_disjoint. intros r Hr. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2. lia. }
      destruct (arg0_facts sp0 av envv rdraw tid regs0 mem0 model0 (mkProcInputC av envv fs0 stdin0) mbase brk (Z_to_bv 64 291460)
                  Hva Hve Hvsp Htid Hio_Hargv Hio_Henvp Hio_Hhw Hvl Hlau ME Hargc Hh0 Hlazy0)
        as (Sr & Slo & Shi & Slen & [t8 Ht8] & Sfit & Snul).
      set (pp := cat_argv_ptr (ed_top rdraw) av envv (in_execfn (mkProcInputC av envv fs0 stdin0)) 0) in *.
      set (a0s := nth 0 av []) in *.
      pose proof (u64_range pp) as Hpr.
      replace (hd [] av) with a0s by (subst a0s; destruct av; reflexivity).
      change fs0 with (m_fs model0).
      refine (OSSVerify.Proofs.boost_json.fuzz_parse.lib.BudgetWit.RUCB.ref_usage_cs sp0 model0 Hvsp Hh0 Hlazy0 eq_refl ltac:(exact Hrdr) pp (bv_unsigned tid) (bv_unsigned (canary_w rdraw)) s0v R M Q2 Q4 Q8 Q11
                _ _ _ _ Htid _ Margv Slo Fra Fs0 F1 F2 F3 F4 F5 F6 F7 a0s t8 Snul Slen _ _ _ _).
      - intros a n Ha Hn. rewrite u_small in Ha, Hn by lia. eapply frame_mod_store_ok; [exact FM|].
        eapply main_entry_store_ok_win; try exact ME; me_close; unfold RefUsageCS_defs.US_STK in *; try apply wok_of_old; lia.
      - intros i Hi. rewrite (proj1 FM (Z_to_bv 64 i)); [eapply main_entry_ro_none; try exact ME; me_close |].
        apply outside_of_disjoint. intros r Hr. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2, u_small by lia. lia.
      - eapply cells_ok_frame; [apply diag_cells_wf | eapply cells_ok_main_entry; try exact ME; me_close | exact FM |].
        eapply Forall_impl; [| apply diag_cells_range]. intros [[a w] v] [R1 R2] r Hr. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2. lia.
      - eapply rdn_frame; [exact FM | | unorm; lia |].
        + rewrite Z_to_bv_bv_unsigned. eapply RefStartupFacts.main_entry_tid; try exact ME; me_close.
        + intros r Hr. unorm. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2. lia.
      - assert (CK : canary_ok mem0 (bv_unsigned (canary_w rdraw))) by (eapply canary_ok_main_entry; try exact ME; me_close).
        split; [| apply u64_range]. eapply rdn_frame; [exact FM | exact (proj1 CK) | unfold CANARY; unorm; lia |].
        intros r Hr. unfold CANARY. unorm. destruct (RS r Hr) as [E1 E2]. rewrite E1, E2. lia.
      - lia.
      - specialize (Sfit Hfit). lia.
      - rewrite <- Sr. apply rdn_ext; [lia|]. intros x Hx. apply ABOVE. lia.
      - rewrite <- Ht8. apply rdn_ext; [unorm; lia|]. intros x Hx. apply ABOVE. revert Hx. unorm. intros Hx. lia.
    Qed.
  End UsageTop.

  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
End Top.
