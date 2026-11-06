(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  Hoare RefExitBase RefStdioDefs RefExit RefPrintfBufBase LibTail StepTac WalkTac Spec RefMainExit DrvExitH.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick11I69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~l94getrhf2BVhf4BvWfk12eqhf7Z_to_bv37Corelib4Init9Datatypesr64list3h5LinuxProcessSemantics5Riscv7Preludet55bvmap69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~hg3floaded_segmentsr66option3h5LinuxProcessSemanticsfLinuxProcessSem3Runhl55mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statehoa4m_fs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8DrvExitH~~~~~~hs09exit_preHl94mkstl97seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3libbRefMainExit~~~~~~ih9amain_frame69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~im5dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~iqd8realizesiqd6t_emitiqd6t_exit69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~jg81W46Stdlib6ZArith6BinInt1Zjk43addhf6bv_andhfbbv_unsignedhoa5Model" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section MainExitH.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable model : ltac2:(zQ "10!jna$0").
  Theorem main_return_exitH : ltac2:(zQ "ha2!h9!jc!l5!p4!pb!q0!q7!qc!se!vb!hj9!hkc!ho1!hr8!hvb!ig8!igf!il7!ipc!iu8!iv4!ive!jjf!jlc!jm3!jmc&@3$4@1$0#5+2Kv$2@2$5@1$0#5+2&@3$4@1$0#5+4Kv$2@2$5@1$0#5+4>4regs@2$9@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$b@1$1@1$0#8>2sp@1$1@1$0#k0>6status@1$1@1$0#k0>5slots@1$8@1$1@1$0#k0>7pending@1$8@1$1@1$0#8>0@3$6@1$1@1$0#k0@2$3^6~0^4>0@3$6@1$1@1$0#k0@2$3^7@3$4@1$0#5+8Kv$2@2$5@1$0#5+8^4>0@3$h1^7^6^4>0>5regs'@2$9@1$0#5@1$1@1$0#k0>0@3$6@1$1@1$0#k0@2$3^1~0@2$7@1$0#k0@2$h7@2$h9@1$0#k0^8+l0>0@3$6@1$1@1$0#k0@2$3^2~1@2$3^b~1>0@3$6@1$1@1$0#k0@2$3^3@3$4@1$0#5+aKv$2@2$5@1$0#5+a^9@5$e^4^c?5model^a^8@4$h3$a$h2@2$c@5$f?2fx^a@2$7@1$0#k0+knlsc^9@1$h0$a?5model@2$h4@2$h6+1^5@2$h5@3$h8@1$0#k0^7@2$7@1$0#k0+vf@1$d?5model").
  Proof.
    intros regs mem sp status slots pending Hsp Hs0 MFH HPRE.
    pose proof (x_regs_ok regs mem sp slots Hsp MFH) as HR.
    pose proof (x_know_ok regs mem sp slots MFH) as HK.
    destruct MFH as [HL _ _ Hlo Hhi]. pose proof (u64_range sp) as Hspr.
    (* [comment removed for export] *)
    ndestruct (HPRE (regupd (regupd (regupd regs 2 (Z_to_bv 64 (bv_unsigned sp + 80))) 4 (getr regs 4)) 10 status))
      as (sp' & tp' & tid & wp2 & rp2 & _ & _ & Hh & Hlazy & _); [gres; reflexivity | gres; reflexivity | gres; reflexivity |].
    eapply (rz_run RSEGS FUELX STOPSX scr0 0x475cc x_sr x_kn 41 (fst (fst x_r)) (snd (fst x_r)) (snd x_r)
              (fst (fst x_c)) (snd (fst x_c)) (snd x_c) (ENV (x_vals regs sp slots)) mem (seg_rom RSEGS) regs model);
      [ vm_cast_no_check (@eq_refl _ x_r) | vm_cast_no_check (@eq_refl _ x_c)
      | exact HR | exact HK | apply Forall_nil | apply Forall_nil | exact Hh | exact Hlazy | ].
    clear HR HK. intros R' M' HR HK EQM.
    change (s_pc (fst (fst x_r))) with 0xda7bc%Z. change (s_regs (fst (fst x_r))) with x_srF in HR.
    assert (EM : M' = mem) by (rewrite EQM; reflexivity). rewrite EM. clear EQM EM.
    apply ref_exitH_Z. apply HPRE.
    - regv HR (2 : reg). cbn [edenot ev ENV]. rewrite alu_add, vadd_wZ. reflexivity.
    - regv HR (4 : reg). cbn [edenot]. rewrite (x_ev_junk regs sp slots 13 HL) by lia. f_equal; apply bv_eq; reflexivity.
    - regv HR (10 : reg). cbn [edenot]. rewrite (x_ev_junk regs sp slots 17 HL) by lia. rewrite <- Hs0. f_equal; apply bv_eq; reflexivity.
  Qed.
End MainExitH.
