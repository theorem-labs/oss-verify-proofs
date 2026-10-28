(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes InitMem RunConst.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA SysStepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed Harness ProgA AsanProgDeps BothHandoff.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require Import BothMain.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase AProto AMalloc_iface AProg_kit AHarness_iface Strnlen_iface ADriver_iface AD_main AMain_asm.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AHarness_bm.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AD_main_pack () := "C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_entryC4ELinuxProcessSemantics?LinuxProcessSem3RunBvalid_input_eitherC4ARocqVerifyHarness?AgentSubmission8BothMain:amain_openC4ELinuxProcessSemantics?LinuxProcessSem3Run5en_spC5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff7atop_ofC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPI47Corelib4Init5Logic2eq00C5ARocqVerifyHarness?AgentSubmission5BothW9AMain_asm4RNG0C5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff<a_space_beg0C5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff<a_ptr_array0C5ARocqVerifyHarness?AgentSubmission4Spec;BothHandoff7resv_ofC5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps8aps_initC5ARocqVerifyHarness?AgentSubmission5BothW7AD_main:apat_mainAI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5BothW7AD_main<amain_packedC5ARocqVerifyHarness?AgentSubmission5BothW9AMain_asm=adrv_of_partsI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission4LibA6ITreeA3alwI4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsC5ARocqVerifyHarness?AgentSubmission5BothW4BImg9b_init_pcC5ARocqVerifyHarness?AgentSubmission5BothW4BImg7b_phdrsI5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI5ARocqVerifyHarness?AgentSubmission4Spec<AsanProgDeps3APS00".   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Packed.
  Variable AI : AMallocIface.
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv (aci AI).
  Hypothesis CLI_CI : forall iv, In iv cli_img_ranges -> In iv (aci AI).
  Hypothesis CI_WF : forall iv, In iv (aci AI) -> 0 <= fst iv.
  Hypothesis DMALLOC : dmalloc_stmt AI.
  Hypothesis DFREE : dfree_stmt AI.
  Hypothesis DFREEN : dfree_null_stmt AI.
  Hypothesis ASHENV : ashenv_law AI.
  Hypothesis FUZZ : fuzz_oneA_stmtB AI rng_fs.
  Hypothesis HSTRN : strnlen_a_stmt.

  (* [comment removed for export] *)
  Corollary adrv_of_walks : forall (A0 : (nat -> Z) -> alw),
    (forall en inp w V m ms mo,
       valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp -> amain_open en inp w V m ms mo ->
       atop_of (en_sp en) = ATOP ->
       exists L, apat_mainA AI rng_fs L (RNG0 A0 V mo) inp (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ms) ->
    adrv_stmt A0.
Proof.
ltac2:(KReplay.run1 (kr_t_AD_main_pack ()) ["CANSEC1"; "Packed"] "h01Lh13inph22msh32A0h44APATh52HPh63RNGh71Vh82enh91mh:2moh;2s0h<1wp;1p;3p;7p;4p;8p;2p;Cp;5p-1p10000p4p710p8g000Gj10Tg000lj13Tg001Jj12Tg001mj14Tg002Oj3ETg003Lj3<Tg004Dj1;Tg005Cj75Tg006;j16Tg006mj17Tg007jj18Tg008`j39Tg009:j3:Tg00:3j1DTg00;5j1CTg00<7j1BTg00=4j4=Tg00>3j81j3?Tg00?0j2>Tg00?JlC@Tg00@Ij5ATg00AKg00AjR0[R1g00BH[g00C<g00D4R2g00Dng00EN#0#0#0R3#0#0#0#3#2%33#2#4[g00F3R3g00G:g00H0g00Heg00I^3Ef6R4f5R53<%;4f8R6f7P4P5f4R7f3R8f2R9F5f9#6#7p,2rcR:#8R;590g00JUR0P:p,2AIR<p,6rng_fsR=f0R>f<?:65f:%D6%C6%B6P;C=P4G1X00'>[[[[]:]2]9^71]<]1]8f1R1P:A?:<=P>g00KOg00LHP:P<P=P7P8P9P1P>G1P:P<P=p,;rng_fs_monop,6DRV_CIp,6CLI_CIp,5CI_WFp,7DMALLOCp,5DFREEp,6DFREENp,6ASHENVp,4FUZZp,5HSTRNP5P7P8P9P1P>MC@W5X23W;X12W6X00DAW4W3o"). Qed.
End Packed.
End CANSEC1.
