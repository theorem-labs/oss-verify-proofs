(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode Image InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prelim Monad MSafe MSafeP STree Malloc Stdio PState Prog KInv KLink KEv StepB Gap ModelInv ImgFacts LB_Main.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ModelOK () := "C47Corelib7Classes?RelationClasses9ReflexiveC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6MSafeP>mspecP_programC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State<reserved_topC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC4ELinuxProcessSemantics?LinuxProcessSem5State:live_bytesK4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_entryC4ELinuxProcessSemantics?LinuxProcessSem3RunBvalid_input_eitherC59OSSVerify5KrLib4Spec7LB_Main<never_forcedC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog4progC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8TopLevel3mo0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5StepB3tnfC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem3Run9valid_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run?valid_mmap_baseI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC49OSSVerify5KrLib8TopLevelBvalid_entry_eitherC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloC4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs8valid_fsC4ELinuxProcessSemantics?LinuxProcessSem5State;in_image_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs@fs_keys_relativeC4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_credsC4ELinuxProcessSemantics?LinuxProcessSem5State9in_nofileC4ELinuxProcessSemantics?LinuxProcessSem3Run<valid_nofileC4ELinuxProcessSemantics?LinuxProcessSem3Run=valid_sigmaskC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_hwcapC4ELinuxProcessSemantics?LinuxProcessSem5State:in_va_sizeC4ELinuxProcessSemantics?LinuxProcessSem3Run=valid_urandomI47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib4Spec4Prog6argv_ZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image9reservedZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6PState7ps_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog9prog_withC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelK47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib4Spec8ModelInv2GIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8ModelInv<argv_Z_shortC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8ModelInv=prog_with_GIPC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib4Spec8ModelInv7GI_initC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run5en_spC4ELinuxProcessSemantics?LinuxProcessSem3Run6en_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run<en_mmap_baseC59OSSVerify5KrLib3Lib5ITreeDleaves_unreachable_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tsafeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_fitsI47Corelib4Init5Logic2eq00C59OSSVerify5KrLib3Lib5ITree5ebindC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nsafeC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I4ELinuxProcessSemantics?LinuxProcessSem5State6VaSize00K4ELinuxProcessSemantics?LinuxProcessSem5State6VaSize02I47Corelib4Init9Datatypes4unit00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C4ELinuxProcessSemantics?LinuxProcessSem5State<brk_aslr_maxK47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec6Malloc4PGSZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes@alloc_ceiling_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec3Gap5FLOORC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiI47Corelib4Init9Datatypes9Empty_set00I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State>stack_max_sizeC59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec7ModelOK=prog_model_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg9p_init_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg7p_phdrsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateBsource_alloc_limitC59OSSVerify5KrLib4Spec8ImgFacts=top_pos_plainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8ImgFacts:ceil_plainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8ImgFacts;floor_plainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8ImgFacts:resv_plainC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8ImgFacts5lim_pC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg5usegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg9u_init_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Ubsan4UImg7u_phdrsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateBtarget_alloc_limitC59OSSVerify5KrLib4Spec8ImgFacts=top_pos_ubsanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8ImgFacts:ceil_ubsanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8ImgFacts;floor_ubsanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8ImgFacts:resv_ubsanC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8ImgFacts5lim_uC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Theorem prog_model_ok : forall segs rs pc ph lim en inp,
  0 < reserved_top (segments_reserved segs) ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
  reserved_top (segments_reserved segs) + brk_aslr_max + 2^34 + 8 * PGSZ <= FLOOR ->
  live_bytes (segments_reserved segs) <= 2^30 -> 2^31 <= lim ->
  valid_entry (mkImage segs pc ph) en inp -> valid_input_either inp ->
  leaves_unreachable_m nstep (Prog.prog segs rs inp en) (mo0 segs lim en inp)
  /\ tsafe nstep nsafe (Prog.prog segs rs inp en) (mo0 segs lim en inp).
Proof.
  intros segs rs pc ph lim en inp Hpos Hceil Hfloor Hresv Hlim Hen Hinp.
  pose proof (never_forced segs rs pc ph lim en inp Hpos Hceil Hfloor Hresv Hlim Hen Hinp) as HNF.
  destruct en as [sp brk0 mbase dr]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hinp) in Hen.
  destruct Hen as ((HspL & HspH & _) & Hbrk & _ & _). destruct Hinp as (Hargv & _ & _ & _).
  revert HNF. unfold prog, prog_itree, mo0, entry_atop. cbn [en_brk en_mmap_base en_sp]. intros HNF.
  apply (mspecP_program (GI []) (prog_with rs (argv_Z (in_argv inp)))).
  - apply prog_with_GIP. apply argv_Z_short. exact Hargv.
  - eapply GI_init; [exact Hbrk| exact Hpos| split; [exact HspL| exact HspH]| reflexivity| exact Hceil].
  - exact HNF.
Qed.

Theorem prog_model_ok_plain : forall rs en inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  leaves_unreachable_m nstep (Prog.prog psegs rs inp en) (mo0 psegs source_alloc_limit en inp)
  /\ tsafe nstep nsafe (Prog.prog psegs rs inp en) (mo0 psegs source_alloc_limit en inp).
Proof.
ltac2:(KReplay.run1 (kr_t_ModelOK ()) [] "h02Heh12Hih22enh33inph42rsp;3p;1p;>g00:Nj34Tg00;Kj33Tg00<Cj10Tg01=kl>2Tg01>jR0f4R1g01?_R2g01@XR3g01AOf3R4f2R5g01BPg01CPg01DMg01EKg01FHf1R6f0R7M>2p=1g00lAg011hg012`A4023?367%06P1P4P5P6P7D1W1W0W3W2W4o"). Qed.

(* [comment removed for export] *)
Theorem prog_model_ok_plain_L : forall L rs en inp, 2^31 <= L ->
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  leaves_unreachable_m nstep (Prog.prog psegs rs inp en) (mo0 psegs L en inp)
  /\ tsafe nstep nsafe (Prog.prog psegs rs inp en) (mo0 psegs L en inp).
Proof.
ltac2:(KReplay.run1 (kr_t_ModelOK ()) [] "h02HLh12Heh22Hih31Lh42enh53inph62rsp;1p;2p;3p;>g006Wj19Tg007<j11Tg008Sj10Tg0098j22Tg0087j28Tg00:Nj37Tg00;Kj34Tg00<Cj13Tg01=kl>6Tg01>jR0f6R1g01?_R2g01@XR3f5R4f4R5f3R6g01BPg01CPg01DMg01EKf2R7f1R8f0R9M>6p=5g00lAR:g011hg012`g014UR;#9#1%0;#0#0#0#1'2/86A7023?478%37P4P1P5P6P7P8P9F5W2W1W0W5W4X6:W3o"). Qed.

Theorem prog_model_ok_ubsan : forall rs en inp,
  valid_entry (mkImage usegs u_init_pc u_phdrs) en inp -> valid_input_either inp ->
  leaves_unreachable_m nstep (Prog.prog usegs rs inp en) (mo0 usegs target_alloc_limit en inp)
  /\ tsafe nstep nsafe (Prog.prog usegs rs inp en) (mo0 usegs target_alloc_limit en inp).
Proof.
ltac2:(KReplay.run1 (kr_t_ModelOK ()) [] "h02Heh12Hih22enh33inph42rsp;3p;1p;>g00:Nj34Tg00;Kj33Tg00<Cj10Tg01=kl>2Tg01G@R0f4R1g01H5R2g01HnR3g01Ief3R4f2R5g01Jfg01Kfg01Lcg01Mag01N^f1R6f0R7M>2p=1g00lAg011hg012`A4023?367%06P1P4P5P6P7D1W1W0W3W2W4o"). Qed.
