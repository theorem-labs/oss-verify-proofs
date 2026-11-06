(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Lib Require NoCache.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_SimInv () := "I47Corelib4Init9Datatypes4list00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00I4ELinuxProcessSemantics?LinuxProcessSem3Run4star00C4ELinuxProcessSemantics?LinuxProcessSem3Run8star_indI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C47Corelib4Init5Logic3notC4ELinuxProcessSemantics?LinuxProcessSem3Run=reaches_errorI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00c59OSSVerify5KrLib6Common6SimInv8star_invC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun?no_error_coexecK4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:omni_corunI47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun<never_errorsC4ELinuxProcessSemantics?LinuxProcessSem3Run3runC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence7modeledC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<img_segmentsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7coveredC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalence;modeled_iffc59OSSVerify5KrLib6Common6SimInvBno_error_run_corunC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRunDnever_errors_coveredC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=coexec_conseqI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00".   (* [comment removed for export] *)

Import ListNotations.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac norm_fd32 :=
  repeat match goal with
         | |- context [fd32 AT_FDCWD] =>
             change (fd32 AT_FDCWD) with AT_FDCWD32
         | H : context [fd32 AT_FDCWD] |- _ =>
             change (fd32 AT_FDCWD) with AT_FDCWD32 in H
         | |- context [fd32 ?x] => change (fd32 x) with x
         | H : context [fd32 ?x] |- _ => change (fd32 x) with x in H
         end.

(* [comment removed for export] *)
Ltac fd32_ok :=
  solve [ reflexivity
        | assumption
        | apply fd32_lt31; assumption
        | apply fd32_id; assumption
        | apply fd32_lt31; lia
        | apply fd32_id; lia ].

(* [comment removed for export] *)
Lemma star_inv (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c') :
  forall c tr c', Inv c -> star segs c tr c' -> Inv c'.
Proof.
ltac2:(KReplay.run1 (kr_t_SimInv ()) [] "h04HInvh11ch22c'h32trh45Hstarh53evsh61Hh75Hsteph87IHHstarh93Invh:2c1h;2c2h<2c3h=4segsp;1p;4p;9g0000j13Tg000Pj12Tg001Fj40Tg002:j41Tg002ml94Tg003b#3g004aR0p-0[g005V#3R1f3R2f2R3O1f5R4P2P3f1R5#2C0P4P3O1[[^20]5^10f4R4P3O1f6R6P2P3P5C1f7R7f9P3O1f:P5O1]0X20X31X10P7f0R8O1P8W0X10f<P4P2%23C0f=R9P2P3P5C1P9P4O1f>R9P2O1]0P9P7O1P5P9f8P7P6P8P2O5O1W0W8W4W6X<0X31X;0X51X:0P4P2P3P8P5M94W4W0X20X31X10W7W9W=o"). Qed.

(* [comment removed for export] *)
Lemma inv_no_reaches_error (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c')
  (Hnoerr : forall c evs, Inv c -> ~ sstep segs c evs SError) :
  forall c, Inv c -> ~ reaches_error segs c.
Proof.
ltac2:(KReplay.run1 (kr_t_SimInv ()) [] "p'0h03evsh11ch21Hh32c'h42trh54HInvh66Hnoerrh73Hssh85Hstarh95Hsteph:3Invh;4segsi001xp;1p;4p;2p;8g0000j14Tg000Pj19Tg001Fj45Tg006Lj16Tg006ej28Tg002:j41Tg007_R0j22Tg008:R1j23Tg008Tj87Tf2R2f1R3f0R4g009OC5p=0g003b#4g004aR5p-0[g005V#4R6f3R7P2O1f5R8P7P2%93C5P8P2O1[[^35]0^15P7P3O1A0823#6[^06^15P7P4O11883R9P1P6f9R:P8P2P3C1A0:34'2X06,36X15,35X46g00:ER;P4f;R<f7R=P2P3C1A0<34'2X06,36X15,35P1P5f<R>f8R?P7P3C1A0>34'2X06,36X15P;P4f>R>f:P8P3C1A0>34'2X06,36P1P6f?R1P<f6P2C1A0124'2X06P;P4fAR1f=R2P?f4R7C1A0174'2P0fBR0P>P:P8C1A0083P;P4fDR;f@P<P=C1fER=?0?7fCP:P8fFP=P;P0P2P:P1P3G7P4O4W7W8P3P4O2n2001000000120000000W2X06P3P4O2n2001000000120100000W2X35P3P4O2n2001000000120100000W2X46P3P4O2n2001000000120100000W2%69eW5X15W6W9W:W;o"). Qed.

(* [comment removed for export] *)
Lemma inv_coexec (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c')
  (Hnoerr : forall c evs, Inv c -> ~ sstep segs c evs SError) :
  forall c, Inv c -> OmniRun.coexec segs c never_errors.
Proof.
  cofix CH. intros c HInv.
  destruct (m_halted (cfg_model c)) as [code |] eqn:Hh.
  - apply coexec_halt; [rewrite Hh; discriminate | exact (fun h => h)].
  - apply coexec_step; [exact Hh | |].
    + intros evs Hss. exfalso. exact (Hnoerr c evs HInv Hss).
    + intros evs c' Hss. exact (CH c' (Hstep c evs c' HInv Hss)).
Qed.

(* [comment removed for export] *)
Lemma no_error_run_corun :
  forall (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw)
         (lim : Z) (inp : ProcInput),
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) ->
  omni_corun (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp never_errors.
Proof.
ltac2:(KReplay.run1 (kr_t_SimInv ()) [] "h01Hh14brk0h23inph33limh42mbh52pch62phh73rndh84segsh92spp;1p;9p;2p;3p;4p;5g0000j1:Tg00:bj10Tg00;Gj13Tg00;ej12Tg00<Hl91Tg006ej29Tg006Lj18Tg00=@j34Tg00>@j35Tg00?=j46Tg00@5j57Tg003b#:g00A0g00ANg00BN#0#0#0#0#0#0#3#2R0g00C3g00D3g00DQf8R1P1f7R2f6R3f5R4f4R5f3R6f2R7f1R8f0R9M91'9#8f9R:P:P1P2P3P4P5P6P7P8M91;49A5:12P7P3P4P5P6C6P8g00EKD7eW0W2W3W7X40X10W9W6W5W8o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma no_error_run_modeled :
  forall (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw)
         (lim : Z) (inp : ProcInput),
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) ->
  Equivalence.modeled (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
ltac2:(KReplay.run1 (kr_t_SimInv ()) [] "h03inph13limh22enh33imgh41Hh52H0h64brk0h72mbh82pch92phh:3rndh;4segsh<2spp;1p;9p;2p;4p;5p;3p;:p;6g0000j1ATg00:bj10Tg00;Gj18Tg00;ej17Tg00<Hl96Tg006ej2;Tg006Lj1:Tg00FHj43Tg00G8j12Tg00H:j14Tg00I<j11Tg00@5j55Tg00J4j49Tg00>@j3@Tg00?=j4?Tg00K>l:>Tg00LCj1<Tg00MHj6=Tg003b#Ag00A0g00ANg00BN#0#0#0#0#0#0#8#7R0g00C3g00D3R1g00DQR2f8R3P3f7R4f6R5f5R6f4R7f3R8f2R9f1R:f0R;M96';#:g00NFR<g00OCR=g007_P8P9P:P;C3#2P7P8P9P:%47#1D5R>[P8P9P:P;%48#1D5P7P8P9P:C3#2[R?P6P7P8P9C3#2\>P8P9P:P;C9P;n2001000000120000000X02W2X11W3P?^02^2=^11^3<P;f:R;f9R<;@3R1P8P4P5P6P7C?R=P9P;P;P<P3P4P5P6P7P8P9M96g00EK%1;P;P<P3P4P5P6P7P8P9P:M:>%<;E=P1P8P=P9%41#1D5eO5b5W4W0W1W:X70X60W<W9W8W;o"). Qed.
