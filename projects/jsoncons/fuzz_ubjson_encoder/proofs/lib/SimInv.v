(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)

From Stdlib Require Import List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_SimInv () := "I47Corelib4Init9Datatypes4list00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00I4ELinuxProcessSemantics?LinuxProcessSem3Run4star00C4ELinuxProcessSemantics?LinuxProcessSem3Run8star_indI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C47Corelib4Init5Logic3notC4ELinuxProcessSemantics?LinuxProcessSem3Run=reaches_errorI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SimInv8star_invC13~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun?no_error_coexecK4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun:omni_corunI47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C4ELinuxProcessSemantics?LinuxProcessSem7OmniRun<never_errorsC4ELinuxProcessSemantics?LinuxProcessSem3Run3runC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence7modeledC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<img_segmentsC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun7coveredC4ELinuxProcessSemanticsEEquivalenceDefinition?OmniEquivalence;modeled_iffc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6SimInvBno_error_run_corunC13~~~C4ELinuxProcessSemantics?LinuxProcessSem7OmniRunDnever_errors_coveredC4ELinuxProcessSemantics?LinuxProcessSem7OmniRun=coexec_conseqI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00".

Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
ltac2:(KReplay.run1 (kr_t_SimInv ()) [] "h04HInvh11ch22c'h32trh45Hstarh55Hsteph63Invh73evsh84segsh91Hh:7IHHstarh;2c1h<2c2h=2c3p;1p;4p;9g0000j13Tg000Pj12Tg001Fj40Tg002:j41Tg002ml94Tg003b#3R0g004aR1p-0[R2g005V#3R3f3R4f2R5O1f5R6P4P5f1R7#2C0P6P5O1[[^21]7^11R6f4R8P5O1f6R9P4P5P7C1f7R:f9P5O1f:P7O1]0X21X33X11P:f0R;O1P;W0X11f<P8P4%25C0f=R<P4P5P7C1P<P8O1f>R<P4O1]0P<P:O1P7P<f8P:P9P;P4O5O1W0W:W4W9X=1X33X<1X73X;1P8P4P5P;P7M94W4W0X21X33X11X56X62X80P5P7P;O3W5W6W8o"). Qed.

(* [comment removed for export] *)
Lemma inv_no_reaches_error (segs : list Segment) (Inv : config -> Prop)
  (Hstep : forall c evs c', Inv c -> sstep segs c evs (SNext c') -> Inv c')
  (Hnoerr : forall c evs, Inv c -> ~ sstep segs c evs SError) :
  forall c, Inv c -> ~ reaches_error segs c.
Proof.
ltac2:(KReplay.run1 (kr_t_SimInv ()) [] "p'0h03evsh11ch21Hh36Hnoerrh45Hsteph53Invh62c'h74segsh82trh94HInvh:3Hssh;5Hstari001xp;1p;4p;2p;8g0000j14Tg000Pj19Tg001Fj45Tg006Lj16Tg006ej28Tg002:j41Tg007_R0j22Tg008:R1j23Tg008Tj87Tf2R2f1R3f0R4g009^C5p=0g003b#4R5g004aR6p-0[R7g005V#4R8f3R9P2O1f5R:P9P2%93C5P:P2O1[[^66]0^16R;P9P3O1A0:23#6[^08^16R<P9P4O118:3R=P1P8f9R>P:P2P3C1A0>34'2X08,38X16,36X88g00:TR?P4f;R@f7RAP2P3C1A0@34'2X08,38X16,36P1P6f<RBf8RCP9P3C1A0B34'2X08,38X16P?P4f>RBf:P:P3C1A0B34'2X08,38P1P8f?R1P@f6P2C1A0124'2X08P?P4fAR1f=RDPCf4REC1A01E4'2P0fBR0PBP>P:C1A00:3P?P4fDR?f@P@PAC1fERA?0CEfCP>P:fFPAP?P0PDP>P1P3G7P4O4W:W;P3P4O2n2001000000120000000W2X08P3P4O2n2001000000120100000W2X66P3P4O2n2001000000120100000W2X88P3P4O2n2001000000120100000W2%6=eW9X16X3<X4;X57X75P9P2P3P4O4W3W4W5W7o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_SimInv ()) [] "h01Hh14brk0h23inph33limh42mbh52pch62phh73rndh84segsh92spp;1p;9p;2p;3p;4p;5g0000j1:Tg00;1j10Tg00;Vj13Tg00<4j12Tg00<Wl91Tg006ej29Tg006Lj18Tg00=Oj34Tg00>Oj35Tg00?Lj46Tg00@Dj57Tg003b#:g00A?g00A]g00B]#0#0#0#0#0#0#3#2R0g00CBg00DBg00D`f8R1P1f7R2f6R3f5R4f4R5f3R6f2R7f1R8f0R9M91'9#8f9R:P:P1P2P3P4P5P6P7P8M91;49A5:12P7P3P4P5P6C6P8g00EZD7eW0W2W3W7X40X10W9W6W5W8o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma no_error_run_modeled :
  forall (segs : list Segment) (pc : N) (ph : PhdrInfo) (sp brk0 mb : word) (rnd : EntryDraw)
         (lim : Z) (inp : ProcInput),
  ~ reaches_error segs (init_config segs pc ph sp brk0 mb rnd lim inp) ->
  Equivalence.modeled (run (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof.
ltac2:(KReplay.run1 (kr_t_SimInv ()) [] "h03inph13limh22enh33imgh41Hh52H0h64brk0h72mbh82pch92phh:3rndh;4segsh<2spp;1p;9p;2p;4p;5p;3p;:p;6g0000j1ATg00;1j10Tg00;Vj18Tg00<4j17Tg00<Wl96Tg006ej2;Tg006Lj1:Tg00FWj43Tg00GGj12Tg00HIj14Tg00IKj11Tg00@Dj55Tg00JCj49Tg00>Oj3@Tg00?Lj4?Tg00KMl:>Tg00Laj1<Tg00Mfj6=Tg003b#Ag00A?g00A]g00B]#0#0#0#0#0#0#8#7R0g00CBg00DBR1g00D`R2f8R3P3f7R4f6R5f5R6f4R7f3R8f2R9f1R:f0R;M96';#:g00NdR<g00OaR=g007_P8P9P:P;C3#2P7P8P9P:%47#1D5R>[P8P9P:P;%48#1D5P7P8P9P:C3#2[R?P6P7P8P9C3#2\>P8P9P:P;C9P;n2001000000120000000X02W2X11W3P?^02^2=^11^3<P;f:R;f9R<;@3R1P8P4P5P6P7C?R=P9P;P;P<P3P4P5P6P7P8P9M96g00EZ%1;P;P<P3P4P5P6P7P8P9P:M:>%<;E=P1P8P=P9%41#1D5eO5b5W4W0W1W:X70X60W<W9W8W;o"). Qed.
