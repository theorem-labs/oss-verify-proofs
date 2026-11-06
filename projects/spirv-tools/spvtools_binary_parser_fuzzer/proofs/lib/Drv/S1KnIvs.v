(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec SeqExec StoreOk SymExec SymExec2 SymExec2Sound.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1Cells S1RKn.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_S1KnIvs () := "C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstC46Stdlib5Lists4List7existsbI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib3Drv5S1RKn8rimg_ivsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv7S1KnIvs9kn_of_ivsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv7S1KnIvs7hdr_ivsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv7S1KnIvs6ivs_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv6S1Exit9img_clearC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~K47Corelib5Lists7ListDef6Forall01K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC46Stdlib5Lists4List7forallbC47Corelib4Init9Datatypes9andb_propI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6leb_leC46Stdlib5Lists4List?Forall_cons_iffK59OSSVerify5KrLib8SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic3and01K47Corelib5Lists7ListDef6Forall02C47Corelib4Init9Datatypes8list_indC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C69OSSVerify6KrSpec8ProblemscSrc_spirv_tools_spvtools_binary_parser_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I46Stdlib5Lists4List6Exists00c59OSSVerify5KrLib3Drv7S1KnIvs;know_of_ivsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib3Drv7S1KnIvs6kn_ivsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv7S1KnIvs9kn_ivs_eqC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
Import SX2. Import SX2S.

Definition hdr_ivs : list (Z * Z) := Eval cbv in rimg_ivs.
Lemma hdr_ivs_eq : hdr_ivs = rimg_ivs.
Proof.
ltac2:(KReplay.run1 (kr_t_S1KnIvs ()) [] "p;2p;1p-1R0p10000p4p710p8P0p1000LR1p4p710p8P0P1p4p7210p8P0p1000ip4p710p8g001Ej22Tg001ej11Tg002Ej20Tg002_R0/20#1g003='0o"). Qed.

Definition kn_of_ivs (l : list (Z * Z)) : list kentry := map (fun iv => KImg (fst iv) (snd iv)) l.
Definition kn_ivs : list kentry := Eval cbv in kn_of_ivs hdr_ivs.
Lemma kn_ivs_eq : kn_ivs = kn_of_ivs hdr_ivs.
Proof.
ltac2:(KReplay.run1 (kr_t_S1KnIvs ()) [] "p;1p;2g001ej12Tg0044j11Tg002Ej20Tg004n#2g005h#1'0o"). Qed.

Definition ivs_wf (l : list (Z * Z)) : bool :=
  forallb (fun iv => (0 <=? fst iv) && (snd iv <=? 2 ^ 64))%Z l.

Section K.
  Variable E : env.
  Variable M : word -> option byte.

  Lemma know_of_ivs : forall l, ivs_wf l = true ->
    Forall (fun iv => img_clear M (fst iv) (snd iv)) l -> know_ok RSEGS E M (kn_of_ivs l).
Proof.
ltac2:(KReplay.run1 (kr_t_S1KnIvs ()) ["K"] "p'0h01li001lh12H1h21Hh32H2h43Hwfh51ai011ah61Ah72H0h81Ph91ih:2ivh;1mh<1nh=2Hch>2Hih?2Hlh@5HresthA2IHhB2hihC2loi023mapi031pi041zp;2p;1p;3p;4p;6p;5g001ER0j2YTg001eR1j1ATg006`j1>Tg007Wj3?Tg008Pj31Tg0044j1<Tg0091j4;Tg00:0j1CTg00:Pj3Jj4RTg00;Qj2ITg00<2j32Tg00<Rj1:Tg00=7j1HTg00=Uj2VTg00>2j23Tg00>Oj2=Tg00>mj3@Tg00?Ij3FTg00?lR2j25Tg00@Gj26Tg00@cj2QTg00ACj4PTg00Agj2ETg00Baj2OTg00C=j1DTg00C[j1NTg00D>j1LTg00D`j2KTg00EFj1MTg00Ehj3BTg00FBj4GTg00F]j6STg00G>j5TTg000Lj3UTg00G`j3XTg00H=j4WTg00H]f0R3g00I=3Bp=0g002_R4?U43p=9AX443p=8P4P4f1R5P3CWp=4g00I]R6/33p=71Y44R7#AR8P7%>3#0p,1MR9%93R:%83R;3?X:7R<=175g00J;R=p,1ER>P9f2R?#<C;[[R@X08%C7RA#>#0A17<Ag004nRAAJ=>9RB'IW2W4P0P4P4A27?5#>#0f3R0=27?917<P=P>P9f4RC=270#<C;[[\@^08P3140?=275#>#014C0=27?917<f5RD#7g00L0#:RE#H%:E#:RE#:#:#:RF#H'VRG,3C'=RH%7:13;G'=X:7R;=@70R:;F5%0H%0:'5P2f6R:#713DG'=#0A@7;C#0P=P>P9f7RH/4:=27D#<C;P3f8RI#713HG'=#0A@7;H#0f:RH#7R;f9/3GRJ;F5%0;%0J'5P2f;RJ#7#013HG#0P=P>P9f</4J=27H#<C;P3f=RH#7#013HG#0P21353#016?5[RH165313?5#0RJ[160?\J1Q53P5n2001000000120000000X;4X<4RJPH^;4^<4RHP3P6f@R;P?O3166;PJPHP3fARHPGP0O316HGg00LUp4p710RHp-0\3RJ%A?R;P2A2053910?P0P?O1A1C05'5[RKP?P5O1A10?3'5A2C?591C0RL[PCP0O1A1DC?'5\LP0P?P5P3CPP5n2001000000120000000W0X55W8W6PK^0;^55^8J^6HP3P7P<fDRHfCRJ'4R;fBRKf?R?O5%9;%8;5?9A17<K'5P2fER2/4HRK#9%8K5?9A17<JP=P>P9fFRJ/42=27H#<C;P3fGRH/4JR2#9%825?9A17<JPAPBfIRBfH'4R<#9R2%8<R<'ERK%AAR;^08P1P7P;P3%CA%95%85'EP0P3O152An10110000020020101100X08p?1000102PHO1166216<GR<fJ/4BRB#9/63%8B,O3'5RB%DE#NRE#LP9%DF/K5O1%ME3B[^94RE'5PIP<PEP:P0P5P3O2X>BX94CGCGP=P>P9PKCRePJP?P3O2ESW?W=P5P3O2n2001000000121000000b2b3b1b3b7b3W1W7P5P3O2n2001000000121000000b1W@W1P5P3O2n2001000000121000000b4W2W4XA@X08XB4XC4P5P3O2n2001103000121104104X57P3DTW0o"). Qed.

  Lemma know_ivs : Forall (fun iv => img_clear M (fst iv) (snd iv)) hdr_ivs -> know_ok RSEGS E M kn_ivs.
Proof.
ltac2:(KReplay.run1 (kr_t_S1KnIvs ()) ["K"] "h01Hh12ivh21lp;2p;3p;1p;4p;6g001Ej2<Tg000Lj3;Tg00G`j30Tg007Wj31Tg008Pj3:Tg001ej12Tg0044j13Tg0091j44Tg002Ej25Tg006`j16Tg00Ehj37Tg00M2j38Tg00Mnj69Tg002_R0/<0R1p,1MR2f0R39;00A000331X11g005hR13:g004n#2R0%31g00J;p,1EP2P3C4X20g00H]R0g00I=R2'5%61=702d=813g00NLg00OCE9W0o"). Qed.

End K.
