(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim ShapeAlg SpinAlg AgentLib Hoare SumsLib
AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanPlanSound2K AsanPlanSoundSumsK Jb0PlanImagesK AsanInitK
AsanNodesExtraDefsK AsanNodesExtraK Jb0StartupK AsanXAllKB0 AsanAddrIsInMemWalkKB0 AsanMaxVAWalkKB0.
Import ListNotations.
Import AX2K. Import AX2SK. Import APCK. Import APK. Import APSK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Jb0StartupClosedK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanInitK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanMaxVAWalkKB0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanNodesExtraK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Hoare."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0DefsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Jb0StartupClosedK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["0BFUEL"; "1None"; "1bool"; "1cons"; "1list"; "1nil"; "1option"; "1true"; "2I"; "2and"; "2eq"; "2ex"; "0E"; "0FUEL"; "0FULL"; "0HS"]; ["0IT0"; "0KC0"; "3init_config"; "4Model"; "4m_fs"; "5bvmap"; "0R"; "6LIMIT"; "6SINV0"; "6argH0"; "6inp"; "7asan_maxva_entry"; "8aim_spec"; "9COk"; "9NX0"; "9acs"]; ["9check"; "9cres"; "9hole_only"; "9loopctx"; "9pc"; "9plan"; "9shape"; "9xnode"; ":cfg_of"; ":cs_ok"; ":x_stmt"; ";env"; "<msteps"; "=at_"; "=regs_agree"; ">AIM_ASAN0"]; [">APH0"; ">ASAN0"; ">ASEGS0"; ">XB0"; ">XE0"; ">XN0"; ">X_MAXVA_ASAN0"; "?asanreflect_fx"; "@getr"; "@mkst"; "Asrealizes"; "Binit_pc"; "CIn"; "Dle"; "Dlt"; "Dpow"]; ["Dsub"; "0T"; "0abrt"; "0argv"; "0brk0"; "0cs0"; "0envp"; "0fs"; "0gid"; "0groups"; "0hw"; "0mbase"; "0mem"; "0model"; "0net"; "0nofile"]; ["0p"; "0r"; "0rdraw"; "0regs"; "0regs'"; "0rom"; "0s"; "0scfg"; "0sigmask"; "0sp"; "0stdin"; "EBV"; "EZ_to_bv"; "Ebv"; "Ebv_unsigned"; "0uid"]; ["0urnd"; "0x"]]).
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Open Scope Z_scope.
Lemma as0_AIMW : ltac2:(TCodec.tc2 tcn__Jb0StartupClosedK "4&L&QB&Q?%3221").
Proof. exact asan_addrisinmem. Qed.
Lemma as0_maxva_entry_eq : ltac2:(TCodec.tc2 tcn__Jb0StartupClosedK "9':'RMyR0%211&RL&QF%2241&K%83521").
Proof. apply bv_eq. reflexivity. Qed.
Lemma as0_SMEARW : ltac2:(TCodec.tc2 tcn__Jb0StartupClosedK "SK'RMyR0%211'6y8%511%311p051&Ey5%2218':&QHr2(RK+:(8%33821%6251r1%93B21'9&QM&QO+2+Q>%3221&RN%12K?%7231&QN+Q?%9281%3251%=251';'Q<&QB&QI&QGr5&Q=&RL&QF%22Q;1z%5221r7r6%;5:9321+UD%:271%>5=Q1154%A3@41%Q:2Q3Q5&R0+1%22I1%@2QI1%Q@3QI51+;%Q?3QD1Q=%QB2Q;1+_oooooooooooO%F2QO1%QF3QO31+<%QE3QJ1QC%QH2QA1+SV\icV\icV\iC%L2R51%QL3R531+=%QK3R01QI%QN2QG1+nSh_QlW`nSh?%Q22R;1%R23R;31+>%R13R61QO%R42QM1+RPXQPTP`RPX1%Q82RA1%R83RA31+?%R73R<1R5%R:2R31+WoonPPPPPPPP0%Q>2RG1%R>3RG31&Q>%RK1RB&QL(3(5%114%335;1%436B1%537I1%638Q01%739Q71%83:RD1'4%11</031%=3>RF1qU4?1%A31R3RH%RG2C1%RH2J1%RI2Q11%RJ2Q81%RK2Q?1%RL2QF1%RM2QM1qU:S91%RA2S:1p0RC1p0S21pV4SE1pU8S>1pU<SB1pTJSC1").
Proof.
intros mem rom regs x Hx Hr. rewrite as0_maxva_entry_eq. rewrite at_0. exact (asan_smearva mem rom regs x Hx Hr).
Qed.
Section Closed.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Variable sp brk0 : word.
Variable rdraw : EntryDraw.
Variable argv envp : list (list byte).
Variables uid hw : word.
Variable fs : Fs.Fs.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
#[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
#[local] Notation LIM := AsanInitK.LIMIT.
Lemma as0_X_ALL : ltac2:(TCodec.tc2 tcn__Jb0StartupClosedK "G'Q7&Q:&QBvRG&QA&N&G&H&Q@vRIvRBvR4vR3vR6vROvR:%9887654321&I%17:986543vR7r1%D9CBA@?5321pV4F1").
Proof. exact (asan_X_ALL scfg sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit). Qed.
Variable IT0 : itab.
Hypothesis IT0_ok : itab_sound ASEGS0 IT0.
Variable HS : nat -> option acs.
Variable T : Fs.Fs -> TSet.
Hypothesis T_nil : forall fs', T fs' [].
Hypothesis HS_sound : holes_stmt ASEGS0 scfg ASAN0 LIM HS SINV argH (HOLES T) fs.
Variables KC0 BFUEL FUEL : nat.
Theorem as0_stage_hole : ltac2:(TCodec.tc2 tcn__Jb0StartupClosedK "RE'Q5'O'Q6':'Q1&Q0&QBv@&QA&N&G&QE&QD&QCv?vAv0v=(1'Q3%211r2r3%B?A@?>=<;:9876321(Mr1%211%H3G41'2&Q2%119(7%M3421'Q;&Ey5'RMyR0%211%5241'6y8%611%311p061'C'Q9&H&Q@vRIvRBvR4vR3vR6vROvR:%9887654321&I%17:986543vR7r4r8%@;QHQFQD64321Q8Q9Q5'QJvRG&Q8&Q4r9%211%45QO91Q?Q@vR1&D%11QC%311%;4R4:51p0=1pTLO1pNQ11pQ>Q71pJQ>1p0Q@1p0QF1pU>R@1pT<RB1pU2RD1").
Proof.
exact (stage_hole scfg Halloc as0_AIMW as0_SMEARW sp brk0 rdraw argv envp uid hw fs Hsp Hva IT0 IT0_ok HS T T_nil HS_sound as0_X_ALL KC0 BFUEL FUEL).
Qed.
End Closed.
Section ClosedStartup.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Variable sp brk0 mbase : word.
Variable rdraw : EntryDraw.
Variable argv envp : list (list byte).
Variable fs : Fs.Fs.
Variable stdin : InputStream.
Variables uid gid hw : word.
Variable groups : list word.
Variable net : NetQueue.
Variables nofile sigmask : word.
Variable abrt : bool. Variable urnd : InputStream.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hbrk : valid_brk ASEGS0 brk0.
Hypothesis Hmb : valid_mmap_base mbase.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Huid : valid_id uid.
Hypothesis Hhw : valid_hwcap hw.
#[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
#[local] Notation LIM := AsanInitK.LIMIT.
Variable IT0 : itab.
Hypothesis IT0_ok : itab_sound ASEGS0 IT0.
Variable HS : nat -> option acs.
Variable T : Fs.Fs -> TSet.
Hypothesis T_nil : forall fs', T fs' [].
Hypothesis HS_sound : holes_stmt ASEGS0 scfg ASAN0 LIM HS SINV argH (HOLES T) fs.
Variables KC0 BFUEL FUEL : nat.
Variable startup_plan : plan.
Variable startup_shape : shape.
Hypothesis startup_cert :
check ASEGS0 IT0 ASAN0 NX0 LIM XN0 XE0 XB0 HS KC0 BFUEL FUEL None asan0_init startup_plan = COk startup_shape.
Hypothesis startup_ho : hole_only startup_shape = true.
Theorem as0_startup_hole_c : ltac2:(TCodec.tc2 tcn__Jb0StartupClosedK "N'QJ&QBvRG&B&QK&Q@vRIvR4vR;vRB&G&JvR3vR6vR7vRJvROvR8vR:vR9vR>vR?vRHvR2vS0%>==<;:987654321%G9IFEDCBA@1vR1%11>%M4LK31").
Proof.
eapply (as0_startup_hole scfg Halloc as0_AIMW as0_SMEARW); try eassumption.
exact (as0_X_ALL scfg sp brk0 rdraw argv envp uid hw fs Hsp Hva Hve Hfit).
Qed.
End ClosedStartup.
