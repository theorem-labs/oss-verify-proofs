(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatSim ShapeAlg SpinAlg AgentLib Hoare SumsLib
AxSymExec3K AxSymExec3SoundK AxSymRun3K AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanPlanSound2K AsanPlanSoundSumsK Ja0PlanImagesK AsanInitK
AsanNodesIfaceK AsanNodesMmLibK AsanNodesMmAK AsanNodesMmBK AsanNodesExtraDefsK AsanNodesExtraK.
Import ListNotations.
Import AX2K. Import AX2SK. Import APCK. Import APK. Import APSK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__Ja0StartupK () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Fs."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanInitK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanK.APK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AsanPlanSoundK.APSK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymExec3K.AX2K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.AxSymRun3K."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0DefsK."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0StartupK.As0."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Ja0StartupK.As0.Stage."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SpinAlg."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M."; "stdpp.bitvector.definitions."], [["0BFUEL"; "1None"; "1Some"; "1bool"; "1nat"; "1nil"; "1option"; "1true"; "2eq"; "3Z"; "0E"; "0E'"; "0FS0"; "0FUEL"; "0FULL"; "0HS"]; ["0IT0"; "0JS"; "0KC0"; "0LIMIT"; "4Fs"; "5init_config"; "6Model"; "6event"; "6m_fs"; "7bvmap"; "0R"; "8E0"; "8LIMIT"; "8SINV0"; "8argH0"; "8inp"]; ["9COk"; "9NX0"; "9acs"; "9check"; "9cres"; "9hole_only"; "9hs_ext"; "9loopctx"; "9pc"; "9plan"; "9shape"; ":cfg_of"; ":cs_ok"; ":emit_stmt"; ":ext2_stmt"; ":ext_stmt"]; [":holes_stmt"; ":sd"; ";env"; "<env_agree"; "=APH0"; "=ASAN0"; "=ASEGS0"; "=XB0"; "=XE0"; "=XN0"; ">HOLES"; "?HOLES"; "@TSet"; "@t_nil"; "Asrealizes"; "Binit_pc"]; ["0SINV"; "0T"; "0abrt"; "0argH"; "0argv"; "0brk0"; "0c"; "0cs0"; "0envp"; "0fs"; "0fs'"; "0gid"; "0groups"; "0h"; "0h'"; "0hw"]; ["0mbase"; "0model"; "0net"; "0nofile"; "0p"; "0rdraw"; "0s"; "0scfg"; "0sigmask"; "0sp"; "0startup_shape"; "0stdin"; "Cbv"; "0uid"; "0urnd"]]).
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Open Scope Z_scope.
Section As0.
Variable scfg : SpuriousCfg.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis AIMW0 : aim_spec ASEGS0 AIM_ASAN0.
Hypothesis SMEARW0 : forall (mem rom : word -> option byte) regs (x : word),
getr regs 10 = x -> (2 ^ 46 <= bv_unsigned x < 2 ^ 47)%Z ->
exists regs',
msteps ASEGS0 (mkst regs (at_ (Z_to_bv 64 X_MAXVA_ASAN0) 0) mem rom) (mkst regs' (at_ (Z_to_bv 64 X_MAXVA_ASAN0) 180) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (2 ^ 47 - 1)
/\ getr regs' 11 = Z_to_bv 64 18446744073709551615 /\ getr regs' 12 = Z_to_bv 64 3689348814741910323
/\ getr regs' 13 = Z_to_bv 64 1085102592571150095 /\ getr regs' 14 = Z_to_bv 64 72340172838076673
/\ getr regs' 15 = Z_to_bv 64 9223301668110598144
/\ regs_agree (fun r : bv 5 => In r ([10; 11; 12; 13; 14; 15]%bv : list (bv 5))) regs regs'.
Lemma XE0_sound : ltac2:(TCodec.tc2 tcn__Ja0StartupK "Q0'9'QB'RLyR0%211'6y8%511%311p051!p021p0;1'3p0:1p0>1&D&Q=&QFvRG&QE&Q1r4&QHr3r2r1%:9987654321pJ<1pT8>1pT2B1pQ8O1").
Proof. intros ? ? ? ?. intros id args cs fd ps cs' E R FULL model T _ H _. discriminate H. Qed.
Lemma XB0_sound : ltac2:(TCodec.tc2 tcn__Ja0StartupK "Q0'9'QB'RLyR0%211'6y8%511%311p051!p021p0;1'3p0:1p0>1&D&Q>&QFvRG&QE&Q1r4&QGr3r2r1%:9987654321pJ<1pT8>1pT2B1pQ8O1").
Proof. intros ? ? ? ?. intros id args cs csa csb E R FULL model TA TB _ H. discriminate H. Qed.
Section Hooks.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ uE E e_sp0 <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree NX0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree NX0 E E' -> SINV E M -> SINV E' M.
Theorem XN0_sound : ltac2:(TCodec.tc2 tcn__Ja0StartupK ";&Q?&QFvRG&QE&Q1vC&QIvR0vR3v<%:9987654321").
Proof.
intros id args cs cs' E R FULL model T HC Hpre Hn Hk. unfold XN0 in Hn.
destruct (Nat.eqb id 95).
{ exact (xn_addrisinmem_sound ASEGS0 scfg ASAN0 NX0 LIMIT SINV argH FS0 Asan0_wx_nowrap asan0_in_hull asan0_hull_ok argH_high e_sp0_init argH_agree SINV_frame SINV_agree
AIM_ASAN0 AIMW0 args cs cs' E R FULL model T HC Hpre Hn Hk). }
destruct (Nat.eqb id 97).
{ change X_MAXVA_ASAN0 with (bv_unsigned (Z_to_bv 64 X_MAXVA_ASAN0)) in Hn.
exact (xn_smearva_sound ASEGS0 scfg ASAN0 NX0 LIMIT SINV argH FS0 Asan0_wx_nowrap asan0_in_hull asan0_hull_ok SINV_frame
(Z_to_bv 64 X_MAXVA_ASAN0) SMEARW0 args cs cs' E R FULL model T HC Hpre Hn Hk). }
destruct (Nat.eqb id 98); [|discriminate Hn].
exact (xn_absbytes_sound ASEGS0 scfg ASAN0 NX0 LIMIT SINV argH FS0 e_sp0_init argH_agree SINV_agree asan0_segs_wr args cs cs' E R FULL model T HC Hpre Hn Hk).
Qed.
End Hooks.
Section Stage.
Variable sp brk0 : word.
Variable rdraw : EntryDraw.
Variable argv envp : list (list byte).
Variables uid hw : word.
Variable fs : Fs.Fs.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv argv.
#[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
#[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
#[local] Notation LIM := AsanInitK.LIMIT.
Let AH := argH0_high APH0 sp rdraw argv envp uid hw Hsp Hva.
Let AA := argH0_agree APH0 sp rdraw argv envp uid hw.
Let SF := SINV0_frame APH0 sp rdraw brk0 argv envp uid hw.
Let SA := SINV0_agree APH0 sp rdraw brk0 argv envp uid hw.
Variable IT0 : itab.
Hypothesis IT0_ok : itab_sound ASEGS0 IT0.
Variable HS : nat -> option acs.
Variable T : Fs.Fs -> TSet.
Hypothesis T_nil : forall fs', T fs' [].
Definition HOLES (h : nat) (E : env) (fs' : Fs.Fs) : TSet := T fs'.
Lemma HOLES_agree : ltac2:(TCodec.tc2 tcn__Ja0StartupK "E'4'QB&D&QC&Q1r3r2%43321'8&QL&QKr5r4%33217%43398%73621p091pTF?1pHA1pFB1pTLD1").
Proof. reflexivity. Qed.
Lemma HOLES_nil : ltac2:(TCodec.tc2 tcn__Ja0StartupK ">'4'QB&D&QKr3r2r1(5'G%211%746541pTF91pF;1pTL=1").
Proof. intros. apply T_nil. Qed.
Lemma HOLES_flat : ltac2:(TCodec.tc2 tcn__Ja0StartupK "C'4'QB&D'8&QL&QKr5r3r1%43321r4r2%73214%:3941pTF<1pH>1pF?1pTNA1pTLB1").
Proof. reflexivity. Qed.
Hypothesis HS_sound : holes_stmt ASEGS0 scfg ASAN0 LIM HS SINV argH HOLES fs.
Hypothesis X_ALL : forall x, x_stmt ASEGS0 scfg ASAN0 NX0 LIM SINV argH fs x.
Variables KC0 BFUEL FUEL : nat.
Theorem stage_sound : ltac2:(TCodec.tc2 tcn__Ja0StartupK "RB'Q9'Q2'Q:'8'Q4&Q3&QFv@&QE&Q1&L&QI&QH&QGv?vBv0v=(1'Q7%211r2r3%B?A@?>=<;:9876321(Q0r1%211%H3G41'QB&Iy5'RLyR0%211%5241'6y8%611%311p061'F'Q<&M&QDvRIvREvR5vR4vR8vRMvR?%9887654321&N%17:986543vR9r4r7%@;QCQAQ?64321Q3Q4Q0'QNvRG&Q;&Q8r8%211%45QJ91Q:Q;&QA&QK&QMr5&H%11QA%655431?%>4R2=81p0@1pU4Q21pNQ41pQFQ:1pFQA1p0QC1pU>R=1pT@R?1pU:RA1").
Proof.
intros p cs0 s Hcert E R FULL model HC.
exact (check_sound ASEGS0 scfg IT0 IT0_ok ASAN0 NX0 LIM HS XN0 XE0 XB0
Asan0_wx_nowrap asan0_in_hull asan0_hull_ok asan0_shadow_ok SINV argH AH e_sp0_init AA SF SA
HOLES HOLES_agree HOLES_nil HOLES_flat fs KC0
(AsanNodesMmBK.node_sys_sound ASEGS0 scfg Halloc ASAN0 NX0 LIM SINV argH fs asan0_res_len asan0_res_hull asan0_hull_ok asan0_shadow_ok AH e_sp0_init AA SF SA)
(AsanNodesMmBK.node_brk2_sound ASEGS0 scfg Halloc ASAN0 NX0 LIM SINV argH fs asan0_in_hull asan0_res_len asan0_res_hull asan0_hull_ok asan0_shadow_ok AH SF)
(node_mmap2_sound_OBL ASEGS0 scfg ASAN0 NX0 LIM SINV argH fs Halloc Asan0_wx_nowrap asan0_in_hull asan0_res_len asan0_res_hull asan0_hull_ok asan0_shadow_ok AH e_sp0_init AA SF SA asan0_hull_tiled asan0_hull_lt)
(node_mmapin_sound_OBL ASEGS0 scfg ASAN0 NX0 LIM SINV argH fs Halloc Asan0_wx_nowrap asan0_in_hull asan0_res_len asan0_res_hull asan0_hull_ok asan0_shadow_ok AH e_sp0_init AA SF SA asan0_hull_tiled asan0_hull_lt)
(node_mprotect2_sound_OBL ASEGS0 scfg ASAN0 NX0 LIM SINV argH fs Halloc Asan0_wx_nowrap asan0_in_hull asan0_res_len asan0_res_hull asan0_hull_ok asan0_shadow_ok AH e_sp0_init AA SF SA asan0_hull_tiled asan0_hull_lt)
(AsanNodesMmBK.node_exit_sound ASEGS0 scfg ASAN0 LIM SINV argH fs)
X_ALL
(node_join_sound ASEGS0 scfg ASAN0 NX0 LIM SINV argH fs)
(XN0_sound LIM SINV argH fs AH AA SF SA) (XE0_sound _ _ _ _) (XB0_sound _ _ _ _)
HS_sound FUEL BFUEL None p cs0 s Hcert
E R FULL model t_nil HC I eq_refl).
Qed.
Corollary stage_hole : ltac2:(TCodec.tc2 tcn__Ja0StartupK "RE'Q9'Q2'Q:'8'Q4&Q3&QFv@&QE&Q1&L&QI&QH&QGv?vBv0v=(1'Q7%211r2r3%B?A@?>=<;:9876321(Q0r1%211%H3G41'3&Q5%119(7%M3421'QB&Iy5'RLyR0%211%5241'6y8%611%311p061'F'Q<&M&QDvRIvREvR5vR4vR8vRMvR?%9887654321&N%17:986543vR9r4r8%@;QHQFQD64321Q8Q9Q5'QNvRG&Q;&Q8r9%211%45QO91Q?Q@vR1&H%11QC%311%;4R4:51p0=1pU4O1pNQ11pQFQ71pFQ>1p0Q@1p0QF1pU>R@1pT@RB1pU:RD1").
Proof.
intros p cs0 s Hcert Hho E R FULL model HC.
apply (srz_conseq ASEGS0 scfg _ (sd HOLES t_nil E (m_fs model) s)); [exact (stage_sound p cs0 s Hcert E R FULL model HC)|].
exact (hole_only_den NX0 HS XN0 XE0 XB0 HOLES HOLES_flat t_nil E (m_fs model) s Hho).
Qed.
Lemma holes_stmt_ext : ltac2:(TCodec.tc2 tcn__Ja0StartupK "R9'4'6'Q2%211p041'8r3r2%211(2r1%2291%73941'QB&Iy5'RLyR0%211%5241y8%511%E11p051'F'Q<&QF&QE&L&M&QDvRIvREvR5vR4vR8vRMvR?%9887654321&N%17:986543vR9r4r6%C;BA@64321Q6Q5Q2'QNvRG&Q;&Q8r7%211%45I91Q=Q<vR1&H%11Q?%311%;4N:51p0=1pU4Q21pNQ41pQFQ91pFQ@1p0QB1pT>QM1pTLR01&Q@&Q6v?%221QM&QK%59Q<HQ;Q:2Q0N1Mp071pQ4R41").
Proof.
intros JS HJ h ch Hh E R FULL model HC. unfold hs_ext in Hh. unfold HOLES.
destruct (JS h) as [c|] eqn:Ej.
- injection Hh as <-. exact (HJ h c Ej E R FULL model HC).
- exact (HS_sound h ch Hh E R FULL model HC).
Qed.
End Stage.
Section Startup.
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
#[local] Notation E0a := (E0 APH0 sp rdraw brk0 argv envp uid hw).
#[local] Notation LIM := AsanInitK.LIMIT.
Variable IT0 : itab.
Hypothesis IT0_ok : itab_sound ASEGS0 IT0.
Variable HS : nat -> option acs.
Variable T : Fs.Fs -> TSet.
Hypothesis T_nil : forall fs', T fs' [].
Hypothesis HS_sound : holes_stmt ASEGS0 scfg ASAN0 LIM HS SINV argH (HOLES T) fs.
Hypothesis X_ALL : forall x, x_stmt ASEGS0 scfg ASAN0 NX0 LIM SINV argH fs x.
Variables KC0 BFUEL FUEL : nat.
Variable startup_plan : plan.
Variable startup_shape : shape.
Hypothesis startup_cert :
check ASEGS0 IT0 ASAN0 NX0 LIM XN0 XE0 XB0 HS KC0 BFUEL FUEL None asan0_init startup_plan = COk startup_shape.
Theorem as0_startup : ltac2:(TCodec.tc2 tcn__Ja0StartupK "Q5'QN&QFvRG&E&QO&QDvRIvR5vR@vRE&L&OvR4vR8vR9vRKvRMvR;vR?vR<vRBvRCvRHvR2vRN%>==<;:987654321%G9IFEDCBA@1&QA&QJvR1%211&QM&K%18LKHJEDA?vRJ%85542E1%Q44Q3Q2:1").
Proof.
pose proof asan0_img_facts as IMG.
rewrite (init_cfg_eq ASEGS0 ASAN0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt urnd Asan.M.init_pc eq_refl).
pose proof (init_cs_ok ASEGS0 ASAN0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt urnd IMG Hsp Hbrk Hva Hve Hfit Huid Hhw) as HC.
exact (stage_sound sp brk0 rdraw argv envp uid hw fs Hsp Hva IT0 IT0_ok HS T T_nil HS_sound X_ALL KC0 BFUEL FUEL
startup_plan asan0_init startup_shape startup_cert _ _ _ _ HC).
Qed.
Corollary as0_startup_hole : ltac2:(TCodec.tc2 tcn__Ja0StartupK "Q6'8'3&Q5vRJ%211(7%63521'QN&QFvRG&E&QO&QDvRIvR5vR@vRE&L&OvR4vR8vR9vRKvRMvR;vR?vR<vRBvRCvRHvR2vRN%>==<;:987654321%G9IFEDCBA@1vR1%11>%M4LK31p0O1").
Proof.
intros Hho. pose proof asan0_img_facts as IMG.
rewrite (init_cfg_eq ASEGS0 ASAN0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt urnd Asan.M.init_pc eq_refl).
pose proof (init_cs_ok ASEGS0 ASAN0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt urnd IMG Hsp Hbrk Hva Hve Hfit Huid Hhw) as HC.
exact (stage_hole sp brk0 rdraw argv envp uid hw fs Hsp Hva IT0 IT0_ok HS T T_nil HS_sound X_ALL KC0 BFUEL FUEL
startup_plan asan0_init startup_shape startup_cert Hho _ _ _ _ HC).
Qed.
End Startup.
End As0.
