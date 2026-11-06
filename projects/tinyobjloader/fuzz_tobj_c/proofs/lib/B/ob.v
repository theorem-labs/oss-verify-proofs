(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Ox.F128_005.   (* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o5.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nw o7.

(* [comment removed for export] *)
Module Start8States0.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "cons"; "nil"; "list"; "option"; "true"; "Some"; "prod"; "bool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "sprop"; "reg_sv"; "SPUle"; "SVar"; "SPAlign"; "ss_next"; "DZero"; "cell"; "mkObj"; "ss_pc"; "sstate"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Decimal"; "D0"; "D1"; "D2"; "Nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ob.Start8States0"; "K18x"; "E22A"; "E22B"; "E22_of"; "R22"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "sym_runA"; "ax_S"; "ax_X"; "ax_base"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@Corelib.Init.Nat"; "of_num_uint"; "@Corelib.Init.Number"; "UIntDecimal"; "@Stdlib.ZArith.BinInt.Z"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Start7States"; "K18S"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Start4States OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o5.Start7States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition pick {T} (v : bool) (a b : T) : T := if v then a else b.

Definition K18x : axst := ax_setX K18 [].
Lemma K18x_at : ltac2:(tb__ "0|2|
S1S0S18S11S24S1dA1M0A1P9fA3S1S0S4S8SbSbA2M1A1S25S1dA1S3G1A1A3S1S0SbS26S1dA1SaS2eA1A3S0S16G0S31A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition R22_run__R : option (list leafA) := ltac2:(tb__ "0|0|
S23S28S29S2aS1aS1bS19S19S19S1cA1A1A1A1A1A1A1S2S17Z706a0S2S17Z6bf18S3S17A1A3A3S1dS6A5").
Local Strategy expand [R22_run__R].
Definition R22 : option (list leafA) := Eval vm_compute in ((fun ro1__ : option (list leafA) => ro1__) R22_run__R).
Lemma R22_run : ltac2:(tb__ "0|0|
S0S5S4S22A1A1S23S28S29S2aS1aS1bS19S19S19S1cA1A1A1A1A1A1A1S2S17Z706a0S2S17Z6bf18S3S17A1A3A3S1dS6A5S21A3").
Proof. exact (@eq_refl (option (list leafA)) R22_run__R <: R22_run__R = R22). Qed.
Definition E22A : axst := Eval vm_compute in (match R22 with Some (l :: _) => la_state l | _ => K18x end).
Definition E22B : axst := Eval vm_compute in (match R22 with Some (_ :: l :: _) => la_state l | _ => K18x end).
Lemma run22 : ltac2:(tb__ "0|1|
S0S5S4S22A1M0A1S23S28S29S2aS1aS1bS19S19S19S1cA1A1A1A1A1A1A1S2S17Z706a0S2S17Z6bf18S3S17A1A3A3S1dS6A5S7G0S2S22S27S1eS2fA2S2S22S27S1fS2fA2S3S22A1A3A3A2A3").
Proof. rewrite R22_run. reflexivity. Qed.
Definition E22_of (v : bool) : axst := pick v E22A E22B.
Lemma E22_at : ltac2:(tb__ "0|5|
S9S1S0S17S15S24S20R1A1M0A1M1A1M2Z706a0A3S1S0S18S11G1A1P9fA3S1S0S5S2cA1S30S28G2A2S7S2cS2dA2A3S1S0S4S8SbSbA2M3A1S25G0A1S3G3A1A3S1S0SbS26G0A1SaS2eA1A3S1S0SbSdG1Z11A2SaZdeA1A3S1S0SbSdG1ZaA2SaZ0A1M4A3S1S0SbSdG1ZbA2SaZ100000A1A3S1S0SbSdG1ZcA2SaZ3A1A3S1S0SbSdG1ZdA2SaZ22A1A3S1S0SbSdG1ZeA2SaZffffffffffffffffA1A3S0SbSdG1ZfA2G4A3A2A2A2A2A2A2A2A2A2A2A2Fv;").
Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition F22 : list sprop := ltac2:(tb__ "0|2|
S2ScS10P9fM0ZcA2S2ScSeSaZ643000A1SfG0A1M1A2S2ScSeG1SaS2bZ7fffff800000Z100000A2A1A2S3ScA1A3A3A3").
Definition F23 : list sprop := ltac2:(tb__ "0|2|
S2ScS10Pa0M0ZcA2S2ScSeSaZ643000A1SfG0A1M1A2S2ScSeG1SaS2bZ7fffff800000Z800000A2A1A2S3ScA1A3A3A3").
Definition o13p : sobj := ltac2:(tb__ "0|0|
S14SfPa0A1SaZ0A1SaZ1000A1S3S13A1S12A5").
Definition F24 : list sprop := ltac2:(tb__ "0|3|
S2ScS10Pa1M0ZcA2S2ScSeSaZ1000M1A1SfG0A1M2A2S2ScSeG2SaS2bZ7fffff800000G1A2A1A2S3ScA1A3A3A3").
End Start8States0.

(* [comment removed for export] *)
Module DrvRGlue.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sobj"; "SLit"; "eval"; "rm"; "cell"; "rl"; "rw"; "ss_objs"; "mkObj"; "obj_holds"; "ss_facts"; "SAlu"; "holds"; "obj_hi_of"; "obj_lo_of"; "sv_eqb"; "DList"; "DUnknown"; "c_off"; "c_val"; "c_width"; "ob_base"; "ob_cells"; "obj_range"; "soff"; "SPBranch"; "SPNot"; "SVar"; "ob_dflt"; "odefault"; "sprop"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Corelib.Init.Datatypes"; "list"; "andb"; "bool"; "true"; "option"; "prod"; "pair"; "Some"; "cons"; "nil"; "nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "ax_setS"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "SHADOW_OFF"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "modulo"; "pow"; "sub"; "eqb"; "leb"; "ltb"; "div"; "mul"; "land"; "lor"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT"; "vTP"; "clen_of"; "flags_of"; "hdr_word"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@Stdlib.Lists.List"; "forallb"; "nth_error"; "Forall2"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT.TAddr"; "TP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ"; "obj_clear_litb2"; "tv_bandfree"; "obj_clear_litb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.DrvR_states"; "errL"; "errL_okb"; "clen_x"; "errL0"; "errL0_okb"; "errV"; "errV0"; "errV0_okb"; "errV_okb"; "flg_x"; "has_tpfact"; "ob_shape0b"; "plen_x"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.ErrnoA"; "errno_blind"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "JA"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "errno_addrA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_AND"; "ALU_OR"; "ALU_SRL"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ob.DrvRGlue"; "pub_lit_okb"; "pub_lit_okb2"; "pub_sym_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvR_tstates"; "ms16_at"; "x4_okb"; "x4d_okb"; "x4set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bxt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require BudA TobjJA TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import DrvGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Code DrvJ.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nw.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nw.DrvJRe.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.ErrnoA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceT DrvIfaceR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.DrvErrno OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o3.DrvR_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvR_tstates.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import PFAddr TAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma ob_shape0b_sound : ltac2:(tb__ "0|0|
S9S7S7S7S0S2dS6dR4R3R2R1A4S2eA3S0S9R5S11R4R3R2S34SdA1S1aA5A3F_;Fhi;Flo;Fb;Fo;").
Proof.
  intros [ob ol oh oc od] b lo hi H. unfold ob_shape0b in H. cbn in H.
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3. subst.
  destruct oc; [|discriminate]. destruct od; try discriminate. reflexivity.
Qed.

Lemma has_tpfact_holds : ltac2:(tb__ "0|0|
S39S8S0S2dS6cR2A1S2eA3S76S27S15R2A1S13S3aR3A1A1A3S0S4S37Q40SbR3S53A2A2S5eA3F_;F_;Frho;FE;").
Proof.
  intros E rho H HF. unfold has_tpfact in H. pose proof (holds_mem _ _ _ HF H) as X. cbn [holds] in X.
  unfold vTP in X |- *. rewrite X. rewrite U_lit. reflexivity.
Qed.

Lemma SPA_errV0 : ltac2:(tb__ "0|0|
S2aS8S39S2bS36Q40A1A1S4eS0S2dS69R3A1S2eA3S29S6R6R4R5R3R2A6S29S6R7S68R5A1R6R4R3A6F_;F_;Fw;Ftp;FE;Frho;FJ;").
Proof.
  intros J rho E tp w H HS. unfold errV0_okb in H. apply andb_prop in H as [H Htp]. apply andb_prop in H as [Hn Hsame].
  destruct (nth_error (ss_objs (ax_S E)) (ierrL E)) as [o|] eqn:En; [|discriminate].
  apply ob_shape0b_sound in Hn. subst o.
  pose proof (has_tpfact_holds E rho Htp (smatchA_facts segs _ _ _ _ (proj1 HS))) as HTP.
  unfold errV0. apply (SPA_reslice segs J rho E (ierrL E) _ O_errnoV tp w En); try reflexivity.
  - exact Hsame.
  - unfold O_errnoV, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small; unfold TP; try lia.
    rewrite HTP. cbn [eval]. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. unfold TP. f_equal; lia.
  - unfold O_errnoV, obj_lo_of, obj_hi_of; cbn [ob_base ob_lo ob_hi]; rewrite !soff_lit_small; lia.
  - exact HS.
Qed.

Lemma SPA_errV : ltac2:(tb__ "0|0|
S2aS8S39S2bS36Q40A1A1S4eS0S2dS6aR3A1S2eA3S29S6R6R4R5R3R2A6S29S6R7S67R5A1R6R4R3A6F_;F_;Fw;Ftp;FE;Frho;FJ;").
Proof.
  intros J rho E tp w H HS. unfold errV_okb in H. apply andb_prop in H as [HC HV]. unfold errV.
  exact (SPA_errV0 J rho (errC E) tp w HV (SPA_errC J rho E tp w HC HS)).
Qed.

Lemma SPA_errL0 : ltac2:(tb__ "0|0|
S2aS8S39S2bS36Q40A1A1S4eS0S2dS66R3A1S2eA3S29S6R6R4R5R3R2A6S29S6R7S65R5A1R6R4R3A6F_;F_;Fw;Ftp;FE;Frho;FJ;").
Proof.
  intros J rho E tp w H HS. unfold errL0_okb in H. apply andb_prop in H as [H Htp]. apply andb_prop in H as [Hn Hsame].
  destruct (nth_error (ss_objs (ax_S E)) (ierrV E)) as [o|] eqn:En; [|discriminate].
  apply ob_shape0b_sound in Hn. subst o.
  pose proof (has_tpfact_holds E rho Htp (smatchA_facts segs _ _ _ _ (proj1 HS))) as HTP.
  unfold errL0. apply (SPA_reslice segs J rho E (ierrV E) _ O_errno tp w En); try reflexivity.
  - exact Hsame.
  - unfold O_errno, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small; unfold TP; try lia.
    rewrite HTP. cbn [eval]. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. unfold TP. f_equal; lia.
  - unfold O_errno, obj_lo_of, obj_hi_of; cbn [ob_base ob_lo ob_hi]; rewrite !soff_lit_small; unfold TP; lia.
  - exact HS.
Qed.

Lemma errL_Ts : ltac2:(tb__ "0|3|
S4eOF_;S2aS39S4fS8S2bS36Q40M0A1M1A1S0S2dS63R4A1S2eA3S70R6A1S8S0S5G1F_;SfR1A1SfR5A1A3S0S5S2bS36Q8A1M2A1F_;SeR2A1SeR6A1A3G1S2S74S37G0R1A2A1A1S0S2fG2A1ScR5R2A2ScR9R2A2A3F_;Fa;S51S6RcS29S6RbS62RaA1R4R7A5R9A4F_;F_;F_;Frho1;S51S6R9S29S6R8R7R5R4A5R6A4F_;F_;F_;Ftp;Frho;FQ;FE;FJ;Fok;").
Proof.
  intros ok J E Q rho tp H HJ HT. unfold errL_okb in H. apply andb_prop in H as [HL HR].
  eapply triple_conseq; [intros w HS; exact (SPA_errL0 J rho E tp w HL HS) | intros w Hw; exact Hw |].
  apply (errR_T (triple segs ok) (fun P P' Q0 HP HTq => ltac:(eapply triple_conseq; [exact HP | intros w0 Hw0; exact Hw0 | exact HTq])) (fun A P Q0 => @triple_ex segs ok A P Q0) (fun X P Q0 => @triple_pure segs ok X P Q0) J (errL0 E) Q rho tp HR HJ).
  exact HT.
Qed.
Lemma errL_Te : ltac2:(tb__ "0|3|
S2aS39S4fS8S2bS36Q40M0A1M1A1S0S2dS63R4A1S2eA3S70R6A1S8S0S5G1F_;SfR1A1SfR5A1A3S0S5S2bS36Q8A1M2A1F_;SeR2A1SeR6A1A3G1S2S74S37G0R1A2A1A1S0S2fG2A1ScR5R2A2ScR9R2A2A3F_;Fa;S50S6S29S6RbS62RaA1R4R7A5R9A3F_;F_;F_;Frho1;S50S6S29S6R8R7R5R4A5R6A3F_;F_;F_;Ftp;Frho;FQ;FE;FJ;").
Proof.
  intros J E Q rho tp H HJ HT. unfold errL_okb in H. apply andb_prop in H as [HL HR].
  eapply etriple_conseq; [intros w HS; exact (SPA_errL0 J rho E tp w HL HS) | intros w Hw; exact Hw |].
  apply (errR_T (etriple segs) (fun P P' Q0 HP HTq => ltac:(eapply etriple_conseq; [exact HP | intros w0 Hw0; exact Hw0 | exact HTq])) (fun A P Q0 => @etriple_ex segs A P Q0) (fun X P Q0 => @etriple_pure segs X P Q0) J (errL0 E) Q rho tp HR HJ).
  exact HT.
Qed.

Lemma x4d_okb_sound : ltac2:(tb__ "0|4|
S2bS30S7S7A2M0A1M1S0S2dS80R1A1S2eA3S3S0G1R2S34G0A1M2A3S3S0G1R2S33G0S31S7S7S53SaS5eA1M3A4G2A3A3S0G1R2S33G0S31S7S7G3S53A4G2A3A3A2A2F_;Fd;").
Proof.
  intros [|[a b] [|]] H; try discriminate; [left; reflexivity|]. cbn in H. apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2];
  apply sv_eqb_sound in H1; apply sv_eqb_sound in H2; subst; auto.
Qed.

Lemma SPA_x4set : ltac2:(tb__ "0|0|
S2aS8S39S7S2bS36Q40A1A1S4eS0S2dS7fR4R3A2S2eA3S29S6R7R5R6R3R2A6S29S6R8S81R5R6A2R7R4R3A6F_;F_;Fw;Ftp;Fe;FA;Frho;FJ;").
Proof.
  intros J rho A e tp w H HS. unfold x4_okb in H. apply andb_prop in H as [H Htp]. apply andb_prop in H as [Hwf Hd].
  destruct (state_diff (ax_S A) (ax_S (x4set e A))) as [[d [|]]|] eqn:E; try discriminate.
  pose proof (has_tpfact_holds A rho Htp (smatchA_facts segs _ _ _ _ (proj1 HS))) as HTP.
  assert (Htpe : eval rho vTP = eval rho (SLit TP)).
  { apply bv_eq. rewrite HTP. cbn [eval]. rewrite Z_to_bv_unsigned. reflexivity. }
  unfold x4set. apply (SPA_restate segs J rho A _ tp w d [] Hwf E).
  - reflexivity.
  - destruct (x4d_okb_sound d Hd) as [-> |[-> | ->]]; [constructor| |];
      (constructor; [cbn [fst snd] | constructor]); [exact Htpe | symmetry; exact Htpe].
  - constructor.
  - exact HS.
Qed.

Lemma ms16_shape_holds : ltac2:(tb__ "0|0|
S8S7S15R2S23S22S7aS14S77S14S78SaZ28A1R1A3SaZfA1A3SaZ0A1A3A1A2Fx;Frho;").
Proof.
  intros rho x. cbn [holds eval branch_taken]. intros HB.
  unfold bv_eqb in HB. apply Z.eqb_eq in HB.
  assert (U0 : bv_unsigned (alu64 ALU_AND (alu64 ALU_OR (Z_to_bv 64 40) (eval rho x)) (Z_to_bv 64 15)) = 0).
  { rewrite HB. rewrite lit_unsigned. reflexivity. }
  rewrite and_val, or_val_A, !lit_unsigned in U0. change (40 mod 2 ^ 64) with 40 in U0. change (15 mod 2 ^ 64) with 15 in U0.
  assert (T : Z.testbit (Z.land (Z.lor 40 (bv_unsigned (eval rho x))) 15) 3 = true).
  { rewrite Z.land_spec, Z.lor_spec. reflexivity. }
  rewrite U0 in T. cbn in T. discriminate.
Qed.
Lemma ms16_at_holds : ltac2:(tb__ "0|0|
S8S7S4S15R3S7eR2R1A2A2Fd;Fb;Frho;").
Proof. intros rho b d. exact (ms16_shape_holds rho (SAlu ALU_ADD b (SLit (- d)))). Qed.

Definition pub_lit_okb (A : axst) (B L : Z) : bool := ltac2:(tb__ "0|4|
S2cS2cS2cS2cS2cS2cS48Z0M0VB;A2S47S44VB;Z40M1A2G0A2A2S49G0VL;A2A2S47S44VL;G1A2G0A2A2S48S43VB;VL;A2M2S45Z2Z28A2A2A2S18S3cVA;A1SaS40A1A2A2S58S9S61S13S3aVA;A1M3A1S3fVB;A1S3fG2A1A3S10G3A1A3A2").

Lemma SPA_publish_lit : ltac2:(tb__ "0|3|
S2aS8S39S2bS36Q40M0A1A1S4eS4S4S0S2dS7bR5R2R1A3S2eA3S4S1S41S3fR4A1R1A2S42R1S3fS43R4R3A2A1A2A2S0S2fS36Q8M1A1M2A1ScR9S38G0R2A2A2S32G2S38G1Z0A2A2A3F_;Fz;S29S6R9R7R8R6R5A6S29S6RaS57R8S33S30S7S7A2S31S7S7SaR5A1SaR4A1A4S3bR8A1A3A2R9R7R6A6F_;F_;F_;FL;FB;Fw;Ftp;FA;Frho;FJ;").
Proof.
  intros J rho A tp w B L Hok Hz HS.
  unfold pub_lit_okb in Hok. apply andb_prop in Hok as [Hok HO]. apply andb_prop in Hok as [Hok Hb]. apply andb_prop in Hok as [Hok H5].
  apply andb_prop in Hok as [Hok H4]. apply andb_prop in Hok as [Hok H3]. apply andb_prop in Hok as [H1 H2].
  apply Z.leb_le in H1. apply Z.eqb_eq in H2. apply Z.ltb_lt in H3. apply Z.eqb_eq in H4. apply Z.leb_le in H5. apply sv_eqb_sound in Hb.
  pose proof HS as [(Hsm & _) _].
  assert (HF : Forall (holds rho) (ss_facts (ax_S A))) by exact (smatch_facts_hold _ _ _ _ Hsm).
  assert (Hall : Forall (obj_holds segs rho (cfg_ms (snd (virt tp w)))) (ss_objs (ax_S A))).
  { destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall. }
  assert (SHB : Sh B = SHADOW_OFF + B / 8) by (unfold Sh; lia).
  assert (SHE : Sh (B + L) = SHADOW_OFF + (B + L) / 8) by (unfold Sh; lia).
  assert (OUT : forall z, Sh B <= z < Sh (B + L) -> outside_all rho (ss_objs (ax_S A)) (Z_to_bv 64 z)).
  { intros z Hzr. apply (ranges_disjoint_outside rho _ (Sh B) (Sh (B + L))).
    - apply Forall_forall. intros o Ho.
      apply (obj_clear_litb_sound rho _ (ss_facts (ax_S A)) (Sh B) (Sh (B + L)) o (proj1 (Forall_forall _ _) Hall o Ho) HF);
        [unfold Sh, SHADOW_OFF; split; [lia | apply Z.add_le_mono_r; apply Z.div_le_mono; lia] | unfold Sh, SHADOW_OFF; pose proof (Z.div_le_mono (B + L) (2 ^ 40) 8 ltac:(lia) H5); lia |].
      exact (proj1 (forallb_forall _ _) HO o Ho).
    - rewrite lit_unsigned.
      rewrite Z.mod_small; [exact Hzr|]. unfold Sh, SHADOW_OFF in Hzr |- *. pose proof (Z.div_le_mono (B + L) (2 ^ 40) 8 ltac:(lia) H5). pose proof (Z.div_pos B 8). lia. }
  apply (SPA_x_publish segs J rho A (SLit B, SLit L) tp w); [reflexivity | | exact HS].
  rewrite Hb. unfold xr_ok. cbn [eval fst snd]. rewrite !lit_unsigned.
  rewrite (Z.mod_small SHADOW_OFF) by (unfold SHADOW_OFF; lia). rewrite (Z.mod_small B) by lia. rewrite (Z.mod_small L) by lia.
  split; [pose proof (Z.div_mod B 64 ltac:(lia)) as DB0; rewrite H2 in DB0; replace B with ((8 * (B / 64)) * 8) by lia; apply Z_mod_mult|].
  split; [lia|].
  intros a Ha.

  assert (W : forall j, 0 <= j < 8 -> Sh B <= (SHADOW_OFF + a / 8) / 8 * 8 + j < Sh (B + L)).
  { intros j Hj. rewrite SHB, SHE.
    pose proof (Z.div_mod B 64 ltac:(lia)) as DB. pose proof (Z.div_mod L 64 ltac:(lia)) as DL.
    pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ma.
    assert (HB8 : B / 8 = 8 * (B / 64)) by (rewrite H2 in DB; nia).
    assert (HBL8 : (B + L) / 8 = 8 * (B / 64) + 8 * (L / 64)) by (rewrite H2 in DB; rewrite H4 in DL; nia).
    assert (LO : 8 * (B / 64) <= a / 8) by (apply Z.div_le_lower_bound; lia).
    assert (HI : a / 8 < 8 * (B / 64) + 8 * (L / 64)) by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_mod (a / 8) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (a / 8) 8 ltac:(lia)) as M3.
    assert (E8 : (SHADOW_OFF + a / 8) / 8 * 8 = SHADOW_OFF + (a / 8) / 8 * 8).
    { replace (SHADOW_OFF + a / 8) with ((268431360 + (a / 8) / 8) * 8 + (a / 8) mod 8) by (unfold SHADOW_OFF; lia).
      rewrite Z.div_add_l by lia. rewrite (Z.div_small ((a / 8) mod 8) 8) by lia. unfold SHADOW_OFF. lia. }
    rewrite E8.
    assert (LO2 : B / 64 <= (a / 8) / 8) by (apply Z.div_le_lower_bound; lia).
    assert (HI2 : (a / 8) / 8 < (B / 64) + (L / 64)) by (apply Z.div_lt_upper_bound; lia).
    lia. }
  assert (INa : Sh B <= SHADOW_OFF + a / 8 < Sh (B + L)).
  { rewrite SHB, SHE. split; [apply Z.add_le_mono_l; apply Z.div_le_mono; lia|].
    apply Z.add_lt_mono_l. pose proof (Z.div_mod B 64 ltac:(lia)) as DB. pose proof (Z.div_mod L 64 ltac:(lia)) as DL.
    rewrite H2 in DB. rewrite H4 in DL. apply Z.div_lt_upper_bound; [lia|]. nia. }
  split; [unfold Sh, SHADOW_OFF in INa |- *; pose proof (Z.div_le_mono (B + L) (2 ^ 40) 8 ltac:(lia) H5); lia|].
  split; [unfold shadow_addr; apply OUT; exact INa|].
  split.
  - intros j Hj. unfold word_byte. split; [apply OUT; apply W; exact Hj|]. rewrite (Hz _ (W j Hj)). discriminate.
  - exists (Z_to_bv 8 0). split; [unfold shadow_addr; apply Hz; exact INa|]. left. reflexivity.
Qed.

Definition pub_lit_okb2 (A : axst) (tv : list (sv * sv)) (B L : Z) : bool := ltac2:(tb__ "0|4|
S2cS2cS2cS2cS2cS2cS48Z0M0VB;A2S47S44VB;Z40M1A2G0A2A2S49G0VL;A2A2S47S44VL;G1A2G0A2A2S48S43VB;VL;A2M2S45Z2Z28A2A2A2S18S3cVA;A1SaS40A1A2A2S58S9S5fS13S3aVA;A1M3A1Vtv;S3fVB;A1S3fG2A1A4S10G3A1A3A2").

Lemma SPA_publish_lit2 : ltac2:(tb__ "0|4|
S2aS8S39S2bS30S7S7A2M0A1S2bS36Q40M1A1A1S4eS4S4S0S2dS7cR6R5R2R1A4S2eA3S60R8R6A2S4S1S41S3fR5A1R1A2S42R1S3fS43R5R4A2A1A2A2S0S2fS36Q8M2A1M3A1ScRbS38G1R2A2A2S32G3S38G2Z0A2A2A3F_;Fz;S29S6RbR9RaR7R6A6S29S6RcS57RaS33G0S31S7S7SaR6A1SaR5A1A4S3bRaA1A3A2RbR8R7A6F_;F_;F_;F_;FL;FB;Fw;Ftp;Ftv;FA;Frho;FJ;").
Proof.
  intros J rho A tv tp w B L Hok HTV Hz HS.
  unfold pub_lit_okb2 in Hok. apply andb_prop in Hok as [Hok HO]. apply andb_prop in Hok as [Hok Hb]. apply andb_prop in Hok as [Hok H5].
  apply andb_prop in Hok as [Hok H4]. apply andb_prop in Hok as [Hok H3]. apply andb_prop in Hok as [H1 H2].
  apply Z.leb_le in H1. apply Z.eqb_eq in H2. apply Z.ltb_lt in H3. apply Z.eqb_eq in H4. apply Z.leb_le in H5. apply sv_eqb_sound in Hb.
  pose proof HS as [(Hsm & _) _].
  assert (HF : Forall (holds rho) (ss_facts (ax_S A))) by exact (smatch_facts_hold _ _ _ _ Hsm).
  assert (Hall : Forall (obj_holds segs rho (cfg_ms (snd (virt tp w)))) (ss_objs (ax_S A))).
  { destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall. }
  assert (SHB : Sh B = SHADOW_OFF + B / 8) by (unfold Sh; lia).
  assert (SHE : Sh (B + L) = SHADOW_OFF + (B + L) / 8) by (unfold Sh; lia).
  assert (OUT : forall z, Sh B <= z < Sh (B + L) -> outside_all rho (ss_objs (ax_S A)) (Z_to_bv 64 z)).
  { intros z Hzr. apply (ranges_disjoint_outside rho _ (Sh B) (Sh (B + L))).
    - apply Forall_forall. intros o Ho.
      apply (obj_clear_litb2_sound rho _ (ss_facts (ax_S A)) tv (Sh B) (Sh (B + L)) o (proj1 (Forall_forall _ _) Hall o Ho) HF);
        [unfold Sh, SHADOW_OFF; split; [lia | apply Z.add_le_mono_r; apply Z.div_le_mono; lia] | unfold Sh, SHADOW_OFF; pose proof (Z.div_le_mono (B + L) (2 ^ 40) 8 ltac:(lia) H5); lia | exact HTV |].
      exact (proj1 (forallb_forall _ _) HO o Ho).
    - rewrite lit_unsigned.
      rewrite Z.mod_small; [exact Hzr|]. unfold Sh, SHADOW_OFF in Hzr |- *. pose proof (Z.div_le_mono (B + L) (2 ^ 40) 8 ltac:(lia) H5). pose proof (Z.div_pos B 8). lia. }
  apply (SPA_x_publish segs J rho A (SLit B, SLit L) tp w); [reflexivity | | exact HS].
  rewrite Hb. unfold xr_ok. cbn [eval fst snd]. rewrite !lit_unsigned.
  rewrite (Z.mod_small SHADOW_OFF) by (unfold SHADOW_OFF; lia). rewrite (Z.mod_small B) by lia. rewrite (Z.mod_small L) by lia.
  split; [pose proof (Z.div_mod B 64 ltac:(lia)) as DB0; rewrite H2 in DB0; replace B with ((8 * (B / 64)) * 8) by lia; apply Z_mod_mult|].
  split; [lia|].
  intros a Ha.

  assert (W : forall j, 0 <= j < 8 -> Sh B <= (SHADOW_OFF + a / 8) / 8 * 8 + j < Sh (B + L)).
  { intros j Hj. rewrite SHB, SHE.
    pose proof (Z.div_mod B 64 ltac:(lia)) as DB. pose proof (Z.div_mod L 64 ltac:(lia)) as DL.
    pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ma.
    assert (HB8 : B / 8 = 8 * (B / 64)) by (rewrite H2 in DB; nia).
    assert (HBL8 : (B + L) / 8 = 8 * (B / 64) + 8 * (L / 64)) by (rewrite H2 in DB; rewrite H4 in DL; nia).
    assert (LO : 8 * (B / 64) <= a / 8) by (apply Z.div_le_lower_bound; lia).
    assert (HI : a / 8 < 8 * (B / 64) + 8 * (L / 64)) by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_mod (a / 8) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (a / 8) 8 ltac:(lia)) as M3.
    assert (E8 : (SHADOW_OFF + a / 8) / 8 * 8 = SHADOW_OFF + (a / 8) / 8 * 8).
    { replace (SHADOW_OFF + a / 8) with ((268431360 + (a / 8) / 8) * 8 + (a / 8) mod 8) by (unfold SHADOW_OFF; lia).
      rewrite Z.div_add_l by lia. rewrite (Z.div_small ((a / 8) mod 8) 8) by lia. unfold SHADOW_OFF. lia. }
    rewrite E8.
    assert (LO2 : B / 64 <= (a / 8) / 8) by (apply Z.div_le_lower_bound; lia).
    assert (HI2 : (a / 8) / 8 < (B / 64) + (L / 64)) by (apply Z.div_lt_upper_bound; lia).
    lia. }
  assert (INa : Sh B <= SHADOW_OFF + a / 8 < Sh (B + L)).
  { rewrite SHB, SHE. split; [apply Z.add_le_mono_l; apply Z.div_le_mono; lia|].
    apply Z.add_lt_mono_l. pose proof (Z.div_mod B 64 ltac:(lia)) as DB. pose proof (Z.div_mod L 64 ltac:(lia)) as DL.
    rewrite H2 in DB. rewrite H4 in DL. apply Z.div_lt_upper_bound; [lia|]. nia. }
  split; [unfold Sh, SHADOW_OFF in INa |- *; pose proof (Z.div_le_mono (B + L) (2 ^ 40) 8 ltac:(lia) H5); lia|].
  split; [unfold shadow_addr; apply OUT; exact INa|].
  split.
  - intros j Hj. unfold word_byte. split; [apply OUT; apply W; exact Hj|]. rewrite (Hz _ (W j Hj)). discriminate.
  - exists (Z_to_bv 8 0). split; [unfold shadow_addr; apply Hz; exact INa|]. left. reflexivity.
Qed.

Definition pub_sym_okb (A : axst) (tv : list (sv * sv)) (eB eL : sv) (LO HI : Z) : bool := ltac2:(tb__ "0|3|
S2cS2cS2cS2cS2cS2cS48Z0M0VLO;A2S47S44VLO;Z40M1A2G0A2A2S47S44VHI;G1A2G0A2A2S48VHI;S45Z2Z2fA2A2A2S18S3cVA;A1SaS40A1A2A2S3eS28S3aVA;A1M2A1S31S7S7VeB;VeL;A4A2A2S58S9S5fS13G2A1Vtv;S3fVLO;A1S3fVHI;A1A4S10G2A1A3A2").

Lemma SPA_publish_sym : ltac2:(tb__ "0|6|
S2aS8S39S2bS30S7S7A2M0A1S2bS36Q40M1A1A1S4eS7S7S4S4S0S2dS7dR8R7R4R3R2R1A6S2eA3S60RaR8A2S37G1SbRbR6A2A2S4S37G1SbRcR6A2A2S4S41R6R2A2S41S43R3R2A2R6A2S0S4S44R4Z40A2Z0M2A3M3G3S42G2R5A2S4S1S41S3fR8A1R1A2S42R1S3fS43R8R7A2A1A2A2S0S2fS36Q8M4A1M5A1ScR14S38G1R2A2A2S32G5S38G4G2A2A2A3F_;Fz;S29S6R14R12R13R10RfA6S29S6R15S57R13S33G0S31S7S7RfReA4S3bR13A1A3A2R14R11R10A6F_;F_;F_;F_;F_;F_;F_;TL;TB;F_;F_;FHI;FLO;FeL;FeB;Fw;Ftp;Ftv;FA;Frho;FJ;").
Proof.
  intros J rho A tv tp w eB eL LO HI Hok HTV B L HLB HBH H2 H4 H3 Hz HS.
  unfold pub_sym_okb in Hok. apply andb_prop in Hok as [Hok HO]. apply andb_prop in Hok as [Hok Hxb]. apply andb_prop in Hok as [Hok Hb].
  apply andb_prop in Hok as [Hok H5]. apply andb_prop in Hok as [Hok HH64]. apply andb_prop in Hok as [H1 HL64].
  apply Z.leb_le in H1. apply Z.eqb_eq in HL64. apply Z.eqb_eq in HH64. apply Z.leb_le in H5. apply sv_eqb_sound in Hb.
  pose proof HS as [(Hsm & _) _].
  assert (HF : Forall (holds rho) (ss_facts (ax_S A))) by exact (smatch_facts_hold _ _ _ _ Hsm).
  assert (Hall : Forall (obj_holds segs rho (cfg_ms (snd (virt tp w)))) (ss_objs (ax_S A))).
  { destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _). exact Hall. }
  assert (SHB : Sh B = SHADOW_OFF + B / 8) by (unfold Sh; lia).
  assert (SHE : Sh (B + L) = SHADOW_OFF + (B + L) / 8) by (unfold Sh; lia).
  assert (OUT : forall z, Sh B <= z < Sh (B + L) -> outside_all rho (ss_objs (ax_S A)) (Z_to_bv 64 z)).
  { intros z Hzr. apply (ranges_disjoint_outside rho _ (Sh LO) (Sh HI)).
    - apply Forall_forall. intros o Ho.
      apply (obj_clear_litb2_sound rho _ (ss_facts (ax_S A)) tv (Sh LO) (Sh HI) o (proj1 (Forall_forall _ _) Hall o Ho) HF);
        [unfold Sh, SHADOW_OFF; split; [lia | apply Z.add_le_mono_r; apply Z.div_le_mono; lia] | unfold Sh, SHADOW_OFF; pose proof (Z.div_le_mono HI (2 ^ 47) 8 ltac:(lia) H5); lia | exact HTV |].
      exact (proj1 (forallb_forall _ _) HO o Ho).
    - rewrite lit_unsigned.
      assert (R1 : Sh LO <= Sh B) by (unfold Sh; apply Z.add_le_mono_r; apply Z.div_le_mono; lia).
      assert (R2 : Sh (B + L) <= Sh HI) by (unfold Sh; apply Z.add_le_mono_r; apply Z.div_le_mono; lia).
      rewrite Z.mod_small; [lia|]. unfold Sh, SHADOW_OFF in Hzr, R1, R2 |- *. pose proof (Z.div_le_mono HI (2 ^ 47) 8 ltac:(lia) H5). pose proof (Z.div_pos LO 8). lia. }
  apply (SPA_x_publish segs J rho A (eB, eL) tp w); [exact Hxb | | exact HS].
  rewrite Hb. unfold xr_ok. cbn [fst snd]. change (eval rho (SLit SHADOW_OFF)) with (Z_to_bv 64 SHADOW_OFF). rewrite lit_unsigned. fold B L.
  rewrite (Z.mod_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
  split; [pose proof (Z.div_mod B 64 ltac:(lia)) as DB0; rewrite H2 in DB0; replace B with ((8 * (B / 64)) * 8) by lia; apply Z_mod_mult|].
  pose proof (urange (eval rho eB)). pose proof (urange (eval rho eL)).
  split; [lia|].
  intros a Ha.

  assert (W : forall j, 0 <= j < 8 -> Sh B <= (SHADOW_OFF + a / 8) / 8 * 8 + j < Sh (B + L)).
  { intros j Hj. rewrite SHB, SHE.
    pose proof (Z.div_mod B 64 ltac:(lia)) as DB. pose proof (Z.div_mod L 64 ltac:(lia)) as DL.
    pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ma.
    assert (HB8 : B / 8 = 8 * (B / 64)) by (rewrite H2 in DB; nia).
    assert (HBL8 : (B + L) / 8 = 8 * (B / 64) + 8 * (L / 64)) by (rewrite H2 in DB; rewrite H4 in DL; nia).
    assert (LOa : 8 * (B / 64) <= a / 8) by (apply Z.div_le_lower_bound; lia).
    assert (HIa : a / 8 < 8 * (B / 64) + 8 * (L / 64)) by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_mod (a / 8) 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (a / 8) 8 ltac:(lia)) as M3.
    assert (E8 : (SHADOW_OFF + a / 8) / 8 * 8 = SHADOW_OFF + (a / 8) / 8 * 8).
    { replace (SHADOW_OFF + a / 8) with ((268431360 + (a / 8) / 8) * 8 + (a / 8) mod 8) by (unfold SHADOW_OFF; lia).
      rewrite Z.div_add_l by lia. rewrite (Z.div_small ((a / 8) mod 8) 8) by lia. unfold SHADOW_OFF. lia. }
    rewrite E8.
    assert (LO2 : B / 64 <= (a / 8) / 8) by (apply Z.div_le_lower_bound; lia).
    assert (HI2 : (a / 8) / 8 < (B / 64) + (L / 64)) by (apply Z.div_lt_upper_bound; lia).
    lia. }
  assert (INa : Sh B <= SHADOW_OFF + a / 8 < Sh (B + L)).
  { rewrite SHB, SHE. split; [apply Z.add_le_mono_l; apply Z.div_le_mono; lia|].
    apply Z.add_lt_mono_l. pose proof (Z.div_mod B 64 ltac:(lia)) as DB. pose proof (Z.div_mod L 64 ltac:(lia)) as DL.
    rewrite H2 in DB. rewrite H4 in DL. apply Z.div_lt_upper_bound; [lia|]. nia. }
  split; [unfold Sh, SHADOW_OFF in INa |- *; pose proof (Z.div_le_mono HI (2 ^ 47) 8 ltac:(lia) H5); pose proof (Z.div_le_mono (B + L) HI 8 ltac:(lia) HBH); lia|].
  split; [unfold shadow_addr; apply OUT; exact INa|].
  split.
  - intros j Hj. unfold word_byte. split; [apply OUT; apply W; exact Hj|]. rewrite (Hz _ (W j Hj)). discriminate.
  - exists (Z_to_bv 8 0). split; [unfold shadow_addr; apply Hz; exact INa|]. left. reflexivity.
Qed.

Lemma SPA_reobj_same_range : ltac2:(tb__ "0|1|
S2aS8S39S35S9S9S2bS36Q40A1A1S4eS0S2fS9A1S59S9S10S3aR6A1A1R5A3S32S9R4A2A3S0S2dS6fS3aR7A1M0S52G0R6R4A3A2S2eA3S0S30S4S4A2S20R9R5A2S20R9R6A2A3S5bS12S6RbR1R8A4S12S6RcR2R8A4F_;Fms;S29S6RcRaRbR6R5A6S29S6RdS3dRbS52S3aRbA1RaR8A3A2RcR7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Fo';Fo;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i o o' tp w Hn Hsame Hr HO HS.
  pose proof HS as [(Hsm & HMI & Haw & Hsh & Hhz) Hk].
  pose proof (nth_error_split3 (ss_objs (ax_S A)) i o Hn) as EO.
  assert (Hin : In o (ss_objs (ax_S A))) by (eapply nth_error_In; exact Hn).
  apply (SPA_reobj segs J rho A (set_obj_at (ax_S A) i o') tp w).
  - exact Hsame.
  - reflexivity.
  - exact HS.
  - destruct w as [tr [ms md]]. unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg].
    unfold virt in Hsm. cbn [fst snd cfg_ms cfg_model w_tr w_cfg] in Hsm.
    pose proof (smatch_mm segs _ _ _ _ _ Hsm) as Hmm. cbn [ss_objs set_obj_at set_objs].
    rewrite EO in Hmm.
    change (firstn i (ss_objs (ax_S A)) ++ o' :: skipn (S i) (ss_objs (ax_S A)))
      with (firstn i (ss_objs (ax_S A)) ++ [o'] ++ skipn (S i) (ss_objs (ax_S A))).
    apply (mem_match_replace segs rho _ (firstn i (ss_objs (ax_S A))) o (skipn (S i) (ss_objs (ax_S A))) [o'] Hmm).
    + constructor; [|constructor]. destruct Hmm as (Hall & _ & _).
      apply HO. exact (proj1 (Forall_forall _ _) Hall o ltac:(apply in_or_app; right; left; reflexivity)).
    + destruct Hmm as (_ & Hpd & _). apply pairwise_disjoint_pdr in Hpd.
      rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *. rewrite Hr. exact Hpd.
    + intros x. split.
      * intros Hx. exists o'. split; [left; reflexivity|]. rewrite Hr. exact Hx.
      * intros (o2 & [<-|[]] & Hx). rewrite Hr in Hx. exact Hx.
  - apply xshadow_outside_cover; [exact Hsh|]. cbn [ss_objs set_obj_at set_objs].
    intros o2 x Ho2 Hx. apply in_app_or in Ho2 as [Ho2|[<-|Ho2]].
    + exists o2. split; [eapply In_firstn_In; exact Ho2 | exact Hx].
    + exists o. split; [exact Hin|]. rewrite <- Hr. exact Hx.
    + exists o2. split; [eapply In_skipn_In; exact Ho2 | exact Hx].
Qed.

Lemma obj_holds_shift : ltac2:(tb__ "0|2|
S8S5bS9S9S4S0S26S25R3A1S1aA3M0G0S0S4S37Q40M1SbR7S1eR4A1A2A2S43S37G1SbR7S1eR5A1A2A2R3A2A3S0S4S17R8R5A2S46S17R8R6A2R4A2A3S0S4S16R9R6A2S46S16R9R7A2R5A2A3S42S46S16RaR7A2S17RaR7A2A2S45Z2Z3fA2A2S5aSdSdSdSdS1S0S4S1dR1A1S1dR2A1A3S1S0S7S1cR1A1S1cR2A1A3S0S4S21RdS1bR1A1A2S46S21RdS1bR2A1A2R9A2A3A2A2Lc';Lc;S1fR9A1S1fR8A1A5S12S6RcRbRaA4S12S6RdRcRaA4F_;F_;F_;F_;F_;F_;F_;F_;Fd;Fo';Fo;Fms;Frho;").
Proof.
  intros rho ms o o' d Hd Hd' Hb Hlo Hhi Hsz HC (HB & Hw & Hcells & Hdf & Hinv).
  unfold obj_holds. cbv zeta. rewrite Hd'. rewrite Hd in Hw, Hdf, Hinv. cbn [dflt_writable dflt_holds dflt_inv] in Hw, Hdf, Hinv |- *.
  rewrite Hb, Hlo, Hhi.
  split; [lia|]. split.
  - intros off Hoff _. replace (bv_unsigned (eval rho (ob_base o)) + d + off) with (bv_unsigned (eval rho (ob_base o)) + (off + d)) by lia.
    apply Hw; [lia | reflexivity].
  - split.
    + clear Hw Hdf Hinv. revert HC Hcells. generalize (ob_cells o') as cs'. generalize (ob_cells o) as cs.
      induction 1 as [|c c' cs cs' (Ew & Ev & Eo) HC2 IH]; intros Hcs; [constructor|].
      inversion Hcs as [|? ? Hc Hcs']; subst. constructor; [|exact (IH Hcs')].
      destruct Hc as (C1 & C2 & C3). unfold cell_holds. rewrite Ew, Ev, Eo. split; [lia|]. split; [lia|].
      unfold oaddr in C3 |- *. rewrite Hb. replace (bv_unsigned (eval rho (ob_base o)) + d + (soff rho (c_off c) - d)) with (bv_unsigned (eval rho (ob_base o)) + soff rho (c_off c)) by lia.
      exact C3.
    + split; [|exact I]. intros off Hoff Hnc.
      replace (bv_unsigned (eval rho (ob_base o)) + d + off) with (bv_unsigned (eval rho (ob_base o)) + (off + d)) by lia.
      apply Hdf; [lia|]. intros HCov. apply Hnc. unfold covered in HCov |- *.
      apply Exists_exists in HCov as (c & Hinc & Hic). clear Hw Hdf Hinv Hcells.
      revert HC Hinc. generalize (ob_cells o') as cs'. generalize (ob_cells o) as cs.
      induction 1 as [|c0 c0' cs cs' (Ew & Ev & Eo) HC2 IH]; intros Hinc; [destruct Hinc|].
      destruct Hinc as [<-|Hinc].
      * apply Exists_cons_hd. unfold in_cell in Hic |- *. rewrite Eo, Ew. lia.
      * apply Exists_cons_tl. exact (IH Hinc).
Qed.

Lemma SPA_relist : ltac2:(tb__ "0|3|
S2aS8S39S35S7S7S7S5S5S2bS36Q40A1A1S4eS0S2fS9A1S59S9S10S3aR9A1A1R8A3S32S9S11R7R6R5S34SdA1M0S19R4A1M1A5A2A3S0S2dS6fS3aRaA1M2S52G2R9S11R8R7R6G0G1A5A3A2S2eA3S0S2bS36Q8A1A1SeRcR5A2SeRcR6A2A3S29S6ReRcRdR5R4A6S29S6RfS3dRdS52S3aRdA1RcS11RbRaR9G0S19R7A1A5A3A2ReR6R5A6F_;F_;F_;F_;Fw;Ftp;Fl';Fl;Fhi;Flo;Fb;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i b lo hi l l' tp w Hn Hsame Hrl HS.
  apply (SPA_reobj_same_range J rho A i (mkObj b lo hi [] (DList l)) (mkObj b lo hi [] (DList l')) tp w Hn Hsame eq_refl); [|exact HS].
  intros ms (HB & Hw & Hc & Hd & Hinv). unfold obj_holds, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  split; [exact HB|]. split; [exact Hw|]. split; [exact Hc|]. split.
  - intros off Hoff Hnc. cbn [dflt_holds]. rewrite Hrl. exact (Hd off Hoff Hnc).
  - cbn [dflt_inv] in Hinv |- *. rewrite Hrl. exact Hinv.
Qed.

Section HdrArith.
Variable F : list byte.
Variable rho : valuation.
Let b := bv_unsigned (rw rho 45%positive).
Let b0 := bv_unsigned (nth 0 F (Z_to_bv 8 0)).
Let b1 := bv_unsigned (nth 1 F (Z_to_bv 8 0)).
Let b2 := bv_unsigned (nth 2 F (Z_to_bv 8 0)).
Let b3 := bv_unsigned (nth 3 F (Z_to_bv 8 0)).
Hypothesis Hh : ltac2:(tb__ "0|0|
S0S4S44Vb;S45Z2Z20A2A2S56VF;A1A3").

Lemma hdr_bytes_rng : ltac2:(tb__ "0|2|
S1S1S41Z0M0Vb0;A2S42Vb0;Z100M1A2A2S1S1S41G0Vb1;A2S42Vb1;G1A2A2S1S1S41G0Vb2;A2S42Vb2;G1A2A2S1S41G0Vb3;A2S42Vb3;G1A2A2A2A2A2").
Proof.
  pose proof (bv_unsigned_in_range 8 (nth 0 F (Z_to_bv 8 0))). pose proof (bv_unsigned_in_range 8 (nth 1 F (Z_to_bv 8 0))).
  pose proof (bv_unsigned_in_range 8 (nth 2 F (Z_to_bv 8 0))). pose proof (bv_unsigned_in_range 8 (nth 3 F (Z_to_bv 8 0))).
  change (bv_modulus 8) with 256 in *. subst b0 b1 b2 b3. lia.
Qed.

Lemma hdr_low8 : b mod 256 = b0.
Proof.
  pose proof hdr_bytes_rng as (R0 & R1 & R2 & R3).
  assert (E : b mod 256 = (b mod 2 ^ 32) mod 256).
  { pose proof (Z.div_mod b (2 ^ 32) ltac:(lia)) as Hd. rewrite Hd at 1.
    replace (2 ^ 32 * (b / 2 ^ 32) + b mod 2 ^ 32) with (b mod 2 ^ 32 + (16777216 * (b / 2 ^ 32)) * 256) by lia.
    rewrite Z_mod_plus_full. reflexivity. }
  rewrite E, Hh. unfold hdr_word. fold b0 b1 b2 b3.
  replace (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3) with (b0 + (b1 + 256 * b2 + 65536 * b3) * 256) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma hdr_byte1 : ltac2:(tb__ "0|1|
S0S4S44S4aVb;Z100M0A2G0A2Vb1;A3").
Proof.
  pose proof hdr_bytes_rng as (R0 & R1 & R2 & R3).
  pose proof (Z.div_mod b (2 ^ 32) ltac:(lia)) as Hd. rewrite Hh in Hd. unfold hdr_word in Hd. fold b0 b1 b2 b3 in Hd.
  rewrite Hd at 1. change (2 ^ 32) with (256 * 16777216).
  replace (256 * 16777216 * (b / (256 * 16777216)) + (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3))
    with (b0 + (16777216 * (b / (256 * 16777216)) + b1 + 256 * b2 + 65536 * b3) * 256) by lia.
  rewrite Z.div_add by lia. rewrite (Z.div_small b0 256) by lia. rewrite Z.add_0_l.
  replace (16777216 * (b / (256 * 16777216)) + b1 + 256 * b2 + 65536 * b3) with (b1 + (65536 * (b / (256 * 16777216)) + b2 + 256 * b3) * 256) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma U_srl8 : ltac2:(tb__ "0|0|
S0S4S37Q40SbVrho;S14S79S24P2dA1SaZ8A1A3A2A2S4aVb;Z100A2A3").
Proof. cbn [eval]. rewrite srl_val. change (8 mod 64) with 8. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma land_shift8_small : ltac2:(tb__ "0|3|
S4S4S41Z0M0R2A2M1S1G1S42R2Z100M2A2A2S0S4S4cS4bR4G2A2R3A2G0A3F_;F_;Fc;Fm;").
Proof.
  intros m c Hm Hc. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8) as [Hlt|Hge].
  - change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. reflexivity.
  - rewrite (Z.bits_above_log2 c i); [apply andb_false_r | lia |].
    destruct (Z.eq_dec c 0) as [->|Hne]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|]. apply (Z.lt_le_trans _ (2 ^ 8)); [lia|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma lor_shift8_small : ltac2:(tb__ "0|3|
S4S4S41Z0R2A2M0S1G0S42R2Z100M1A2A2S0S4S4dS4bR4G1A2M2R3A2S43G2R3A2A3F_;F_;Fc;Fm;").
Proof.
  intros m c Hm Hc. rewrite <- Z.lxor_lor by (apply land_shift8_small; lia). symmetry. apply Z.add_nocarry_lxor. apply land_shift8_small; lia.
Qed.

Lemma U_flg_x : ltac2:(tb__ "0|1|
S0S4S37Q40SbVrho;S6bA2A2S2dS4L_;S49S55VF;A1M0Z80A2G0S46S43G0S45Z2Z40A2A2Z100A2X2dx2A3").
Proof.
  pose proof hdr_bytes_rng as (R0 & R1 & R2 & R3).
  unfold flg_x. cbn [eval].
  change (alu64 ALU_SRL (rw rho 45%positive) (Z_to_bv 64 8)) with (eval rho (SAlu ALU_SRL (SVar 45) (SLit 8))).
  rewrite (U_sext_w 8); [| reflexivity | cbv; discriminate]. rewrite U_srl8. change (Z.of_N 8) with 8. change (2 ^ 8) with 256. rewrite hdr_byte1.
  unfold zsext, flags_of. fold b1. change (2 ^ (8 - 1)) with 128. unfold M64v. destruct (b1 <? 128); lia.
Qed.

Lemma U_clen_x : ltac2:(tb__ "0|0|
S0S4S37Q40SbVrho;S64A2A2S54VF;A1A3").
Proof.
  pose proof hdr_bytes_rng as (R0 & R1 & R2 & R3). pose proof (urange (rw rho 45%positive)) as Rb. fold b in Rb.
  unfold clen_x. cbn [eval].
  change (alu64 ALU_SRL (rw rho 45%positive) (Z_to_bv 64 8)) with (eval rho (SAlu ALU_SRL (SVar 45) (SLit 8))).
  rewrite or_val_A, srl_val, sll_val. change (57 mod 64) with 57. change (49 mod 64) with 49.
  rewrite (U_sext_w 8); [| reflexivity | cbv; discriminate]. rewrite U_srl8. change (Z.of_N 8) with 8. change (2 ^ 8) with 256. rewrite hdr_byte1.
  rewrite (U_zext_w 8) by (cbv; discriminate). change (Z.of_N 8) with 8. change (2 ^ 8) with 256. fold b. rewrite hdr_low8.
  set (z := zsext 8 b1).
  assert (Hz : z mod 128 = b1 mod 128 /\ 0 <= z).
  { subst z. unfold zsext. change (2 ^ (8 - 1)) with 128. change (2 ^ 8) with 256. unfold M64v.
    destruct (Z.ltb_spec b1 128); split; try lia.
    all: replace (b1 + 18446744073709551616 - 256) with (b1 + (144115188075855871) * 128) by lia; rewrite Z_mod_plus_full; reflexivity. }
  destruct Hz as [Hzm Hz0].
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (2 ^ 64) with (128 * 2 ^ 57) by reflexivity.
  rewrite Z.mul_mod_distr_r by lia. rewrite Hzm.
  replace (2 ^ 57) with (2 ^ 8 * 2 ^ 49) by reflexivity. rewrite Z.mul_assoc, Z.div_mul by lia.
  change (2 ^ 8) with 256. pose proof (Z.mod_pos_bound b1 128 ltac:(lia)).
  rewrite lor_shift8_small by lia. unfold clen_of. fold b0 b1.
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2 ^ 7) with 128. lia.
Qed.

Lemma clen_of_range : 0 <= clen_of F <= 32767.
Proof.
  pose proof hdr_bytes_rng as (R0 & R1 & R2 & R3). unfold clen_of. fold b0 b1.
  change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2 ^ 7) with 128. pose proof (Z.mod_pos_bound b1 128 ltac:(lia)). lia.
Qed.

Lemma U_plen_x : ltac2:(tb__ "0|3|
S4S0S4S37Q40M0SfVrho;P65A2A2Z0A3S0S4S37G0SfVrho;P2aA2A2R2A3S41S43S54VF;A1M1Z6M2A2R3A2S42R4S45Z2Z3eA2A2S0S4S37G0SbVrho;S6eA2A2S46S46R5G2A2G1A2A3F_;F_;F_;F_;Flen;").
Proof.
  intros len H101 H32 Hcl Hlen. pose proof clen_of_range as HC.
  unfold plen_x. fold clen_x. rewrite U_add, U_sub, U_clen_x, !U_lit. cbn [eval]. rewrite H32. unfold M64v.
  rewrite (Z.mod_small (len - clen_of F)) by lia.
  replace ((-6) mod 18446744073709551616) with (18446744073709551616 - 6) by reflexivity.
  replace (len - clen_of F + (18446744073709551616 - 6)) with ((len - 6 - clen_of F) + 1 * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
End HdrArith.

Lemma SPA_JA_Kc : ltac2:(tb__ "0|3|
S75S8S2bS36Q40A1A1M0S5cOF_;F_;F_;F_;S2bS30S4S4A2M1A1M2G2S5S73S73S8S8OF_;G2S2bS30G1S4A2A1S82S75OF_;S72S39S8G0S4eS2bS5dA1S5cRfR2R1A2RfR3R2A2F_;Fmd;Ftr;S29S6S71R12R11R10RfReRcRbRaR9R8R7R6AcR5R4R3R2A6S29S6S71R13R12R11R10ReRdRcRbRaR9R8R7AcR6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fnd;FPA;FBX;FFF;FFB;FP0f;Frho0;FKc';FKc;FNP;FXGL;FCST;FAInv;").
Proof.
  intros AInv CST XGL NP Kc Kc' rho0 P0f FB FF BX PA nd A rho tp w HK [Hsm (Ai & kc & Hav & Hk & REST)].
  split; [exact Hsm|]. exists Ai, kc. split; [exact Hav|]. split; [apply HK; exact Hk | exact REST].
Qed.
End DrvRGlue.

(* [comment removed for export] *)
Module DrvTLXi_h.

From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA SummaryA GlueA CFGA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjUnbase ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface IfaceS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform MuslWLA DrvGlueA DrvGlueB DrvGlueC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceT Lib_fuzz_iface2 DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nl.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require o7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n7.Icpt_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memcpy_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_fuzz_iface2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nv.DrvT_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nl.DrvSiteS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o7.DrvTLX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import PFAddr MCAddr TAddr FZAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition optS'' := 0.
Definition optS' (x : option sstate) (d : sstate) : sstate := match x with Some s => s | None => d end.
Definition optA (x : option axst) (d : axst) : axst := match x with Some s => s | None => d end.
End DrvTLXi_h.

