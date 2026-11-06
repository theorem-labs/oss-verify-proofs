(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From Stdlib Require FunctionalExtensionality.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require DrvGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nu DrvTLXa.

(* [comment removed for export] *)
Module Lib_b_warn.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "None"; "bool"; "false"; "list"; "true"; "app"; "pair"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "mkA"; "A_globals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "sobj"; "sv"; "SPUle"; "FcsrFrm0"; "SPAlign"; "SVar"; "mkSS"; "valuation"; "DUnknown"; "SAlu"; "cell"; "mkObj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "vb"; "vERR"; "P_alloc"; "P_st"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "check_cfgA"; "check_ecfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_b_warn"; "Pre_bw"; "FUEL_bw"; "P_bw"; "Posts_bw"; "X_bw"; "bw_facts"; "bw_objs"; "cutpcs_bw"; "NXP_bw"; "O_wstk"; "cuts_bw"; "exits_bw"; "vcuts_bw"; "vexits_bw"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "LQA"; "SPA"; "jpredA"; "stableA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "leafA"; "mkLeafA"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_b_warn.BWarnAddr"; "bw_entry"; "bw_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "NPH"; "P_hdr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import RA.ReallocAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module BWarnAddr.
  Definition bw_entry : Z := 0xa0394.
  Definition bw_ret : Z := 0xa4530.
End BWarnAddr.
Import BWarnAddr.

Definition FUEL_bw : nat := 100%nat.
Definition NXP_bw : positive := 160%positive.

Definition O_wstk (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S1aS14PaA1SdN60A1SdZ0A1Vcells;S17A5").
Definition bw_facts : list sprop := ltac2:(tb__ "0|4|
S0SeS13PcZ4M0A2S0SeS11SdS48A1S1fA2S0SeS11S18S3eS1fSdZ518A1A3SdZ7fffff800000A1A2S0SeS11S1fSdS43A1M1A2S0SeS13PaM2G0A2S0SeS11SdZ10000A1S14G2A1M3A2S0SeS11G3G1A2S1SeA1A3A3A3A3A3A3A3").
Definition bw_objs (err : sv) : list sobj := ltac2:(tb__ "0|0|
S7SfS0SfS30S1S19A1A1S0SfS21S0SfS42S0SfS22Verr;A1S1SfA1A3A3A3A3ScA3").
Definition X_bw : list (sv * sv) := ltac2:(tb__ "0|1|
S0S9S10S10A2M0S8S10S10S1fSdZ518A1A4S1G0A1A3").

Definition Pre_bw : axst := ltac2:(tb__ "0|0|
SbS15S3fS1eS1cS12S2S10A1S2dS20A1S2cS41S4A9S2bA2").
Definition P_bw : axst := ltac2:(tb__ "0|0|
SbS15S40S1dS1bA1S1cS12S2S10A1S2dS20A1S2cS2fS4A9S2bA2").
Definition Posts_bw : list leafA := ltac2:(tb__ "0|0|
S0S3bS3cS29S47A2S1S3bA1A3").

Definition cuts_bw : list axst := [Pre_bw].
Definition exits_bw : list axst := [P_bw].
Definition cutpcs_bw : list Z := [].

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.

Lemma check_bw : ltac2:(tb__ "0|0|
S35S3S25SaS28S2eS1bS31S32A6S6A3").
Proof. vm_compute. reflexivity. Qed.

Theorem b_warn_sum : ltac2:(tb__ "0|0|
S46OF_;S38S16S5S3dQ40A1A1S3aSaR4R3A3S39SaS1bR4A3S45SaR6S37SaR5S27R4R3A5S36SaR5S1bR4R3S2aA6A4F_;F_;Ftp;Frho;FJ;Fok;").
Proof.
  intros ok J rho tp Hok Hst.
  eapply triple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_bw rho tp w Hw) | intros w Hw; exact Hw |].
  apply (cfg_soundA segs FUEL_bw cutpcs_bw NF cuts_bw exits_bw (withGA (fun r => agree_below NF rho r) J) ok
           (LQA segs J NF rho tp Posts_bw) tp).
  - intros r t tr ms md msv' [_ HJ]. eapply Hok; eauto.
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - exact check_bw.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    + apply exit_postA. in_nth 0.
  - left; reflexivity.
Qed.

Definition vcuts_bw : list vnodeA := ltac2:(tb__ "0|0|
S0S23S24S27Z1eSdZ0A1A3S1S23A1A3").
Definition vexits_bw : list vnodeA := ltac2:(tb__ "0|0|
S0S23S24S29Z1SdZ0A1A3S1S23A1A3").

Lemma echeck_bw : ltac2:(tb__ "0|0|
S35S3S26SaS28S2eS1bS33S34A6S6A3").
Proof. vm_compute. reflexivity. Qed.

Theorem b_warn_sum_ex : ltac2:(tb__ "0|0|
S38S16S5S3dQ40A1A1S39SaS1bR3A3S44SaS37SaR4S27R3R2A5S36SaR4S1bR3R2S2aA6A3F_;Ftp;Frho;FJ;").
Proof.
  intros J rho tp Hst.
  eapply etriple_conseq; [intros w Hw; exact (SPA_withG_intro segs J NF Pre_bw rho tp w Hw) | intros w Hw; exact Hw |].
  change Pre_bw with (vna_state (mkVNA Pre_bw 30 (SLit 0))).
  apply (cfg_complete_autoA segs FUEL_bw cutpcs_bw NF vcuts_bw vexits_bw (withGA (fun r => agree_below NF rho r) J)
           (LQA segs J NF rho tp Posts_bw) tp).
  - apply stableA_withG; [intros r1 r2 H1 H2; eapply agree_below_trans; eauto | exact Hst].
  - intros n Hin. destruct Hin as [<-|[]]; cbv; congruence.
  - exact echeck_bw.
  - intros E rhoE HinE. destruct HinE as [<-|[]].
    + apply (eexit_postA segs J NF rho vcuts_bw Posts_bw (mkVNA P_bw 1 (SLit 0))). in_nth 0.
  - left; reflexivity.
Qed.
End Lib_b_warn.

(* [comment removed for export] *)
Module Lib_realloc_rom_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bd_subst"; "bitem"; "bud_le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "ss_facts"; "holds"; "sobj"; "sprop"; "SLit"; "SVar"; "rm"; "ss_next"; "SPUle"; "SAlu"; "ss_objs"; "ob_base"; "sv_eqb"; "sstate"; "ob_hi"; "ob_lo"; "obj_range"; "sprop_below"; "swf"; "SPBranch"; "agree_below"; "eval"; "rw"; "obj_wf"; "soff"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "mul"; "pow"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "entailsA"; "ax_X"; "ax_setS"; "@Corelib.Init.Datatypes"; "bool"; "list"; "prod"; "true"; "pair"; "nil"; "nat"; "option"; "cons"; "Some"; "fst"; "snd"; "app"; "false"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_realloc_rom"; "vK"; "kb16"; "vP"; "tv1"; "vQ"; "ndR"; "vKn"; "bd1"; "pN"; "pls"; "B32"; "X_a2"; "q1"; "E_fa2"; "E_fp"; "X_step"; "tv0"; "E_fa1"; "E_freeT"; "X_a1"; "X_cp0"; "X_p"; "X_s"; "s_f"; "s_m"; "C_0"; "E_fc"; "E_free"; "E_ft"; "E_m"; "R_m"; "X_cp0f"; "X_t"; "bd0"; "s_cp0"; "s_post"; "s_step"; "vA"; "P0_rr"; "P_okX"; "R_f"; "VQ"; "X_c"; "X_cp0c"; "free_facts"; "step_facts"; "tv2"; "O_fs"; "P_fail"; "P_ok"; "Pre_m"; "Pre_rr"; "X_r"; "cp0_facts"; "cutsE"; "exitsE"; "tiles2"; "tvP"; "two47"; "E_ff"; "FUEL_rr"; "Pre_f"; "T_free"; "T_mnull"; "T_mok0"; "X_f"; "cutpcs_rr"; "eoff"; "sel7"; "sel8"; "vF0"; "vF1"; "vPn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "PTrue"; "nd_below"; "JA_pre"; "nd_tv"; "JA"; "ffinA"; "ok_frameKA"; "tvinA"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "AE_A"; "ulink"; "L_free"; "unwind_stopJ"; "JL_free"; "J_alloc_pre"; "J_free_pre"; "L_malloc_null"; "L_malloc_ok"; "Posts_malloc"; "Pre_free"; "Pre_malloc"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "etriple"; "triple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@Stdlib.Lists.List"; "In"; "nth_error"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "wsub_id_below"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena"; "rd64"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_realloc_rom_pf.Sum"; "Phi1"; "ptr0"; "Phi0"; "Phis"; "Posts_rr"; "K0"; "Kn0"; "Phi2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tnz"; "tvv"; "tv_sub_eqb"; "FBx"; "remove_nth"; "tvd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSelect"; "AXSplit"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_realloc_rom_pf"; "extraAL"; "o_src"; "extraFS"; "o_dstE"; "o_dstX"; "PDk_rr"; "Psi_fail"; "Psi_ok"; "extraX"; "o_nb"; "o_restX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "JAF"; "efmeasA"; "carve_site_chk"; "carve_ent_stateA"; "phiK"; "JLAP"; "ejcertAF"; "ent_obj"; "phi_reads"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "carve_stateA"; "drop_lastA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "is_shadowZ"; "site_okA"; "cmaddrA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CellTile"; "tiles_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "pclMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "PostsCk"; "keptR"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymCall ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena CellTile ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxArrA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_realloc_rom.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import RRAddr.

Definition o_src (q : sv) : sobj := ltac2:(tb__ "0|0|
SecS4dS46S45Vq;A1A2PadA2").
Definition o_restX : sobj := Eval vm_compute in nth 2 (ss_objs (ax_S X_s)) O_D.
Definition o_dstX : sobj := Eval vm_compute in last (ss_objs (ax_S X_p)) O_D.
Definition o_dstE : sobj := Eval vm_compute in last (ss_objs (ax_S E_fp)) O_D.
Definition o_nb : sobj := Eval vm_compute in nth 1 (ss_objs (ax_S X_cp0)) O_D.

Lemma T_mnull_eq : ltac2:(tb__ "0|0|
S1S2dSf3S76S61S5cS62Sa4S9dS36S9eA1S9cA3A5S83A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_mok0_eq : ltac2:(tb__ "0|0|
S1S2dSf3S76S61S5cS62Sa5S9dS36S9eA1S9cA3A5S84A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_free_eq : ltac2:(tb__ "0|0|
S1S2dSf3S81S56S5bS6cS9fS9dS36S9eA1S9cA3A5S82A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma X_eqs : ltac2:(tb__ "0|8|
S0S1S38S1aA1Sf7S2cS53A1S7cA2S3aS1aS2cS64A1A2A3S0S1S38S2dA1M0Sd4S85S39Sd3Sd6U1S11Z10A1A2S36Sd3A1M1A3A2S3aS2dS5aA2A3S0S1S38SfA1Sb6SfS17S2cS5aA1M2A1U2M3A3S3aSfSe4A2A3S0S1S2dS30S5aSfcG2G3S73S12S4cA1S50S4aA3A3A2S78A3S0S1G0Sd4S78S39Sd3Sd5S89A1G1A3A2S3aS2dS59A2A3S0S1S32SfA1M4S17S2cS59A1A1S3dSfS17S2cS57A1A1M5S39SfSdeS36SfA1M6A3A3A3S0S1S2dSefS59G5A2S57A3S0S1G4G5S3dSfS17S2cS4fA1A1M7S39SfSdbS48A1G6A3A3A3S0S1S2dSefS57G7A2S4fA3S1S2dSe8S4fS4dS46S45S50A1A2A2S6eA3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma E_eqs : ltac2:(tb__ "0|4|
S0S1S38S1aA1Sf7S2cS5fA1S7cA2S3aS1aS2cS60A1A2A3S0S1S38S2dA1Sd4S7fS39Sd3Sd5S88A1S36Sd3A1A3A2S3aS2dS52A2A3S0S1S32SfA1M0S17S2cS52A1A1S3dSfS17S2cS55A1A1M1S39SfSddS36SfA1M2A3A3A3S0S1S2dSefS52G1A2S55A3S0S1G0G1S3dSfS17S2cS51A1A1M3S39SfSdbS48A1G2A3A3A3S0S1S2dSefS55G3A2S51A3S1S2dSeeS51S46S45S44A1A3S5eA3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma cp0_eqs : ltac2:(tb__ "0|0|
S0S1S2dSe8S63S4dS46S45S11Z0A1A1A2A2S6fA3S1S38SfA1Sb6SfS17S2cS58A1A1U1A3S3aSfSe3A2A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition extraAL (o : sobj) : bool := ltac2:(tb__ "0|1|
S31S31L_;M0S19S18Vo;A1S69A2G0S19S1cVo;A1S11Z0A1A2S19S1bVo;A1S11Z30A1A2S3eX31x2S3eX31x2").
Definition extraFS (c : sv) (o : sobj) : bool := ltac2:(tb__ "0|1|
S31S31L_;M0S19S18Vo;A1S16Sd7S12S4cA1S45Vc;A1A3A2G0S19S1cVo;A1S11Z0A1A2S19S1bVo;A1S45S16Sd8S4aVc;A3A1A2S3eX31x2S3eX31x2").
Definition extraX (o : sobj) : bool := ltac2:(tb__ "0|0|
S31S31L_;SdaVo;A1S34SdcS50Vo;A2X31x2").

Lemma chk_X : ltac2:(tb__ "0|2|
S0S1S31S1fS2cSeeS4fS4dS46S45S50A1A2S11Z10A1A3A1A1S34A3S0S1S31Se7S4fS47S36S33S33ScS5A2ScA2A1U1Se2A5S34A3S0S1S31S93S14S2cS4fA1A1S49S47S4bA2M0A2S34A3S0S1S31S2eS6eS5dS68A3S34A3S0S1S31SbeS68S90A2S34A3S0S1S31ScfS68S47S47A3S34A3S0S1S31S93S14S2cS6eA1M1A1G0A2S34A3S0S1S31SaSdG1A1S8S68S4bA2S4bA3S34A3S0S1S31S24S14S2cS5aA1A1S73S12S4cA1S50S4aA3A2S34A3S1S31Sb7S10S1eS14S2cS64A1A1A1S71A3S34A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma chk_E : ltac2:(tb__ "0|2|
S0S1S31S1fS2cSeeS51S46S45S44A1A3A1A1S34A3S0S1S31Se7S51S47S36S33S33ScS5A2ScA2A1U1SdaA5S34A3S0S1S31S2eS5eS56S36S33S6ScA2A1M0A3S34A3S0S1S31ScfG0S47S47A3S34A3S0S1S31S93S14S2cS5eA1M1A1S49S47S4bA2A2S34A3S0S1S31SaSdG1A1S8G0S4bA2S4bA3S34A3S1S31Sb7S10S1eS14S2cS60A1A1A1S70A3S34A3A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma chk_cp0 : ltac2:(tb__ "0|2|
S0S1S31S1fS2cSeeS63S4dS46S45S11Z0A1A1A2S11Z10A1A3A1A1S34A3S0S1S31Se7S63S47S36S33S33ScS5A2ScA2A1U1SdaA5S34A3S0S1S31S93S14S2cS63A1A1S49S47S4bA2M0A2S34A3S0S1S31S2eS6fS5dS66A3S34A3S0S1S31SbeS66S90A2S34A3S0S1S31ScfS66S47S47A3S34A3S0S1S31S93S14S2cS6fA1M1A1G0A2S34A3S0S1S31SaSdG1A1S8S66S4bA2S4bA3S34A3S1S31Sb7S10S1eS14S2cS58A1A1A1S79A3S34A3A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma chk_post : ltac2:(tb__ "0|2|
S0S1S31S2eS6bS75S67A3S34A3S0S1S31SbeS67S90A2S34A3S0S1S31ScfS67S72S7dA3S34A3S0S1S31S93S14S2cS6bA1M0A1S49S72S36S9A1M1A2A2S34A3S1S31SaSdG0A1S8S67G1A2G1A3S34A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Ltac meas := unfold efmeasA; cbn [ef_rank ef_var fst snd];
  match goal with |- context [bv_unsigned (eval ?r ?e)] => pose proof (urange (eval r e)); lia end.
Tactic Notation "innth" integer(k) := do k right; left; reflexivity.

Lemma kb16_exact : ltac2:(tb__ "0|0|
SbScS26S7R2R1A2S4eA2S1S5S7R3S45R2A1A2S29Z10S7R3R2A2A2A3F_;Fe;Frho;").
Proof. intros rho e H. unfold kb16, B32 in *. apply uval_mul_lit; lia. Qed.

Lemma VQ_val : ltac2:(tb__ "0|1|
SbS5S0S26Z0R1A2S26R1Z20M0A2A2S28S7R3S48A2S7R3S44A2A2S26S7R4S44A2S4eA2S1S5S7R5S6dR4A1A2S2bS29G0S2bS27S27S7eZ1A2S7R5S44A2A2S7R5S48A2A2A2R4A2A3F_;F_;F_;Fc;Frho;").
Proof.
  intros rho c Hc HqK HK. unfold VQ, two47, B32 in *. pose proof (uval_range rho vQ) as RQ. pose proof (uval_range rho vK) as RK.
  assert (EA : uval rho (SAlu ALU_ADD (SLit (2 ^ 47 + 1)) vK) = 2 ^ 47 + 1 + uval rho vK).
  { rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity. }
  assert (ES : uval rho (SAlu ALU_SUB (SAlu ALU_ADD (SLit (2 ^ 47 + 1)) vK) vQ) = 2 ^ 47 + 1 + uval rho vK - uval rho vQ).
  { unfold uval in *. rewrite U_sub. rewrite EA. unfold M64v. apply Z.mod_small. lia. }
  assert (EM : uval rho (SMd M_MUL (SLit 32) (SAlu ALU_SUB (SAlu ALU_ADD (SLit (2 ^ 47 + 1)) vK) vQ)) = 32 * (2 ^ 47 + 1 + uval rho vK - uval rho vQ)).
  { rewrite uval_mul_lit by (rewrite ?ES; lia). rewrite ES. reflexivity. }
  unfold uval in *. rewrite U_sub, U_lit, EM. unfold M64v. rewrite (Z.mod_small c) by lia. apply Z.mod_small. lia.
Qed.
Lemma meas_VQ : ltac2:(tb__ "0|2|
S2dS91S37S5S5SbS0S26Z0R2A2S26R2Z20M0A2A2S28S7R2S48A2S7R2S44A2A2S26S7R3S44A2S4eA2S1S5Se6S35S33S33S2dS91A2M1S37A2S33S5ScA2S35G1S37S35S2dS91R9R8A4R7A4S35S5ScR6S6dR5A1A4A4R4A2S27S29R6S2aZ2Z40A2A2S2bS29G0S2bS27S27S7eZ1A2S7R4S44A2A2S7R4S48A2A2A2R5A2A2A3F_;F_;F_;Frho;Fc;Frk;Fk;Fnd;FT;").
Proof. intros T nd k rk c rho Hc HqK HK. unfold efmeasA. cbn [ef_rank ef_var fst snd]. change (bv_unsigned (eval rho (VQ c))) with (uval rho (VQ c)). rewrite (VQ_val rho c Hc HqK HK). reflexivity. Qed.

Lemma blocks_arith : ltac2:(tb__ "0|17|
SbSeR1S20Sd9S48S44A3A2SeR2S15S48S11S4eA1M0A2A2SeR3S15S11Z1M1A1S44A2A2SeR4S20Sd9S44S4aA3A2SeR5S15S4aG0A2A2SeR6S15S11Z1000M2A1M3S12S4cA1M4A2A2SeR7S15S16Sd7G4S45S4aA1M5A3S11Z7fffff800000M6A1M7A2A2SeR8S15G3S46A2A2SeR9S15S16Sd7S46S45S44A1M8A3S12P1eA1M9A2A2SeRaS15G9G7A2A2SeRbS15S46S11Z800000000000A1A2A2SeRcS15G4G7A2A2SeRdS15G5G0A2A2S0S28S7ReS48A2MaS7ReS44A2MbA2S0S28GbS7ReS4aA2McA2S0S26S29Z10MdGcA2MeS4eA2S0S26G1GbA2S0S1S5S7ReS45S48A1MfA2S29GdGaA2M10A3S0S1S5S7ReG8A2S29GdGbA2M11A3S0S1S5S7ReG5A2GeA3S0S5S0S26Z0R1A2S26R1Z40A2A2S1S5S7R10S87R2A1A2S27S29GdS7R10S48A2A2R2A2A3F_;Fj;S0S1S5S7ReS50A2S27GaG1A2A3S0S1S5S7ReS45S50A1M12A2S27G10GdA2A3S0S1S5S7ReS16Sd7S16Sd8G8GfA3S11N10A1A3A2S2bS2bG11G10A2GdA2A3S0S26G2S7ReG4A2M13A2S0S26S27G13GeA2G6A2S0S26G2S7ReS46A2M14A2S0S26S27G14G11A2G6A2S0S1S5S7ReS4dG4GfA2A2S27G13G10A2M15A3S0S1S5S7ReS4dS46GfA2A2S27G14G10A2M16A3S0S1S5S7ReS4dG4G12A2A2S27G15GdA2A3S0S1S5S7ReS4dS46G12A2A2S27G16GdA2A3S0ScS26S7RfR1A2S7RfS4aA2A2S1S5S7R10S45S16Sd8S4aR2A3A1A2S2bS29GdS7R10S4aA2A2S29GdS7R10R2A2A2A2A3F_;Fq;S1S5S7ReS4dG4G8A2A2S27G13G11A2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frho;").
Proof.
  intros rho H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13. zf H1. zf H2. zf H3. zf H4. zf H5. zf H6. zf H7. zf H8. zf H9. zf H10. zf H11. zf H12. zf H13.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. unfold B32 in *.
  rewrite uval_lit in H2, H3, H5, H6, H7, H8, H10, H11, H12, H13 by lia.
  pose proof (uval_range rho vQ) as RQ. pose proof (uval_range rho vK) as RK. pose proof (uval_range rho vKn) as RKn.
  pose proof (uval_range rho (SVar pN)) as RN. pose proof (uval_range rho vP) as RP. pose proof (uval_range rho (SVar 30)) as R30.
  assert (EQ : uval rho (kb16 vQ) = 16 * uval rho vQ) by (apply kb16_exact; unfold B32; lia).
  assert (EK : uval rho (kb16 vK) = 16 * uval rho vK) by (apply kb16_exact; unfold B32; lia).
  assert (EKn : uval rho (kb16 vKn) = 16 * uval rho vKn) by (apply kb16_exact; unfold B32; lia). rewrite EKn in H13.
  rewrite uval_add_small in H7 by (rewrite EKn; lia). rewrite EKn in H7.
  rewrite uval_add_small in H9 by (rewrite EK; lia). rewrite EK in H9.
  assert (E1 : uval rho q1 = uval rho vQ + 1) by (unfold q1; rewrite uval_add_small by (rewrite uval_lit by lia; lia); rewrite uval_lit by lia; reflexivity).
  assert (E1k : uval rho (kb16 q1) = 16 * uval rho vQ + 16) by (rewrite kb16_exact by (unfold B32; lia); lia).
  repeat (split; [lia|]).
  split; [intros j Hj; unfold eoff; rewrite uval_add_small by (rewrite EQ, uval_lit by lia; lia); rewrite EQ, uval_lit by lia; reflexivity|].
  split; [exact E1|]. split; [exact E1k|].
  split.
  { unfold uval in *. rewrite U_add, U_sub, U_lit, EK, EQ. unfold M64v. rewrite Zplus_mod_idemp_l.
    change ((-16) mod 18446744073709551616) with 18446744073709551600.
    replace (16 * bv_unsigned (eval rho vK) - 16 * bv_unsigned (eval rho vQ) + 18446744073709551600) with ((16 * bv_unsigned (eval rho vK) - 16 * bv_unsigned (eval rho vQ) - 16) + 1 * 18446744073709551616) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  repeat (split; [lia|]).
  unfold pls. rewrite !uval_add_small by (rewrite ?EQ, ?E1k, ?EK; lia). rewrite EQ, E1k, EK.
  repeat (split; [lia|]). split; [|lia].
  intros q Hq. pose proof (uval_range rho q).
  assert (ES : uval rho (SAlu ALU_SUB vKn q) = uval rho vKn - uval rho q) by (unfold uval in *; rewrite U_sub; unfold M64v; apply Z.mod_small; lia).
  rewrite kb16_exact by (rewrite ES; unfold B32; lia). rewrite ES. lia.
Qed.

Ltac blocks HF :=
  let r := match type of HF with Forall (holds ?r) _ => r end in
  let H1 := fresh in let H2 := fresh in let H3 := fresh in let H4 := fresh in let H5 := fresh in let H6 := fresh in
  let H7 := fresh in let H8 := fresh in let H9 := fresh in let H10 := fresh in let H11 := fresh in let H12 := fresh in let H13 := fresh in
  fact HF (SPBranch BC_LTU vQ vK) H1; fact HF (SPUle vQ (SLit B32)) H2; fact HF (SPUle (SLit 1) vK) H3;
  fact HF (SPBranch BC_LTU vK vKn) H4; fact HF (SPUle vKn (SLit B32)) H5;
  fact HF (SPUle (SLit 4096) (SVar pN)) H6; fact HF (SPUle (SAlu ALU_ADD (SVar pN) (kb16 vKn)) (SLit 140737479966720)) H7;
  fact HF (SPUle (SLit 4096) vP) H8; fact HF (SPUle (SAlu ALU_ADD vP (kb16 vK)) (SVar 30)) H9; fact HF (SPUle (SVar 30) (SLit 140737479966720)) H10;
  fact HF (SPUle vP (SLit 140737488355328)) H11; fact HF (SPUle (SVar pN) (SLit 140737479966720)) H12; fact HF (SPUle (kb16 vKn) (SLit B32)) H13;
  destruct (blocks_arith _ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13)
    as (?LqK & ?LKKn & ?LKn & ?LK1 & ?EQ16 & ?EK16 & ?EKn16 & ?Eoff & ?Eq1 & ?Eq1k & ?Erem & ?LN1 & ?LN2 & ?LP1 & ?LP2 & ?EdN & ?EdP & ?EdN1 & ?EdP1 & ?Efs & ?EdNK);
  clear H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13;
  pose proof (uval_range r vQ); pose proof (uval_range r vK); pose proof (uval_range r vKn); pose proof (uval_range r (SVar pN)); pose proof (uval_range r vP).

Lemma step_facts_ok : ltac2:(tb__ "0|0|
SbS9aS10SeR1A1SdS2cS64A1A1A3S9aS10SeR2A1S71A3F_;Frho;").
Proof.
  intros rho HF. blocks HF.
  fact HF (SPBranch BC_NE (kb16 vK) (eoff 16)) HNE.
  apply (proj1 (holds_bne _ _ _)) in HNE. change (bv_unsigned (eval rho ?a) <> bv_unsigned (eval rho ?b)) with (uval rho a <> uval rho b) in HNE.
  rewrite EK16, (Eoff 16) in HNE by lia.
  unfold step_facts, fs_facts. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
  - apply (proj2 (holds_bltu _ _ _)). change (uval rho q1 < uval rho vK). rewrite Eq1. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite (Eoff 32), EK16 by lia. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite (Eoff 32), EKn16 by lia. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite uval_lit, (Efs q1) by lia. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite uval_lit, (Efs q1) by (unfold B32; lia). unfold B32 in *. lia.
Qed.

Lemma cp0_facts_ok : ltac2:(tb__ "0|0|
SbS9aS10SeR1A1SdS2cS58A1A1A3S9aS10SeR2A1S79A3F_;Frho;").
Proof.
  intros rho HF.
  fact HF (SPUle (SLit 1) vK) H3. fact HF (SPBranch BC_LTU vK vKn) H4. fact HF (SPUle vKn (SLit B32)) H5. fact HF (SPUle (kb16 vKn) (SLit B32)) H6. zf H3. zf H4. zf H5. zf H6.
  repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. unfold B32 in *. rewrite uval_lit in H3, H5, H6 by lia.
  pose proof (uval_range rho vK) as RK. pose proof (uval_range rho vKn) as RKn.
  assert (EK : uval rho (kb16 vK) = 16 * uval rho vK) by (apply kb16_exact; unfold B32; lia).
  assert (EKn : uval rho (kb16 vKn) = 16 * uval rho vKn) by (apply kb16_exact; unfold B32; lia). rewrite EKn in H6.
  assert (ES : uval rho (SAlu ALU_SUB vKn (SLit 0)) = uval rho vKn).
  { unfold uval in *. rewrite U_sub, U_lit. unfold M64v. change (0 mod 18446744073709551616) with 0. rewrite Z.sub_0_r. apply Z.mod_small. lia. }
  assert (EF : uval rho (kb16 (SAlu ALU_SUB vKn (SLit 0))) = 16 * uval rho vKn) by (rewrite kb16_exact by (rewrite ES; unfold B32; lia); lia).
  unfold cp0_facts, fs_facts. constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
  - apply (proj2 (holds_bltu _ _ _)). change (uval rho (SLit 0) < uval rho vK). rewrite uval_lit by lia. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite EK, uval_lit by lia. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite EKn, uval_lit by lia. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite EF, uval_lit by lia. lia.
  - apply (proj2 (h_ule _ _ _)). rewrite EF, uval_lit by (unfold B32; lia). unfold B32 in *. lia.
Qed.

Lemma free_facts_ok : ltac2:(tb__ "0|0|
SbS9aS10SeR1A1SdS2cS60A1A1A3S9aS10SeR2A1S70A3F_;Frho;").
Proof.
  intros rho HF. blocks HF.
  fact HF (SPNot (SPBranch BC_NE (kb16 vK) (eoff 16))) HEQ.
  apply (proj1 (holds_nbne _ _ _)) in HEQ. change (bv_unsigned (eval rho ?a) = bv_unsigned (eval rho ?b)) with (uval rho a = uval rho b) in HEQ.
  rewrite EK16, (Eoff 16) in HEQ by lia.
  unfold free_facts. constructor; [|constructor].
  apply (proj2 (h_ule _ _ _)). rewrite Eq1. lia.
Qed.

Lemma soff_u : ltac2:(tb__ "0|0|
SbScS28S7R2R1A2S2aZ2Z3fA2A2S1S5S25R3R2A2S7R3R2A2A3F_;Fe;Frho;").
Proof. intros rho e H. apply soff_smallu. exact H. Qed.

Lemma U_Z_to_bv : ltac2:(tb__ "0|1|
S5S0S26Z0R1A2S28R1S2aZ2Z40A2A2A2S1S5S43Q40M0S42G0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. apply u64_of_sum. exact Hz. Qed.

Lemma rd64_pair_bytes : ltac2:(tb__ "0|7|
S41Q40M0A1S38S41Q8A1A1M1F_;M2G2S5S5S5S5S1S38S5A1M3Sc3R6R4A2S3aS5R2A2M4A3S1G3Sc3R7S27R5Z8M5A2A2G4A3S1G3Sc3R7R5A2S3aS5R4A2M6A3S1G3Sc3R8S27R6G5A2A2G6A3S5S0S26Z0R1A2S28R1Z10A2A2S1G1RcS42G0S27RaR2A2A2A1RbS42G0S27R9R2A2A2A1A3F_;Fi;F_;F_;F_;F_;Fv1;Fv0;Fb;Fa;Fm2;Fm1;").
Proof.
  intros m1 m2 a b v0 v1 A0 A1 B0 B1 i Hi.
  destruct (Z_lt_dec i 8) as [L|L].
  - replace (a + i) with (a + Z.of_nat (Z.to_nat i)) by lia. replace (b + i) with (b + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (rd64_enc_bytes m1 a v0 A0) by lia. rewrite (rd64_enc_bytes m2 b v0 B0) by lia. reflexivity.
  - replace (a + i) with (a + 8 + Z.of_nat (Z.to_nat (i - 8))) by lia. replace (b + i) with (b + 8 + Z.of_nat (Z.to_nat (i - 8))) by lia.
    rewrite (rd64_enc_bytes m1 (a + 8) v1 A1) by lia. rewrite (rd64_enc_bytes m2 (b + 8) v1 B1) by lia. reflexivity.
Qed.

Definition Psi_fail (r0 rho : valuation) : Prop := ltac2:(tb__ "0|2|
S5S0S26S7Vr0;S46A2M0R1A2S28R1S27G0S29Z10S7Vr0;S44A2A2A2A2A2S1S38S41Q8A1A1S13Vrho;S42Q40R2A2M1A2S13Vr0;G1A2A3F_;Fz;").
Definition Psi_ok (r0 rho : valuation) : Prop := ltac2:(tb__ "0|8|
S0S5S0S26Z0R1A2M0S28R1S29Z10M1S7Vr0;S44A2A2A2A2S0S1S38S41Q8A1M2A1M3S13Vrho;S42Q40M4S27S7Vrho;S8cA2R2A2A2A2M5S13Vr0;S42G4S27S7Vr0;S46A2R2A2A2A2M6A3S2S1G3G6S3fG2A1M7A3A1A2F_;Fj;S5S0G0S28R1S29G1S7Vr0;S4aA2A2A2A2S2S1G3G5G7A3A1F_;Fj;A2").
Definition PDk_rr : list pdescK := ltac2:(tb__ "0|4|
S39S33S33S2dS91A2M0SbSbOFrho;Fr0;M1A2M2S35G0G1S35S2dS91S74S49S54S36S9A1M3A2A4Se0A4S39G2S35G0G1S35S2dS91S75S49S7dG3A2A4Se1A4S36G2A1A3A3").

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sb8SbS32S41Q40A1A1Sb9OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
SabS40VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S5SfaVCST;R1A2S0S26Z0R2A2S28R2Sf0A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S5SfaVXGL;R1A2S0S26Z0R2A2S28R2Sf0A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S32S33S33S5S5A2S5A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 2 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nn.Lib_arena_alloc.HTOP_ok.
Let P0 := P0_rr FB FF.

Definition Posts_rr : list (axst * jpostA) := ltac2:(tb__ "0|0|
SffVAInv;VCST;VXGL;VKc;S6aS92SdfVFB;VFF;VBX;Aa").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S96VAInv;VCST;VXGL;S90VKc;Vrho0;VP0;VFB;VFF;VBX;S92Vnd;Ac").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
Sb1S40S90Vrho0;Vtp0;Sc9A5").

Definition ptr0 : Z := uval rho0 vP.
Definition K0 : Z := uval rho0 vK.
Definition Kn0 : Z := uval rho0 vKn.
Definition Phi0 (rho : valuation) : Prop := ltac2:(tb__ "0|1|
S5S0S26Sc6R1A2S28R1S27Sc6S29Z10ScaA2A2A2A2S1S38S41Q8A1A1S13Vrho;S42Q40R2A2M0A2S13Vrho0;G0A2A3F_;Fz;").
Definition Phi1 (rho : valuation) : Prop := ltac2:(tb__ "0|5|
S0Sc7Vrho;A1S0S5S0S26Z0R1A2S28R1S29Z10S7Vrho;S48A2A2M0A2A2S1S38S41Q8A1A1S13Vrho;S42Q40M1S27S7Vrho;S12S4cA1A2R2A2A2A2S13Vrho0;S42G1S27Sc6R2A2A2A2A3F_;Fj;S0S1S38S5A1M2Sc3S13Vrho;A1M3S27Sc6G0A2M4A2S3aS5S7Vrho;S8aA2A2A3S1G2Sc3G3S27G4Z8A2A2S3aS5S7Vrho;S8bA2A2A3A2A2A2").
Definition Phi2 (rho : valuation) : Prop := ltac2:(tb__ "0|6|
S0S5S0S26Z0R1A2M0S28R1S29Z10M1ScaA2A2A2S1S38S41Q8A1M2A1M3S13Vrho;S42Q40M4S27S7Vrho;S12S4cA1A2R2A2A2A2M5S13Vrho0;S42G4S27Sc6R2A2A2A2A3F_;Fj;S5S0G0S28R1S29G1ScbA2A2A2S2S1G3G5S3fG2A1A3A1F_;Fj;A2").
Definition Phis : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|5|
S39S33S32S6A1M0SbOFrho;M1A2M2S35G0G1S36S6A1M3Sc7A4S39G2S35G0G1S39S6P6fM4S39S6PacS39S6PadS39S6PaeG3A3A3A3A3Sc5A4S39G2S35G0G1S39S6G4G3A3SccA4S36G2A1A3A3A3").
Let JAFv (k : nat) (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
Se5VAInv;VCST;VXGL;S90VKc;Vrho0;VP0;VFB;VFF;VBX;S92Se9Sc8Vk;A2Vnd;Ad").

Lemma uval_rw : ltac2:(tb__ "0|1|
SbSbS6S1S41Q40A1S23R3R1A2S23R2R1A2A3S1S5S7R3S12R2A1M0A2S7R4G0A2A3F_;Fv;Frho';Frho;").
Proof. intros rho rho' v H. unfold uval. cbn [eval]. rewrite H. reflexivity. Qed.

Lemma Phis_reads : ltac2:(tb__ "0|3|
S9aS33S32S6A1M0SbOF_;M1A2M2G2SedS3bG0G1R1A3S3cG0G1R1A3A2Lp;Sc8A3").
Proof.
  unfold Phis. constructor; [|constructor; [|constructor; [|constructor]]]; cbn [fst snd]; unfold Phi2, Phi1, Phi0.
  - intros rho rho' _ _ HM H z Hz. rewrite <- HM. exact (H z Hz).
  - intros rho rho' HV _ HM (H0 & H1 & H2 & H3).
    assert (E111 : uval rho' (SVar pN) = uval rho (SVar pN)) by (apply uval_rw; apply HV; cbn; tauto).
    assert (E172 : uval rho' vQ = uval rho vQ) by (apply uval_rw; apply HV; cbn; tauto).
    assert (E173 : uval rho' vF0 = uval rho vF0) by (apply uval_rw; apply HV; cbn; tauto).
    assert (E174 : uval rho' vF1 = uval rho vF1) by (apply uval_rw; apply HV; cbn; tauto).
    rewrite E111, E172, E173, E174. split; [|split; [|split]].
    + intros z Hz. rewrite <- HM. exact (H0 z Hz).
    + intros j Hj. rewrite <- HM. exact (H1 j Hj).
    + rewrite (rd64_ext (rm rho) (rm rho')); [exact H2 | intros z _; symmetry; apply HM].
    + rewrite (rd64_ext (rm rho) (rm rho')); [exact H3 | intros z _; symmetry; apply HM].
  - intros rho rho' HV _ HM [H1 H2].
    assert (E111 : uval rho' (SVar pN) = uval rho (SVar pN)) by (apply uval_rw; apply HV; cbn; tauto).
    rewrite E111. split; intros j Hj; rewrite <- HM; [exact (H1 j Hj) | exact (H2 j Hj)].
Qed.

Lemma ejcertAF_ok : ltac2:(tb__ "0|0|
S1S31SebS40S90Sc8S80S86P64S7aS7bA8S34A3").
Proof. rewrite (ejcertAF_V segs NF Phis PhisV FUEL_rr cutpcs_rr 100 cutsE exitsE eq_refl). exact ejcertAF_ok0. Qed.

Lemma JA_P0 : ltac2:(tb__ "0|0|
S91S2dSbS32S41Q40A1A1SadS8dS40VJAv;R5A1R4R3R2R1A6S0VP0;Vrho0;A1Sc0S90Vrho0;R4A3A2F_;Fw;Ftp;Frho;FS;Fnd;").
Proof. intros nd S rho tp [tr [ms md]] [_ (Ai & kc & HJ)]. pose proof HJ as (Hav & _ & _ & _ & _ & _ & _ & _ & _ & HP0 & _). split; [exact HP0 | exact Hav]. Qed.

Lemma tracked_disjoint0 : ltac2:(tb__ "0|7|
Sb8SbS32S41Q40A1A1Sb9SbS32S33ScScA2M0A1S37S37G0G0VAInv;RaR9R8R7A4S99VFB;RbR7R6A4Sd2R8R7A2S1S38G0A1M1Sb6G0R8R7A3S3aG0R5A2M2A3S1G1Sb6G0R9R7A3G2A3S2S1S37R9R8A3A1ScdRcR8A2ScdRdR8A2S3S26S27S3bS5S5SceReRaA2M3A3M4S3cS5S5G3A3A2S3bS5S5SceReR9A2M5A3M6A2S26S27G6S3cS5S5G5A3A2G4A2A2F_;F_;F_;F_;F_;F_;F_;F_;Ftj;Fti;Fj;Fi;Ftv;Frho;Fm1;Ft1;Fr1;FAi;").
Proof.
  intros Ai r1 t1 m1 rho tv i j ti tj HM HN HD Hi Hj Hij Hzi Hzj.
  pose proof (tvd_nth rho _ i j ti tj HD Hi Hj Hij Hzi Hzj) as NE.
  destruct (proj1 (Forall_forall _ _) HN ti (nth_error_In _ _ Hi) Hzi) as (_ & Li & _).
  destruct (proj1 (Forall_forall _ _) HN tj (nth_error_In _ _ Hj) Hzj) as (_ & Lj & _).
  destruct (law_blocks' segs AInv CST ALA HCST Ai r1 t1 m1 HM) as (HPD & _ & _).
  apply In_nth_error in Li as [i1 Hi1]. apply In_nth_error in Lj as [i2 Hi2].
  destruct (Nat.eq_dec i1 i2) as [->|Hne12]; [exfalso; apply NE; rewrite Hi1 in Hi2; injection Hi2 as E1 E2; unfold tvv; rewrite E1, E2; reflexivity|].
  assert (Hi1' : nth_error (aa_live Ai ++ aa_frames Ai) i1 = Some (tvv rho ti)) by (rewrite nth_error_app1; [exact Hi1 | apply nth_error_Some; congruence]).
  assert (Hi2' : nth_error (aa_live Ai ++ aa_frames Ai) i2 = Some (tvv rho tj)) by (rewrite nth_error_app1; [exact Hi2 | apply nth_error_Some; congruence]).
  exact (pd_elems _ _ _ _ _ HPD Hi1' Hi2' Hne12).
Qed.
Lemma tracked_disjoint : ltac2:(tb__ "0|7|
S91SbS32S41Q40A1A1S32SbaA1Sb9S37S37S33ScScA2M0G0VJAv;R9R8R7R6R5A5S1S38G0A1M1Sb6G0S95RaA1R5A3S3aG0R3A2M2A3S1G1Sb6G0S95RbA1R5A3G2A3S2S1S37R7R6A3A1ScdRcR6A2ScdRdR6A2S3S26S27S3bS5S5SceReR8A2M3A3M4S3cS5S5G3A3A2S3bS5S5SceReR7A2M5A3M6A2S26S27G6S3cS5S5G5A3A2G4A2A2F_;F_;F_;F_;F_;F_;Ftj;Fti;Fj;Fi;Fmd;Ftr;Ftp;Frho;Fnd;").
Proof.
  intros nd rho tp tr md i j ti tj (Ai & kc & HJ) Hi Hj Hij Hzi Hzj.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & _).
  exact (tracked_disjoint0 Ai rho tp md rho _ i j ti tj HM HN HD Hi Hj Hij Hzi Hzj).
Qed.

Lemma al_extra_sound : ltac2:(tb__ "0|1|
SbS32SfA1S32S33ScScA2A1S32S33S33ScS5A2ScA2A1SfS5Sc0S90Vrho0;R6A3VP0;Vrho0;A1Sb5SfR4R7A3S1S31SdaR5A1S34A3S0S26S3bS5S5S1dRaR6A2M0A3R5A2S28R5S3cS5S5G0A3A2A2S3Sf9VCST;Vrho0;Sd0VFB;RbR9A3Sf8VFF;RbR8A3R6A5S3S0S26Z0R6A2S28R6Sf0A2A2Sf4R6A1A2A2F_;F_;F_;F_;F_;Fa;Fo;Ffr;Ftv';Fobjs;Frho;").
Proof.
  intros rho objs tv' fr o a Hav [(f & s & fl & Hin & H1 & H2) _] _ HE Hr. left.
  unfold extraAL in HE. apply lazy_andb_prop in HE as [Hb HE]. apply lazy_andb_prop in HE as [Hl Hh].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh. unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr. cbn [fst snd] in Hr.
  rewrite !soff_lit_small in Hr by lia.
  assert (E12 : rw rho 12%positive = rw rho0 12%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  unfold vA in Hr. cbn [eval] in Hr. rewrite E12 in Hr.
  right; right; right. exists f, s, fl. split; [apply In_FFx; left; exact Hin | lia].
Qed.

Lemma fs_extra_sound : ltac2:(tb__ "0|2|
SbScSfS5S26S7R4R3A2S7R4S4aA2A2S26S7R5S4aA2S4eA2S26Z1000S7R6S12S4cA1M0A2A2S26S27S7R7G0A2S29Z10S7R7S4aA2A2A2Z7fffff800000A2S1S31SdcR7R6A2S34A3S0S26S3bS5S5S1dR9R7A2M1A3R6A2S28R6S3cS5S5G1A3A2A2S3Sf9VCST;Vrho0;Sd0VFB;RaSd1S33ScScA2U1S47A3A3Sf8VFF;RaS36S33S33ScS5A2ScA2A1A3R7A5S3S0S26Z0R7A2S28R7Sf0A2A2Sf4R7A1A2A2F_;F_;F_;F_;F_;F_;Fa;Fo;Fc;Frho;").
Proof.
  intros rho c o a Hc HKn HN1 HN2 HE Hr. left. right; right; left.
  unfold extraFS in HE. apply lazy_andb_prop in HE as [Hb HE]. apply lazy_andb_prop in HE as [Hl Hh].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  pose proof (uval_range rho c) as Rc. pose proof (uval_range rho vKn) as RKn. unfold B32 in HKn.
  assert (Ec : uval rho (kb16 c) = 16 * uval rho c) by (apply kb16_exact; unfold B32; lia).
  assert (ES : uval rho (SAlu ALU_SUB vKn c) = uval rho vKn - uval rho c) by (unfold uval in *; rewrite U_sub; unfold M64v; apply Z.mod_small; lia).
  assert (Eh : uval rho (kb16 (SAlu ALU_SUB vKn c)) = 16 * uval rho vKn - 16 * uval rho c) by (rewrite kb16_exact by (rewrite ES; unfold B32; lia); lia).
  assert (EKn : uval rho (kb16 vKn) = 16 * uval rho vKn) by (apply kb16_exact; unfold B32; lia).
  assert (Eb : uval rho (SAlu ALU_ADD (SVar pN) (kb16 c)) = uval rho (SVar pN) + 16 * uval rho c) by (rewrite uval_add_small by (rewrite Ec; lia); lia).
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr. cbn [fst snd] in Hr.
  rewrite soff_lit_small in Hr by lia. rewrite (soff_u rho (kb16 (SAlu ALU_SUB vKn c))) in Hr by (rewrite Eh; lia).
  change (bv_unsigned (eval rho ?e)) with (uval rho e) in Hr. rewrite Eb, Eh in Hr.
  exists (uval rho (SVar pN)), (uval rho (kb16 vKn)). split; [|rewrite EKn; lia].
  apply In_FBx. right. exists (SVar pN, kb16 vKn). split; [left; reflexivity|]. split; [|reflexivity].
  unfold tnz. cbn [fst]. change (bv_unsigned (eval rho (SVar pN))) with (uval rho (SVar pN)). lia.
Qed.

Lemma agree_uval : ltac2:(tb__ "0|1|
S6SbSbS6S21R4R3R2A3SfbR2R5A2S1S5S7R4S12R3A1M0A2S7R5G0A2A3F_;F_;Fv;Frho';Frho;Fn;").
Proof. intros n rho rho' v (A & _ & _) Hv. unfold uval. cbn [eval]. rewrite <- (A v Hv). reflexivity. Qed.
Lemma agree_rm : ltac2:(tb__ "0|0|
S6SbSbS21R3R2R1A3S41Q40A1S1S38S41Q8A1A1S13R3R1A2S13R4R1A2A3Fa;F_;Frho';Frho;Fn;").
Proof. intros n rho rho' (_ & _ & C) a. symmetry. apply C. Qed.
Lemma vals_uval : ltac2:(tb__ "0|1|
SbS6Sc0S90Vrho0;R2A3SfbR2S90A2S1S5S7R4S12R3A1M0A2S7Vrho0;G0A2A3F_;F_;Fv;Frho;").
Proof. intros rho v Hav Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. Qed.

Lemma cp0_glue : ltac2:(tb__ "0|2|
SbS32S41Q40A1A1SadSc7R3A1S8dS40VJAv;S49S47S4bA2A1M0S58R4R3R2A6S4SbSbS0Sc5R1A1S0S1S5S7R1S44A2S7R6S44A2M1A3S0S1S5S7R1S48A2Z0A3S0S0S26Z1G1A2S26G1S4eA2A2S8dS40G0S5dR1R5R4A6A2A2A2A2Lr';A2F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp [tr [ms md]] HPhi Hw.
  destruct (JA_P0 _ _ _ _ _ Hw) as [HP0 Hav]. pose proof (smatchA_facts segs _ _ _ _ (proj1 Hw)) as HF.
  pose proof chk_cp0 as (Cwf & Csite & Cnb & Cent & Cid & Ctv & Cnb2 & Cbud & Cfb).
  fact HF (SPUle (SLit 1) vK) H3. fact HF (SPBranch BC_LTU vK vKn) H4. fact HF (SPUle vKn (SLit B32)) H5. fact HF (SPUle vP (SLit 140737488355328)) H6.
  zf H3. zf H4. zf H5. zf H6. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. unfold B32 in *. rewrite uval_lit in H3, H5, H6 by lia.
  pose proof (uval_range rho vK) as RK. pose proof (uval_range rho vP) as RP.
  assert (EK : uval rho (kb16 vK) = 16 * uval rho vK) by (apply kb16_exact; unfold B32; lia).
  assert (EB : uval rho (pls vP (kb16 (SLit 0))) = uval rho vP).
  { unfold pls, kb16. rewrite uval_add_small; rewrite uval_mul_lit, uval_lit by (rewrite ?uval_lit; lia); lia. }
  assert (EP : uval rho vP = ptr0) by (unfold ptr0; exact (vals_uval rho 13 Hav ltac:(reflexivity))).
  assert (EKK : uval rho vK = K0) by (unfold K0; exact (vals_uval rho 14 Hav ltac:(reflexivity))).

  assert (Hw1 : SPA segs (JAv (ndR tv1 bd1)) X_cp0f rho tp (tr, mkCfg ms md)).
  { unfold X_cp0f, ax_add_facts. apply (SPA_refacts_JA segs _ rho X_cp0 (cp0_facts ++ ss_facts (ax_S X_cp0))); [exact Hw | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
    intros tr' md' _ HF'. apply Forall_app. split; [exact (cp0_facts_ok rho HF') | exact HF']. }

  destruct (JA_carve_ent segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue HKc HNP tv1 [] bd1 ANone 1 vP (kb16 vK)
              (pls vP (kb16 (SLit 0))) X_cp0f rho tp tr ms md eq_refl eq_refl Cwf ltac:(apply (proj1 (Pos.leb_le _ _)); reflexivity) Cnb)
    as (r1 & Hag & R0 & R1 & SP1).
  { intros r HFr. apply Forall_app in HFr as [_ HFr].
    fact HFr (SPUle (SLit 1) vK) Q3. fact HFr (SPBranch BC_LTU vK vKn) Q4. fact HFr (SPUle vKn (SLit B32)) Q5. fact HFr (SPUle vP (SLit 140737488355328)) Q6.
    zf Q3. zf Q4. zf Q5. zf Q6. repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. unfold B32 in *. rewrite uval_lit in Q3, Q5, Q6 by lia.
    pose proof (uval_range r vK). pose proof (uval_range r vP).
    assert (EKr : uval r (kb16 vK) = 16 * uval r vK) by (apply kb16_exact; unfold B32; lia).
    assert (EBr : uval r (pls vP (kb16 (SLit 0))) = uval r vP).
    { unfold pls, kb16. rewrite uval_add_small; rewrite uval_mul_lit, uval_lit by (rewrite ?uval_lit; lia); lia. }
    rewrite EBr, EKr. lia. }
  { apply (carve_site_chk_sound segs AInv CST ALA HCST NF rho0 P0 FB FF X_cp0f tv1 [] 1%nat extraAL rho Csite).
    intros Ai tp1 md1 _ HP0' Hav' _ _ _ _ _ _ _ _ _ o a Ho HE Hr. exact (al_extra_sound rho _ _ _ o a Hav' HP0' Ho HE Hr). }
  { intros z Hz. rewrite EB, EP in Hz. rewrite (HPhi z) by (unfold K0 in *; lia). apply (proj2 HP0). unfold ptr0, K0 in *. lia. }
  { exact Hw1. }
  rewrite (proj1 cp0_eqs) in SP1. change (ss_next (ax_S X_cp0f)) with 141%positive in Hag, R0, R1. change (Pos.succ 141) with 142%positive in R1.
  rewrite EB, EP in R0, R1.
  exists (rho_sub r1 s_cp0).
  assert (E14 : uval (rho_sub r1 s_cp0) vK = uval rho vK) by (etransitivity; [|exact (agree_uval _ rho r1 14 Hag ltac:(reflexivity))]; reflexivity).
  assert (E172 : uval (rho_sub r1 s_cp0) vQ = 0) by (etransitivity; [|exact (uval_lit r1 0 ltac:(lia))]; reflexivity).
  assert (E111 : uval (rho_sub r1 s_cp0) (SVar pN) = uval rho (SVar pN)) by (etransitivity; [|exact (agree_uval _ rho r1 pN Hag ltac:(reflexivity))]; reflexivity).
  assert (E173 : uval (rho_sub r1 s_cp0) vF0 = uval r1 (SVar 141)) by reflexivity.
  assert (E174 : uval (rho_sub r1 s_cp0) vF1 = uval r1 (SVar 142)) by reflexivity.
  assert (EM : rm (rho_sub r1 s_cp0) = rm r1) by reflexivity.
  split; [|split; [exact E14 | split; [exact E172 | split; [lia|]]]].
  - unfold Phi1, Phi0. rewrite E172, E111, E173, E174, EM. split; [|split; [|split]].
    + intros z Hz. rewrite (agree_rm _ _ _ Hag). exact (HPhi z Hz).
    + intros j Hj. lia.
    + rewrite Z.mul_0_r, Z.add_0_r. rewrite (rd64_ext (rm rho) (rm r1)) by (intros z _; apply (agree_rm _ _ _ Hag)). exact R0.
    + rewrite Z.mul_0_r, Z.add_0_r. rewrite (rd64_ext (rm rho) (rm r1)) by (intros z _; apply (agree_rm _ _ _ Hag)). exact R1.
  - apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc X_cp0c C_0 s_cp0 (ndR tv1 bd1) (ndR tv1 bd1) r1 tp _ Cent Cid);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Cnb2 | exact Ctv | reflexivity | exact Cbud | reflexivity | exact SP1].
Qed.

Lemma cont_lt : ltac2:(tb__ "0|0|
SbS9aS10SeR1A1SdS2cS53A1A1A3S28S27S7R2S48A2Z1A2S7R2S44A2A2F_;Frho;").
Proof.
  intros rho HF. blocks HF.
  fact HF (SPBranch BC_NE (kb16 vK) (eoff 16)) HNE.
  apply (proj1 (holds_bne _ _ _)) in HNE. change (bv_unsigned (eval rho ?a) <> bv_unsigned (eval rho ?b)) with (uval rho a <> uval rho b) in HNE.
  rewrite EK16, (Eoff 16) in HNE by lia. lia.
Qed.
Lemma facts_X_p : ltac2:(tb__ "0|3|
S0S1S32S10A1M0SdS2cS59A1A1M1S3dS10S71SdS2cS53A1A1M2A3A3S0S1G0SdS2cS57A1A1G1A3S0S1G0SdS2cS4fA1A1G1A3S0S1G0SdS2cS5aA1A1G1A3S1G0SdS2cS64A1A1G2A3A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma rng_dstX : ltac2:(tb__ "0|3|
SbS9aS10SeR1A1SdS2cS59A1A1A3S0S26S7R2S12S4cA1A2M0S7R2S18SdeA1A2M1A2S0S26S27G1S7R2S11Z10A1A2M2A2S27G0S7R2S45S4aA1A2A2A2S28Z0G2A2A2A2F_;Fr;").
Proof.
  intros r HFr. rewrite (proj1 facts_X_p) in HFr. apply Forall_app in HFr as [_ HF]. pose proof (cont_lt r HF) as HqK. blocks HF.
  cbn [ob_base o_dstX]. change (SAlu ALU_ADD (SVar 111) (SMd M_MUL (SLit 16) (SVar 172))) with (pls (SVar pN) (kb16 vQ)).
  rewrite EdN, EKn16, uval_lit by lia. lia.
Qed.
Lemma rng_srcX : ltac2:(tb__ "0|2|
SbS9aS10SeR1A1SdS2cS57A1A1A3S0S26S7R2S46A2M0S7R2S18SdbS48A1A1A2M1A2S26S27G1Z10A2S27G0S7R2S45S44A1A2A2A2A2F_;Fr;").
Proof.
  intros r HFr. rewrite (proj1 (proj2 facts_X_p)), (proj1 facts_X_p) in HFr. apply Forall_app in HFr as [_ HF]. blocks HF.
  cbn [ob_base o_src ent_obj]. rewrite EdP, EK16. lia.
Qed.
Lemma rng_nxtX : ltac2:(tb__ "0|2|
SbS9aS10SeR1A1SdS2cS4fA1A1A3S0S26S7R2S46A2M0S7R2S4dS46S45S50A1A2A2M1A2S26S27G1Z10A2S27G0S7R2S45S44A1A2A2A2A2F_;Fr;").
Proof.
  intros r HFr. rewrite (proj1 (proj2 (proj2 facts_X_p))), (proj1 facts_X_p) in HFr. apply Forall_app in HFr as [_ HF]. pose proof (cont_lt r HF) as HqK. blocks HF.
  rewrite EdP1, EK16. lia.
Qed.
Lemma fs_boundsX : ltac2:(tb__ "0|2|
SbS9aS10SeR1A1SdS2cS4fA1A1A3S0S26S7R2S50A2S7R2S4aA2M0A2S0S26G0S4eA2S0S26Z1000S7R2S12S4cA1A2M1A2S26S27G1S29Z10G0A2A2Z7fffff800000A2A2A2A2F_;Fr;").
Proof.
  intros r HFr. rewrite (proj1 (proj2 (proj2 facts_X_p))), (proj1 facts_X_p) in HFr. apply Forall_app in HFr as [_ HF]. pose proof (cont_lt r HF) as HqK. blocks HF.
  rewrite Eq1. unfold B32 in *. lia.
Qed.

Lemma step_glue : ltac2:(tb__ "0|3|
SbS32S41Q40A1A1SadSc5R3A1S8dS40VJAv;S49S47S4bA2A1M0S53R4R3R2A6S4SbSbS0Sc5R1A1S0S1S5S7R1S44A2S7R6S44A2M1A3S0S1S5S7R1S48A2S27S7R6S48A2Z1A2M2A3S0S28G2G1A2S0S26G1S4eA2S8dS40G0S5dR1R5R4A6A2A2A2A2A2Lr';A2F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp [tr [ms md]] (HP0i & HPc & HR0 & HR1) Hw.
  destruct (JA_P0 _ _ _ _ _ Hw) as [HP0 Hav]. pose proof (smatchA_facts segs _ _ _ _ (proj1 Hw)) as HF.
  pose proof chk_X as (Cwf & Csite & Cnb & Cent & Cid & Ctv & Cnb2 & Cbud & Cwf2 & Cfb).
  pose proof X_eqs as (Xt & Xs & Xn2 & Xr & Xp & Xo1 & Xd1 & Xo2 & Xd2 & Xc).
  pose proof facts_X_p as (Fp & Fa1 & Fa2 & Fs & Ft).
  pose proof (cont_lt rho HF) as HqK. blocks HF.
  assert (EP : uval rho vP = ptr0) by (unfold ptr0; exact (vals_uval rho 13 Hav ltac:(reflexivity))).
  assert (EKK : uval rho vK = K0) by (unfold K0; exact (vals_uval rho 14 Hav ltac:(reflexivity))).

  pose proof (SPA_tiles segs (JAv (ndR tv1 bd1)) rho tiles2 X_step (ax_S X_t) tp _ Xt Hw) as Hw1. change (ax_setS X_step (ax_S X_t)) with X_t in Hw1.
  assert (Hw2 : SPA segs (JAv (ndR tv1 bd1)) X_f rho tp (tr, mkCfg ms md)).
  { unfold X_f, ax_add_facts. apply (SPA_refacts_JA segs _ rho X_t (step_facts ++ ss_facts (ax_S X_t))); [exact Hw1 | exact Cfb |].
    intros tr' md' _ HF'. apply Forall_app. split; [exact (step_facts_ok rho HF') | exact HF']. }
  pose proof (SPA_axforms segs (JAv (ndR tv1 bd1)) [AXSplit 1 (SLit 16)] rho X_f X_s tp _ Xs Hw2) as Hw3.
  assert (Hw4 : SPA segs (JAv (ndR tv1 bd1)) X_r rho tp (tr, mkCfg ms md)).
  { rewrite <- Xr. apply (SPA_reshape segs _ rho X_s 2 o_restX (O_fs (SVar pN) q1 vKn) tp _ Xn2); [reflexivity | reflexivity | reflexivity | exact Cwf2 | | exact Hw3].
    intros _. unfold obj_lo_of, obj_hi_of, O_fs, o_restX. cbn [ob_base ob_lo ob_hi].
    change (SMd M_MUL (SLit 16) (SAlu ALU_SUB (SVar 33) (SVar 172))) with (kb16 (SAlu ALU_SUB vKn vQ)).
    change (SAlu ALU_ADD (SVar 111) (SMd M_MUL (SLit 16) (SVar 172))) with (pls (SVar pN) (kb16 vQ)).
    change (SAlu ALU_ADD (SVar pN) (kb16 q1)) with (pls (SVar pN) (kb16 q1)).
    repeat change (bv_unsigned (eval rho ?e)) with (uval rho e). rewrite !soff_lit_small by lia.
    rewrite (soff_u rho (kb16 (SAlu ALU_SUB vKn q1))) by (rewrite Efs by lia; lia). rewrite (soff_u rho (kb16 (SAlu ALU_SUB vKn vQ))) by (rewrite Efs by lia; lia).
    rewrite !Efs by lia. rewrite EdN1, EdN, Eq1. lia. }
  pose proof (SPA_axforms segs (JAv (ndR tv1 bd1)) [AXSelect sel8] rho X_r X_p tp _ Xp Hw4) as Hw5.

  assert (NZ1 : tnz rho (SVar pN, kb16 vKn)) by (unfold tnz; cbn [fst]; change (bv_unsigned (eval rho (SVar pN))) with (uval rho (SVar pN)); lia).
  assert (NZ2 : tnz rho (vP, kb16 vK)) by (unfold tnz; cbn [fst]; change (bv_unsigned (eval rho vP)) with (uval rho vP); lia).
  assert (DISJ : uval rho (SVar pN) + 16 * uval rho vKn <= uval rho vP \/ uval rho vP + 16 * uval rho vK <= uval rho (SVar pN)).
  { destruct Hw5 as [_ HJ]. cbn [w_tr w_cfg cfg_model snd fst] in HJ.
    pose proof (tracked_disjoint (ndR tv1 bd1) rho tp tr md 0 1 (SVar pN, kb16 vKn) (vP, kb16 vK) HJ eq_refl eq_refl ltac:(lia) NZ1 NZ2) as D.
    unfold tvv in D. cbn [fst snd] in D. repeat change (bv_unsigned (eval rho ?e)) with (uval rho e) in D. rewrite EKn16, EK16 in D. exact D. }

  destruct (JA_absorb_tr segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue tv1 [] bd1 ANone 0 (SVar pN) (kb16 vKn)
              X_p (ss_objs (ax_S X_a1)) o_dstX (SLit 16) rho tp tr ms md Xo1 eq_refl eq_refl eq_refl eq_refl rng_dstX Hw5) as (Hw6 & OUT2 & DEF2 & CELLS2).
  rewrite Xd1 in Hw6. cbn [ob_base o_dstX] in OUT2, DEF2, CELLS2.
  change (SAlu ALU_ADD (SVar 111) (SMd M_MUL (SLit 16) (SVar 172))) with (pls (SVar pN) (kb16 vQ)) in OUT2, DEF2, CELLS2.
  rewrite EdN, (uval_lit rho 16) in OUT2, DEF2, CELLS2 by lia.
  set (rho2 := rho_absorb rho [o_dstX] (vms md tp ms)) in *.
  assert (UV2 : forall e, uval rho2 e = uval rho e) by (intros e; unfold uval, rho2; rewrite eval_absorb; reflexivity).
  assert (OLD2 : forall z, uval rho vP <= z < uval rho vP + 16 * uval rho vK -> rm rho2 (Z_to_bv 64 z) = rm rho (Z_to_bv 64 z)).
  { intros z Hz. apply OUT2. rewrite U_Z_to_bv by lia. lia. }
  pose proof (CELLS2 0 vF0 ltac:(cbn; tauto) ltac:(lia) ltac:(lia)) as C0. rewrite Z.add_0_r in C0. change (uval rho vF0) with (uval rho vF0) in C0.
  pose proof (CELLS2 8 vF1 ltac:(cbn; tauto) ltac:(lia) ltac:(lia)) as C1.

  destruct (JA_absorb_ent_same segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue tv1 [] bd1 ANone 1 vP (kb16 vK)
              X_a1 (ss_objs (ax_S X_a2)) (o_src vQ) vF0 vF1 rho2 tp tr ms md Xo2 eq_refl eq_refl eq_refl eq_refl ltac:(cbn; tauto) ltac:(cbn; tauto) rng_srcX) as [Hw7 RM3].
  { cbn [ob_base o_src ent_obj]. rewrite !UV2, EdP. rewrite (rd64_ext (rm rho) (rm rho2)) by (intros z Hz; apply OLD2; lia). rewrite EP. exact HR0. }
  { cbn [ob_base o_src ent_obj]. rewrite !UV2, EdP. rewrite (rd64_ext (rm rho) (rm rho2)) by (intros z Hz; apply OLD2; lia). rewrite EP. exact HR1. }
  { exact Hw6. }
  rewrite Xd2 in Hw7. set (rho3 := rho_absorb rho2 [o_src vQ] (vms md tp ms)) in *.
  assert (UV3 : forall e, uval rho3 e = uval rho e) by (intros e; etransitivity; [|apply UV2]; unfold uval, rho3; rewrite eval_absorb; reflexivity).

  destruct (JA_carve_ent segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue HKc HNP tv1 [] bd1 ANone 1 vP (kb16 vK)
              (pls vP (kb16 q1)) X_a2 rho3 tp tr ms md eq_refl eq_refl Cwf ltac:(apply (proj1 (Pos.leb_le _ _)); reflexivity) Cnb)
    as (r4 & Hag & Q0 & Q1 & SP4).
  { exact rng_nxtX. }
  { apply (carve_site_chk_sound segs AInv CST ALA HCST NF rho0 P0 FB FF X_a2 tv1 [] 1%nat extraX rho3 Csite).
    intros Ai tp1 md1 HFa HP0' Hav' _ _ _ _ _ _ _ _ _ o a Ho HE Hr. unfold extraX in HE. apply lazy_orb_prop in HE as [HE|HE].
    - exact (al_extra_sound rho3 _ _ _ o a Hav' HP0' Ho HE Hr).
    - destruct (fs_boundsX rho3 HFa) as (B1 & B2 & B3 & B4). exact (fs_extra_sound rho3 q1 o a B1 B2 B3 B4 HE Hr). }
  { intros z Hz. rewrite UV3, EdP1 in Hz. unfold rho3. rewrite RM3. rewrite OLD2 by lia. rewrite EP, EKK in *. rewrite (HP0i z) by lia. apply (proj2 HP0). unfold ptr0, K0 in *. lia. }
  { exact Hw7. }
  rewrite Xc in SP4. change (ss_next (ax_S X_a2)) with 210%positive in Hag, Q0, Q1. change (Pos.succ 210) with 211%positive in Q1.
  rewrite UV3, EdP1, EP in Q0, Q1.
  assert (RM4 : forall a, rm r4 a = rm rho3 a) by (apply (agree_rm _ _ _ Hag)).
  exists (rho_sub r4 s_step).
  assert (E14 : uval (rho_sub r4 s_step) vK = uval rho vK).
  { etransitivity; [|apply UV3]. etransitivity; [|exact (agree_uval _ rho3 r4 14 Hag ltac:(reflexivity))]. reflexivity. }
  assert (E172 : uval (rho_sub r4 s_step) vQ = uval rho vQ + 1).
  { rewrite <- Eq1, <- (UV3 q1). transitivity (uval r4 q1); [reflexivity|]. unfold uval. rewrite <- (eval_agree 210 rho3 r4 q1 Hag eq_refl). reflexivity. }
  assert (E111 : uval (rho_sub r4 s_step) (SVar pN) = uval rho (SVar pN)).
  { etransitivity; [|apply UV3]. etransitivity; [|exact (agree_uval _ rho3 r4 pN Hag ltac:(reflexivity))]. reflexivity. }
  assert (E173 : uval (rho_sub r4 s_step) vF0 = uval r4 (SVar 210)) by reflexivity.
  assert (E174 : uval (rho_sub r4 s_step) vF1 = uval r4 (SVar 211)) by reflexivity.
  assert (EM : rm (rho_sub r4 s_step) = rm r4) by reflexivity.
  split; [|split; [exact E14 | split; [exact E172 | split; [lia | split; [unfold B32 in *; lia|]]]]].
  - unfold Phi1, Phi0. rewrite E172, E111, E173, E174, EM. split; [|split; [|split]].
    + intros z Hz. rewrite RM4. unfold rho3. rewrite RM3. rewrite OLD2 by (rewrite EP, EKK; lia). exact (HP0i z Hz).
    + intros j Hj. rewrite RM4. unfold rho3. rewrite RM3.
      destruct (Z_lt_dec j (16 * uval rho vQ)) as [L|L].
      * rewrite OUT2 by (rewrite U_Z_to_bv by lia; lia). apply HPc. lia.
      * replace (uval rho (SVar pN) + j) with (uval rho (SVar pN) + 16 * uval rho vQ + (j - 16 * uval rho vQ)) by lia.
        rewrite (rd64_pair_bytes (rm rho2) (rm rho) _ _ (uval rho vF0) (uval rho vF1) C0 C1 HR0 HR1 (j - 16 * uval rho vQ)) by lia.
        replace (ptr0 + 16 * uval rho vQ + (j - 16 * uval rho vQ)) with (ptr0 + j) by lia. apply HP0i. rewrite <- EKK. lia.
    + rewrite (rd64_ext (rm rho3) (rm r4)) by (intros z _; apply RM4). replace (ptr0 + 16 * (uval rho vQ + 1)) with (ptr0 + 16 * uval rho vQ + 16) by lia. exact Q0.
    + rewrite (rd64_ext (rm rho3) (rm r4)) by (intros z _; apply RM4). replace (ptr0 + 16 * (uval rho vQ + 1) + 8) with (ptr0 + 16 * uval rho vQ + 16 + 8) by lia. exact Q1.
  - apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc X_c C_0 s_step (ndR tv1 bd1) (ndR tv1 bd1) r4 tp _ Cent Cid);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Cnb2 | exact Ctv | reflexivity | exact Cbud | reflexivity | exact SP4].
Qed.

Lemma facts_E_p : ltac2:(tb__ "0|3|
S0S1S32S10A1M0SdS2cS52A1A1M1S3dS10S70SdS2cS5fA1A1M2A3A3S0S1G0SdS2cS55A1A1G1A3S0S1G0SdS2cS51A1A1G1A3S0S1G0SdS2cS60A1A1G2A3S0S1G0SdS2cS5eA1A1G1A3S1G0SdS2cS56A1A1G1A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma lastK : ltac2:(tb__ "0|0|
SbS9aS10SeR1A1SdS2cS52A1A1A3S1S5S7R2S44A2S27S7R2S48A2Z1A2A3F_;Fr;").
Proof.
  intros r HFr. rewrite (proj1 facts_E_p) in HFr. apply Forall_app in HFr as [H1 HF]. blocks HF.
  apply Forall_inv in H1. zf H1. rewrite Eq1 in H1. lia.
Qed.
Lemma rng_dstE : ltac2:(tb__ "0|3|
SbS9aS10SeR1A1SdS2cS52A1A1A3S0S26S7R2S12S4cA1A2M0S7R2S18SddA1A2M1A2S0S26S27G1S7R2S45S16Sd8S4aS48A3A1A2M2A2S27G0S7R2S45S4aA1A2A2A2S28Z0G2A2A2A2F_;Fr;").
Proof.
  intros r HFr. rewrite (proj1 facts_E_p) in HFr. apply Forall_app in HFr as [_ HF]. blocks HF.
  cbn [ob_base o_dstE]. change (SAlu ALU_ADD (SVar 111) (SMd M_MUL (SLit 16) (SVar 172))) with (pls (SVar pN) (kb16 vQ)).
  rewrite EdN, EKn16, Efs by lia. lia.
Qed.
Lemma rng_srcE : ltac2:(tb__ "0|2|
SbS9aS10SeR1A1SdS2cS55A1A1A3S0S26S7R2S46A2M0S7R2S18SdbS48A1A1A2M1A2S26S27G1Z10A2S27G0S7R2S45S44A1A2A2A2A2F_;Fr;").
Proof.
  intros r HFr. rewrite (proj1 (proj2 facts_E_p)), (proj1 facts_E_p) in HFr. apply Forall_app in HFr as [_ HF]. blocks HF.
  cbn [ob_base o_src ent_obj]. rewrite EdP, EK16. lia.
Qed.
Lemma rng_oldE : ltac2:(tb__ "0|3|
SbS9aS10SeR1A1SdS2cS51A1A1A3S0S26S7R2S46A2M0G0A2S0S26S27G0S7R2S45S44A1A2M1A2M2G2A2S28Z0G1A2A2A2F_;Fr;").
Proof.
  intros r HFr. rewrite (proj1 (proj2 (proj2 facts_E_p))), (proj1 facts_E_p) in HFr. apply Forall_app in HFr as [_ HF]. blocks HF. rewrite EK16. lia.
Qed.

Lemma free_glue : ltac2:(tb__ "0|1|
SbS32S41Q40A1A1SadSc5R3A1S8dS40VJAv;S49S47S4bA2A1M0S5fR4R3R2A6S4SbSbS0SccR1A1S0S2S1S5S7R1S12S4cA1A2Z0A3A1S0S1S5S7R1S45S4aA1A2S29Z10ScbA2A3S0S28ScaScbA2S8dS40G0S56R1R5R4A6A2A2A2A2Lr';A2F_;F_;Fw;Ftp;Frho;").
Proof.
  intros rho tp [tr [ms md]] (HP0i & HPc & HR0 & HR1) Hw.
  destruct (JA_P0 _ _ _ _ _ Hw) as [HP0 Hav]. pose proof (smatchA_facts segs _ _ _ _ (proj1 Hw)) as HF.
  pose proof chk_E as (Cwf & Csite & Cent & Ctv & Cnb2 & Cbud & Cfb).
  pose proof E_eqs as (Xt & Xp & Xo1 & Xd1 & Xo2 & Xd2 & Xc).
  pose proof facts_E_p as (Fp & Fa1 & Fa2 & Ft & Fc & FT).
  blocks HF.
  assert (EP : uval rho vP = ptr0) by (unfold ptr0; exact (vals_uval rho 13 Hav ltac:(reflexivity))).
  assert (EKK : uval rho vK = K0) by (unfold K0; exact (vals_uval rho 14 Hav ltac:(reflexivity))).
  assert (EKN : uval rho vKn = Kn0) by (unfold Kn0; exact (vals_uval rho 33 Hav ltac:(reflexivity))).

  pose proof (SPA_tiles segs (JAv (ndR tv1 bd1)) rho tiles2 E_free (ax_S E_ft) tp _ Xt Hw) as Hw1. change (ax_setS E_free (ax_S E_ft)) with E_ft in Hw1.
  assert (Hw2 : SPA segs (JAv (ndR tv1 bd1)) E_ff rho tp (tr, mkCfg ms md)).
  { unfold E_ff, ax_add_facts. apply (SPA_refacts_JA segs _ rho E_ft (free_facts ++ ss_facts (ax_S E_ft))); [exact Hw1 | exact Cfb |].
    intros tr' md' _ HF'. apply Forall_app. split; [exact (free_facts_ok rho HF') | exact HF']. }
  pose proof (SPA_axforms segs (JAv (ndR tv1 bd1)) [AXSelect sel7] rho E_ff E_fp tp _ Xp Hw2) as Hw5.
  pose proof (smatchA_facts segs _ _ _ _ (proj1 Hw5)) as HF5. pose proof (lastK rho HF5) as HK.

  assert (NZ1 : tnz rho (SVar pN, kb16 vKn)) by (unfold tnz; cbn [fst]; change (bv_unsigned (eval rho (SVar pN))) with (uval rho (SVar pN)); lia).
  assert (NZ2 : tnz rho (vP, kb16 vK)) by (unfold tnz; cbn [fst]; change (bv_unsigned (eval rho vP)) with (uval rho vP); lia).
  assert (DISJ : uval rho (SVar pN) + 16 * uval rho vKn <= uval rho vP \/ uval rho vP + 16 * uval rho vK <= uval rho (SVar pN)).
  { destruct Hw5 as [_ HJ]. cbn [w_tr w_cfg cfg_model snd fst] in HJ.
    pose proof (tracked_disjoint (ndR tv1 bd1) rho tp tr md 0 1 (SVar pN, kb16 vKn) (vP, kb16 vK) HJ eq_refl eq_refl ltac:(lia) NZ1 NZ2) as D.
    unfold tvv in D. cbn [fst snd] in D. repeat change (bv_unsigned (eval rho ?e)) with (uval rho e) in D. rewrite EKn16, EK16 in D. exact D. }

  destruct (JA_absorb_tr segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue tv1 [] bd1 ANone 0 (SVar pN) (kb16 vKn)
              E_fp (ss_objs (ax_S E_fa1)) o_dstE (kb16 (SAlu ALU_SUB vKn vQ)) rho tp tr ms md Xo1 eq_refl eq_refl eq_refl eq_refl rng_dstE Hw5) as (Hw6 & OUT2 & DEF2 & CELLS2).
  rewrite Xd1 in Hw6. cbn [ob_base o_dstE] in OUT2, DEF2, CELLS2.
  change (SAlu ALU_ADD (SVar 111) (SMd M_MUL (SLit 16) (SVar 172))) with (pls (SVar pN) (kb16 vQ)) in OUT2, DEF2, CELLS2.
  rewrite EdN, (Efs vQ) in OUT2, DEF2, CELLS2 by lia.
  set (rho2 := rho_absorb rho [o_dstE] (vms md tp ms)) in *.
  assert (UV2 : forall e, uval rho2 e = uval rho e) by (intros e; unfold uval, rho2; rewrite eval_absorb; reflexivity).
  assert (OLD2 : forall z, uval rho vP <= z < uval rho vP + 16 * uval rho vK -> rm rho2 (Z_to_bv 64 z) = rm rho (Z_to_bv 64 z)).
  { intros z Hz. apply OUT2. rewrite U_Z_to_bv by lia. lia. }
  pose proof (CELLS2 0 vF0 ltac:(cbn; tauto) ltac:(lia) ltac:(lia)) as C0. rewrite Z.add_0_r in C0.
  pose proof (CELLS2 8 vF1 ltac:(cbn; tauto) ltac:(lia) ltac:(lia)) as C1.

  destruct (JA_absorb_ent_same segs HTOP AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue tv1 [] bd1 ANone 1 vP (kb16 vK)
              E_fa1 (ss_objs (ax_S E_fa2)) (o_src vQ) vF0 vF1 rho2 tp tr ms md Xo2 eq_refl eq_refl eq_refl eq_refl ltac:(cbn; tauto) ltac:(cbn; tauto) rng_srcE) as [Hw7 RM3].
  { cbn [ob_base o_src ent_obj]. rewrite !UV2, EdP. rewrite (rd64_ext (rm rho) (rm rho2)) by (intros z Hz; apply OLD2; lia). rewrite EP. exact HR0. }
  { cbn [ob_base o_src ent_obj]. rewrite !UV2, EdP. rewrite (rd64_ext (rm rho) (rm rho2)) by (intros z Hz; apply OLD2; lia). rewrite EP. exact HR1. }
  { exact Hw6. }
  rewrite Xd2 in Hw7. set (rho3 := rho_absorb rho2 [o_src vQ] (vms md tp ms)) in *.
  assert (UV3 : forall e, uval rho3 e = uval rho e) by (intros e; etransitivity; [|apply UV2]; unfold uval, rho3; rewrite eval_absorb; reflexivity).

  destruct (JA_carve_tr segs AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue HNP tv1 [] bd1 ANone 1 vP (kb16 vK) vP (kb16 vK)
              E_fa2 rho3 tp tr ms md eq_refl eq_refl Cwf rng_oldE) as (Hw8 & _ & _ & _).
  { apply (carve_site_chk_sound segs AInv CST ALA HCST NF rho0 P0 FB FF E_fa2 tv1 [] 1%nat extraAL rho3 Csite).
    intros Ai tp1 md1 HFa HP0' Hav' _ _ _ _ _ _ _ _ _ o a Ho HE Hr. exact (al_extra_sound rho3 _ _ _ o a Hav' HP0' Ho HE Hr). }
  { intros z Hz. rewrite !UV3, EK16 in Hz. unfold rho3. rewrite RM3. rewrite OLD2 by lia. rewrite EP, EKK in *. rewrite (HP0i z) by lia. apply (proj2 HP0). unfold ptr0, K0 in *. lia. }
  { exact Hw7. }
  rewrite Xc in Hw8.
  exists (rho_sub rho3 []).
  assert (E111 : uval (rho_sub rho3 []) (SVar pN) = uval rho (SVar pN)) by (etransitivity; [|apply UV3]; reflexivity).
  assert (EKn4 : uval (rho_sub rho3 []) (kb16 vKn) = uval rho (kb16 vKn)) by (etransitivity; [|apply UV3]; reflexivity).
  assert (EM : rm (rho_sub rho3 []) = rm rho3) by reflexivity.
  split; [|split; [rewrite E111; lia | split; [rewrite EKn4, EKn16, <- EKN; lia| split; [rewrite <- EKK, <- EKN; lia|]]]].
  - unfold Phi2. rewrite E111, EM. unfold rho3. split.
    + intros j Hj. rewrite RM3.
      destruct (Z_lt_dec j (16 * uval rho vQ)) as [L|L].
      * rewrite OUT2 by (rewrite U_Z_to_bv by lia; lia). apply HPc. lia.
      * replace (uval rho (SVar pN) + j) with (uval rho (SVar pN) + 16 * uval rho vQ + (j - 16 * uval rho vQ)) by lia.
        rewrite (rd64_pair_bytes (rm rho2) (rm rho) _ _ (uval rho vF0) (uval rho vF1) C0 C1 HR0 HR1 (j - 16 * uval rho vQ)) by (rewrite <- EKK in Hj; lia).
        replace (ptr0 + 16 * uval rho vQ + (j - 16 * uval rho vQ)) with (ptr0 + j) by lia. apply HP0i. lia.
    + intros j Hj. rewrite RM3.
      destruct (Z_lt_dec j (16 * uval rho vQ)) as [L|L].
      * rewrite OUT2 by (rewrite U_Z_to_bv by lia; lia). rewrite (HPc j) by lia. apply (proj2 HP0). unfold ptr0, K0, Kn0 in *. lia.
      * apply DEF2. lia.
  - apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc E_fc E_freeT [] (ndR tv1 bd1) (ndR tv1 bd1) rho3 tp _ Cent eq_refl);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Cnb2 | exact Ctv | reflexivity | exact Cbud | reflexivity | exact Hw8].
Qed.

Lemma Phi0_keptR : ltac2:(tb__ "0|3|
S32S33ScScA2M0A1SbSbSb5G0S35ScScS46S45S44A1M1A4R3A3Sc0S90Vrho0;R3A3S2S1S5S7R4S46A2Z0A3A1S1S5S7R5G1A2S29Z10S7R5S44A2A2A3S100R6R7R5A3Sc7R7A1M2G2F_;F_;F_;F_;F_;F_;Frho';Frho;Ftv;").
Proof.
  intros tv rho rho' Hin Hav Hnz EK HK H z Hz.
  assert (EP : uval rho vP = ptr0) by (unfold ptr0; exact (vals_uval rho 13 Hav ltac:(reflexivity))).
  assert (EKK : uval rho vK = K0) by (unfold K0; exact (vals_uval rho 14 Hav ltac:(reflexivity))).
  rewrite (HK (vP, kb16 vK) z Hin); [exact (H z Hz) | unfold tnz; cbn [fst]; exact Hnz |].
  unfold tvv. cbn [fst snd]. repeat change (bv_unsigned (eval rho ?e)) with (uval rho e). rewrite EK, EP, EKK. exact Hz.
Qed.

Lemma P0_frame : ltac2:(tb__ "0|1|
Sb8SbSc0S90Vrho0;R1A3VP0;Vrho0;A1S97VFF;R4A2S38S5A1S5S0S26S43Q40S22R6S69A2A2M0R1A2S28R1S27G0Z30A2A2A2Sf6VCST;R8R3R2A4F_;Fa;Fx;F_;F_;F_;Frho;FAi;").
Proof.
  intros Ai rho Hav [(f & sz & fl & Hin & H1 & H2) _] HFF x a Ha.
  assert (E12 : rw rho 12%positive = rw rho0 12%positive) by (symmetry; apply (proj1 Hav); reflexivity).
  unfold vA in Ha. cbn [eval] in Ha. rewrite E12 in Ha.
  right; right; right. exists f, sz. split; [exact (proj1 (HFF _ _ _ Hin)) | lia].
Qed.
Lemma al_obj_range : ltac2:(tb__ "0|3|
SbSfS5S1S31S19S18R2A1S69A2S34A3S1ScS1cR3A1S11Z0A1A3S1ScS1bR4A1S11Z30M0A1A3S0S26S3bS5S5S1dR6R5A2M1A3R4A2S28R4S3cS5S5G1A3A2A2S0S26S43Q40S22R7S69A2A2M2R5A2S28R5S27G2G0A2A2A2F_;F_;F_;F_;Fa;Fo;Frho;").
Proof.
  intros rho o a Hb Hl Hh Hr. apply sv_eqb_sound in Hb. unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr.
  cbn [fst snd] in Hr. rewrite !soff_lit_small in Hr by lia. lia.
Qed.

Lemma site_m : ltac2:(tb__ "0|1|
SbSf5VAInv;VCST;VXGL;S90Vrho0;VP0;VFB;VFF;S61S5cS62R1S49S54S65A2S3fS5A1Sb8Sc4S0S0S26Z1S7R3SbdS5cPcA2A2M0A2S28G0S2aZ2Z27A2A2A2Sa0S36S9eA1S9cSbcSbbR3S62R1A3S5cA2A3A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR (r1 & t1 & m1 & HM) HT HTK. cbn [nd_tv nd_fr nd_bd ndR] in HN, HD, HZ, HFR.
  split; [|split; [|split; [|exact I]]].
  - eapply (robjs_checkA_sound segs AInv CST ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None (fun o => sv_eqb (ob_base o) vA) R_m None r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros o a Ho Hb Hr. eapply (P0_frame Ai rho Hav HP0 HFF). cbn in Ho.
      destruct Ho as [<-|[<-|[]]]; [cbn in Hb; discriminate|]. eapply (al_obj_range rho O_al a); [reflexivity | reflexivity | reflexivity | exact Hr].
    + exact I.
  - eapply (xrs_checkA_sound segs AInv CST XGL ALA FB Ai rho (ss_facts (ax_S E_m)) tv0 None (ss_objs (ax_S E_m)) (fun r => sv_eqb (fst r) vA) (ax_X E_m) None r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros r a Hr Hb Ha. left. eapply (P0_frame Ai rho Hav HP0 HFF). cbn in Hr.
      destruct Hr as [<-|[<-|[]]]; cbn in Hb; try discriminate. cbn [fst snd] in Ha. unfold uval in Ha. rewrite U_lit in Ha. change (48 mod M64v) with 48 in Ha. exact Ha.
    + exact I.
  - change (wsub_get s_m 12) with (kb16 vKn).
    fact HF (SPUle (SLit 1) vK) H3. fact HF (SPBranch BC_LTU vK vKn) H4. fact HF (SPUle vKn (SLit B32)) H5. zf H3. zf H4. zf H5.
    repeat change (bv_unsigned (eval ?r ?e)) with (uval r e) in *. unfold B32 in *. rewrite uval_lit in H3, H5 by lia.
    rewrite kb16_exact by (unfold B32; lia). lia.
Qed.

Lemma site_f : ltac2:(tb__ "0|2|
SbSf5VAInv;VCST;VXGL;S90Vrho0;VP0;VFB;VFF;S56S5bS6cR1S49S47S4bA2S3aS5S7R1SbdS5bPcA2M0A2A2Sb8Sc4S0ScdR3S35ScScS46S45S44A1A4M1A2S0S1S33S5S5A2SceR3G1A2S35S5S5S7R3G0A2S7R3SbdS5bPdA2A2A4A3Sa0S36S9eA1S9cSbcSbbR3S6cR1A3S5bA2A3A2A2Lms;LAi;AfFrho;").
Proof.
  intros rho Ai ms HF HP0 Hav HB HFF HN HD HZ HFR (r1 & t1 & m1 & HM) HT HTK. cbn [nd_tv nd_fr nd_bd ndR] in HN, HD, HZ, HFR.
  change (wsub_get s_f 12) with vP. change (wsub_get s_f 13) with (kb16 vK).
  assert (Hnz : tnz rho (vP, kb16 vK)).
  { fact HF (SPUle (SLit 4096) vP) H18. unfold tnz. cbn [fst]. zf H18. rewrite uval_lit in H18 by lia. unfold uval, vP in *. lia. }
  split; [|split; [|split; [exact Hnz|split; [reflexivity|exact I]]]].
  - eapply (robjs_checkA_sound segs AInv CST ALA FB Ai rho (ss_facts (ax_S E_freeT)) tv1 (Some 1%nat) (fun o => sv_eqb (ob_base o) vA) R_f _ r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros o a Ho Hb Hr. eapply (P0_frame Ai rho Hav HP0 HFF). cbn in Ho.
      destruct Ho as [<-|[<-|[]]]; [cbn in Hb; discriminate|]. eapply (al_obj_range rho O_al a); [reflexivity | reflexivity | reflexivity | exact Hr].
    + exists (vP, kb16 vK). split; [reflexivity|]. split; [exact Hnz | reflexivity].
  - eapply (xrs_checkA_sound segs AInv CST XGL ALA FB Ai rho (ss_facts (ax_S E_freeT)) tv1 (Some 1%nat) (ss_objs (ax_S E_freeT)) (fun r => sv_eqb (fst r) vA) (ax_X E_freeT) _ r1 t1 m1 HM HF HN HD HZ HTK).
    + OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    + intros r a Hr Hb Ha. left. eapply (P0_frame Ai rho Hav HP0 HFF). cbn in Hr.
      destruct Hr as [<-|[<-|[]]]; cbn in Hb; try discriminate. cbn [fst snd] in Ha. unfold uval in Ha. rewrite U_lit in Ha. change (48 mod M64v) with 48 in Ha. exact Ha.
    + exists (vP, kb16 vK). split; [reflexivity|]. split; [exact Hnz | reflexivity].
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S5S32S41Q40A1A1SacF_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S8eS2dSbS32S41Q40A1A1SacS9aS10SeR3A1SdS2cR4A1A1A3VTR;S8dS40R6R5R4R3A5R2A2M0F_;G0F_;FQa;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Qa : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Qa) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Qa.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
SacSacSacSadR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQa;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Qa : assn), (forall a, TR (P a) Qa) -> TR (fun w => exists a, P a w) Qa.
Hypothesis TR_pureP : ltac2:(tb__ "0|1|
SacOSacSadR4R1A1R4F_;Fw;R3VTR;R5R3A2M0F_;G0F_;F_;FQa;FX;FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S8eS8eS2dS2dSbfS32SfA1M0S32S33S2dSb0A2M1A1S32S33ScScA2M2A1SacSbS32S41Q40A1A1M3G2Sb5G2R1R5A3Sb5G2R2S2fRbA1A3F_;Fr;S1S38G0A1Sb4RaR9R8A3S3aG0R7A2A3S1S31Sb3RbRaR9R8S9bG1S2dS3bS2dSb0A2R7A4A5S34A3SbG3VTR;S8dS40RfRdR2R1A5Sb1S40S14S2cRdA1A1R2R1RaA5A2Ftp1;Frho1;S32SbaA1M4Sc4Sb9S8fS40R9R8R10S35G4Sf1R3Sf2R2R1A2A4A5R13RaR9R4R2A4R13SbcSbbRbRfSc2R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S2dSb0G4Sc4Sb9SbG3G4Sc4Sb9Sb5G1S35S2dSb0RaR9A4R14A3S8fS40R12R11R19S35G4Sf1R9Sf2R8R7A2A4A5R1cR13R12RaR8A4Sc0S14S2cR1aA1A1SbcSbbR14R18Sc2R9R13RaA3A3R19A2R8A3S8fS40R9R8ReS35G4Sf1R7Sf2R6R5A2A4A5ReSbcSbbR16R1aSc2RbR15RcA3A3R1bA2R15RaR9R8R6A6S0SfdR17Sc2RcR16RdA3R1bR1cR1dR10R1eR19RbA9SbSc1R18Sc2RdR17ReA3R1cR1dS2cR1eA1S2cR1fA1S2cR11A1R1RcA9VTR;S8dS40Sb2R11SbcSbbR19R1dSc2ReR18RfA3A3R1eA2R18RdRcA5SfeR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S8dS40R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQa;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis TR_phi : ltac2:(tb__ "0|0|
SbOF_;S91S2dSbS32S41Q40A1A1SacR6R3A1VTR;S8dS40VJAv;R6A1R5R4R3A5R2A2F_;VTR;S8dS40Se5VAInv;VCST;VXGL;S90VKc;Vrho0;VP0;VFB;VFF;VBX;S92R7R6AdR5R4R3A5R2A2F_;FQa;Ftp;Frho;FS;Fnd;FPhi;").
Hypothesis CMALLOC : ltac2:(tb__ "0|1|
Sb8SbS32S41Q40A1A1VTR;S8dS40Sa2VAInv;S36S9eA1M0S9cR3VKc;S12PcA1A6Sa8S9dG0S9cA3R2R1A5Sb1S40S90R2R1Sa6S9dVAInv;VCST;VXGL;G0S9cR3VKc;A8A5A2Ftp1;Frho1;FAi;").
Hypothesis CFREE : ltac2:(tb__ "0|2|
Sb8SbS32S41Q40A1A1VTR;S8dS40Sa3VAInv;S36S9eA1M0S9cR3VKc;A5Sa7S9dG0S9cA3R2R1A5Sb1S40S90R2R1S39S33S2dSb0A2M1S35S2dSb0S9fS9dG0S9cA3Sa1VAInv;VCST;VXGL;R3VKc;A5A4S36G1A1A3A5A2Ftp1;Frho1;FAi;").

Hypothesis REENTER : ltac2:(tb__ "0|5|
S2dS91S37S33S5ScA2M0SbS32S41Q40A1A1M1S5G1Sb5S33S33S33S2dS91A2M2S37A2M3G0A2S35G3G0S35G2S37S35S2dS91R8R7A4R6A4R5A4S7aA3Se9Sc8R7R5A3S0S26Z0Se6S35G3G0S35G2S37S35S2dS91RaR9A4R8A4R7A4R6A2M4A2S28G4R4A2A2VTR;S8dS40VJAv;RaA1RbR7R6A5VFAM;R5R4A2A2F_;F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fk;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|2|
S2dS91SbOF_;M0SbG0F_;SbS32S41Q40A1A1M1S5G1Sb5S33S2dSb0A2S35S2dSb0R8SeaVAInv;VCST;VXGL;VKc;VP0;VFB;VFF;VBX;S92R7R5AbA4Sc9A3SbR8R1A1R8Vrho0;R2A2F_;Fr;VTR;S8dS40Se5VAInv;VCST;VXGL;S90VKc;Vrho0;VP0;VFB;VFF;VBX;S92R8R9AdRaR6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;FPsi;FPhi;Fnd;FP;").

Lemma TR_phi_in : ltac2:(tb__ "0|0|
SbOF_;S91S2dSbS32S41Q40A1A1SacR6R3A1VTR;S8dS40Se5VAInv;VCST;VXGL;S90VKc;Vrho0;VP0;VFB;VFF;VBX;S92R7R6AdR5R4R3A5R2A2VTR;S8dS40VJAv;R7A1R6R5R4A5R3A2F_;F_;FQa;Ftp;Frho;FS;Fnd;FPhi;").
Proof. intros Phi nd S rho tp Qa HP H. eapply TR_pre; [|exact H]. intros w Hw. apply SPA_JAF_intro; [exact Hw | exact HP]. Qed.

Lemma X_E_m : ltac2:(tb__ "0|1|
SbS32S41Q40A1A1M0S5G0S26S29Z5aS2aZ2Z40A2A2R2A2VTR;S8dS40VJAFv;U0S49S54S65A2A2S61R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_phi. intros HPhi. apply TR_facts. intros HF.
  apply (TR_pureP _ (P0 rho0 /\ agree_vals NF rho0 rho)); [intros w Hw; exact (JA_P0 _ _ _ _ w Hw)|]. intros [HP0 Hav].
  fact HF (SPUle (SLit 4096) vP) H18. fact HF (SPBranch BC_LTU vK vKn) HKKn. fact HF (SPUle vKn (SLit B32)) HKB. zf H18. zf HKKn. zf HKB.
  rewrite uval_lit in H18 by lia. rewrite uval_lit in HKB by (unfold B32; lia).
  assert (EK : uval rho (kb16 vK) = 16 * uval rho vK) by (apply kb16_exact; lia).
  assert (Hnz : uval rho vP <> 0) by lia.
  apply (malloc_callT_k segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue HKc HBX TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe E_m s_m R_m rho tp (ndR tv0 bd0) bd1 (FAM b tp0) CMALLOC).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - apply payA_of_bud_pay. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - intros A A_ _ _; exact I.
  - exact (site_m rho).
  - intros rho' tp' Hag HK. cbn [nd_tv nd_fr nd_am ndR]. fold Pre_m. rewrite T_mnull_eq.
    apply (REENTER T_mnull (ndR tv0 bd1) 0%nat (80, z0)); [innth 1 | | meas].
    exact (Phi0_keptR tv0 rho rho' ltac:(left; reflexivity) Hav Hnz EK HK HPhi).
  - intros rho' tp' Hag HK. cbn [nd_tv nd_fr nd_am ndR]. fold Pre_m. rewrite T_mok0_eq.
    eapply TR_pre; [|apply (REENTER T_mok (ndR tv1 bd1) 0%nat (80, z0)); [innth 2 | | meas]].
    + intros w Hw. unfold T_mok. apply (SPA_refacts_JA segs); [exact Hw | reflexivity |].
      intros tr md HJ HF'. apply Forall_app. split; [|exact HF'].
      eapply JA_tv_facts; [exact ALA | | exact HJ | left; reflexivity |]; [reflexivity|].
      fact HF' (SPNot (SPBranch BC_EQ (SVar pN) (SLit 0))) Hnz'. eapply tnz_of_fact. exact Hnz'.
    + exact (Phi0_keptR tv0 rho rho' ltac:(left; reflexivity) Hav Hnz EK HK HPhi).
Qed.

Lemma X_X_cp0 : ltac2:(tb__ "0|1|
SbS32S41Q40A1A1M0S5G0S26S29Z4bS2aZ2Z40A2A2R2A2VTR;S8dS40VJAFv;U0S49S47S4bA2A2S58R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_phi. intros HPhi.
  apply (TR_pre (fun w => exists r', (Phi1 r' /\ uval r' vK = uval rho vK /\ uval r' vQ = 0 /\ 1 <= uval rho vK <= B32) /\ SPA segs (JAv (ndR tv1 bd1)) C_0 r' tp w)).
  { intros w Hw. destruct (cp0_glue rho tp w HPhi Hw) as (r' & H1 & H2 & H3 & H4 & H5). exists r'. auto. }
  apply TR_exw; intros r'. eapply TR_pureP; [intros w [H _]; exact H|]. intros (HP1 & EK & EQ & HK).
  eapply TR_pre; [intros w [_ Hw]; exact Hw|].
  apply (REENTER C_0 (ndR tv1 bd1) 1%nat (70, VQ 0) r'); [innth 3 | exact HP1 |].
  rewrite (meas_VQ C_0 _ 1%nat 70 0 r') by (rewrite ?EK, ?EQ; lia). rewrite EK, EQ. unfold two47, B32 in *. lia.
Qed.

Lemma X_X_step : ltac2:(tb__ "0|4|
SbS32S41Q40A1A1M0S5G0S26Se6S35S33S33S2dS91A2M1S37A2S33S5ScA2S35G1S37S35S2dS91S53S49S47S4bA2M2A4U1M3A4S35S5ScZ46S6dZ1fA1A4A4R4A2R2A2VTR;S8dS40VJAFv;G3G2A2S53R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_phi. intros HPhi.
  apply (TR_pre (fun w => exists r', (Phi1 r' /\ uval r' vK = uval rho vK /\ uval r' vQ = uval rho vQ + 1 /\ uval rho vQ + 1 < uval rho vK /\ uval rho vK <= B32)
                                     /\ SPA segs (JAv (ndR tv1 bd1)) C_0 r' tp w)).
  { intros w Hw. destruct (step_glue rho tp w HPhi Hw) as (r' & H1 & H2 & H3 & H4 & H5 & H6). exists r'. auto 10. }
  apply TR_exw; intros r'. eapply TR_pureP; [intros w [H _]; exact H|]. intros (HP1 & EK & EQ & HqK & HKB).
  eapply TR_pre; [intros w [_ Hw]; exact Hw|].
  apply (REENTER C_0 (ndR tv1 bd1) 1%nat (70, VQ 0) r'); [innth 3 | exact HP1 |].
  rewrite (meas_VQ X_step _ 1%nat 70 31 rho) in Hb by lia.
  rewrite (meas_VQ C_0 _ 1%nat 70 0 r') by (rewrite ?EK, ?EQ; lia). rewrite EK, EQ. unfold two47, B32 in *. lia.
Qed.

Lemma X_E_free : ltac2:(tb__ "0|1|
SbS32S41Q40A1A1M0S5G0S26S29Z41S2aZ2Z40A2A2R2A2VTR;S8dS40VJAFv;U1S49S47S4bA2A2S5fR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_phi. intros HPhi.
  apply (TR_pre (fun w => exists r', (Phi2 r' /\ uval r' (SVar pN) <> 0 /\ uval r' (kb16 vKn) = 16 * Kn0 /\ K0 < Kn0) /\ SPA segs (JAv (ndR tv1 bd1)) E_freeT r' tp w)).
  { intros w Hw. destruct (free_glue rho tp w HPhi Hw) as (r' & H1 & H2 & H3 & H4 & H5). exists r'. auto 6. }
  apply TR_exw; intros r'. eapply TR_pureP; [intros w [H _]; exact H|]. intros (HP2 & Hnz & HKK & HKn).
  eapply TR_pre; [intros w [_ Hw]; exact Hw|].
  apply (free_callT_k segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 P0 FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           [] UStopLe E_freeT s_f R_f r' tp (ndR tv1 bd1) 1%nat (vP, kb16 vK) [] (FAM b tp0) CFREE).
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - reflexivity.
  - reflexivity.
  - apply payA_of_bud_pay. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - intros A A_ _ _; exact I.
  - exact (site_f r').
  - intros rho' tp' Hag HK. cbn [nd_tv nd_fr nd_am ndR remove_nth]. fold Pre_f. rewrite T_free_eq.
    apply (REENTER T_free (ndR tv2 []) 2%nat (60, z0)); [innth 19 | | meas].

    assert (E111 : uval rho' (SVar pN) = uval r' (SVar pN)) by (unfold uval; cbn [eval]; rewrite <- (proj1 Hag pN ltac:(reflexivity)); reflexivity).
    assert (KEEP : forall j, 0 <= j < 16 * Kn0 -> rm rho' (Z_to_bv 64 (uval r' (SVar pN) + j)) = rm r' (Z_to_bv 64 (uval r' (SVar pN) + j))).
    { intros j Hj. apply (HK (SVar pN, kb16 vKn) (uval r' (SVar pN) + j) ltac:(left; reflexivity)); [unfold tnz; cbn [fst]; exact Hnz |].
      unfold tvv. cbn [fst snd]. repeat change (bv_unsigned (eval r' ?e)) with (uval r' e). lia. }
    change (Phi2 rho'). unfold Phi2. rewrite E111. destruct HP2 as [HP2a HP2b]. pose proof (uval_range rho0 vK) as RK0. unfold K0, Kn0 in *.
    split; intros j Hj; rewrite KEEP by lia; [exact (HP2a j Hj) | exact (HP2b j Hj)].
Qed.

Lemma X_P_fail : ltac2:(tb__ "0|1|
SbS32S41Q40A1A1M0S5G0VTR;S8dS40VJAFv;U0S49S54S36S9A1A2A2S74R4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0. apply (POST P_fail (ndR tv0 []) (phiK Phis 0) Psi_fail); [left; reflexivity|].
  intros r Hr z Hz. exact (Hr z Hz).
Qed.

Lemma X_P_okX : ltac2:(tb__ "0|1|
SbS32S41Q40A1A1M0S5G0VTR;S8dS40VJAFv;U2S49S72S36S9A1A2A2S6bR4R3A5VFAM;R2R1A2A2Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0. apply TR_phi. intros HPhi.
  apply (TR_pureP _ (P0 rho0 /\ agree_vals NF rho0 rho)); [intros w Hw; exact (JA_P0 _ _ _ _ w Hw)|]. intros [HP0 Hav].
  pose proof chk_post as (Cent & Cid & Ctv & Cnb & Cbud).
  apply (TR_pre (SPA segs (JAv (ndR tvP [])) P_ok (rho_sub rho s_post) tp)).
  { intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc P_okX P_ok s_post (ndR tv2 []) (ndR tvP []) rho tp w Cent Cid);
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | exact Cnb | exact Ctv | reflexivity | exact Cbud | reflexivity | exact Hw]. }
  apply (TR_phi_in (fun r => Psi_ok rho0 r) (ndR tvP []) P_ok (rho_sub rho s_post) tp).
  - assert (E140 : uval (rho_sub rho s_post) vPn = uval rho (SVar pN)) by reflexivity.
    assert (EM : rm (rho_sub rho s_post) = rm rho) by reflexivity. unfold Psi_ok. rewrite E140, EM. destruct HPhi as [HPa HPb]. split.
    + intros j Hj. split; [exact (HPa j Hj) | apply (proj2 HP0); unfold ptr0, K0 in Hj |- *; lia].
    + intros j Hj. exact (HPb j Hj).
  - apply (POST P_ok (ndR tvP []) (fun r => Psi_ok rho0 r) Psi_ok); [right; left; reflexivity | intros r Hr; exact Hr].
Qed.

Lemma exits_okT : ltac2:(tb__ "0|4|
S2dS91S37S33S5ScA2M0SbS32S41Q40A1A1M1G1Sb5S33S33S33S2dS91A2M2S37A2M3G0A2S35G3G0S35G2S37S35S2dS91R7R6A4R5A4R4A4S7bA3VTR;S8dS40VJAFv;R6R7A2R8R4R3A5VFAM;Se6S35G3G0S35G2S37S35S2dS91R8R7A4R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FkX;FndX;FX;").
Proof.
  intros X ndX kX rvX rho tp tp0 Hin. cbn in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[]]]]]]]; injection H as <- <- <- <-.
  - apply X_E_m. meas.
  - apply X_X_cp0. meas.
  - apply X_X_step. lia.
  - apply X_E_free. meas.
  - apply X_P_fail.
  - apply X_P_okX.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S98S40VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
Sa9S40S9dVAInv;VCST;VXGL;A5").

Theorem realloc_rom_sum : ltac2:(tb__ "0|0|
S32S41Q40A1A1SafS40Vok;S8dS40S94VAInv;VCST;VXGL;VKc;S6aVFB;VFF;A2VFB;VFF;VBX;S92S49S54S65A2AaS77Vrho0;R1A5Sb1S40S90Vrho0;R1Sc9A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JAF segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc Phis Phis_reads FUEL_rr cutpcs_rr 100
                (map efdrop cutsE) (map efdrop exitsE) ok (Q tp0) Hok (ejcertAF_jcertAF segs NF Phis _ _ _ _ _ ejcertAF_ok))
         with (ndT := ndR tv0 bd0) (kT := 0%nat); [|left; reflexivity].
       intros X ndX kX rho tp Hin. apply in_map_iff in Hin as ([[[X' nd'] k'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map (nodeIAF AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis) (map efdrop cutsE)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (TRs_pureP segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros Phi nd S rho1 tp1 Qa H. exact (triple_JAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phi ok nd S rho1 tp1 Qa H).
       - intros Ai rho1 tp1. apply (aca_malloc _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros Ai rho1 tp1. apply (aca_free _ _ _ _ _ AC); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
       - intros T nd k rv' rho1 tp1 b tp2 HinT HP _. apply (reenter_cutJAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis ok (map efdrop cutsE) T nd k); [|exact HP].
         apply in_map_iff. exists (T, nd, k, rv'). auto.
       - intros P nd Phi Psi rho1 tp1 b tp2 HinP HPsi. apply (exit_postGAF segs AInv CST XGL NF Kc P0 FB FF BX PTrue ok rho0 tp0 Phi Psi nd Posts_rr P); [exact HinP | exact HPsi].
       - exact Hin. }
  intros w Hw. apply SPA_JAF_intro; [apply JA_pre_intro; exact Hw|]. intros z Hz. reflexivity.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
SaaS40S9dVAInv;VCST;VXGL;A5").

Theorem realloc_rom_sum_ex : ltac2:(tb__ "0|0|
S32S41Q40A1A1SaeS40S8dS40S94VAInv;VCST;VXGL;VKc;S6aVFB;VFF;A2VFB;VFF;VBX;S92S49S54S65A2AaS77Vrho0;R1A5Sb1S40S90Vrho0;R1Sc9A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JAF segs AInv CST XGL ALA NF Kc rho0 P0 FB FF BX PTrue HKc Phis Phis_reads FUEL_rr cutpcs_rr 100 cutsE exitsE (Q tp0) ejcertAF_ok)
         with (ndT := ndR tv0 bd0) (kT := 0%nat) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX kX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIAF AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis) cutsE) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (TRe_pureP segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Phi nd S rho1 tp1 Qa H. exact (etriple_JAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phi nd S rho1 tp1 Qa H).
       - intros Ai rho1 tp1. apply (acx_malloc _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros Ai rho1 tp1. apply (acx_free _ _ _ _ _ ACX); [first [left; reflexivity | right; left; reflexivity | right; right; left; reflexivity] | exact HKc].
       - intros T nd k rv' rho1 tp1 b tp2 HinT HP Hm. apply (ereenter_cutJAF segs AInv CST XGL NF Kc rho0 P0 FB FF BX PTrue Phis cutsE T nd k rv'); [exact HinT | exact HP | exact Hm].
       - intros P nd Phi Psi rho1 tp1 b tp2 HinP HPsi. apply (eexit_postGAF segs AInv CST XGL NF Kc P0 FB FF BX PTrue rho0 tp0 Phi Psi nd Posts_rr P); [exact HinP | exact HPsi].
       - exact Hin. }
  intros w Hw. apply SPA_JAF_intro; [apply JA_pre_intro; exact Hw|]. intros z Hz. reflexivity.
Qed.
End Existence.
End Sum.

Print Assumptions realloc_rom_sum.
Print Assumptions realloc_rom_sum_ex.
End Lib_realloc_rom_pf.

(* [comment removed for export] *)
Module Lib_build_line_index_rom_call.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_base"; "ax_X"; "@Corelib.Init.Datatypes"; "list"; "bool"; "true"; "pair"; "prod"; "option"; "Some"; "andb"; "None"; "false"; "fst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "sobj"; "sv"; "SLit"; "sprop"; "ss_facts"; "holds"; "sv_eqb"; "@Corelib.Init.Logic"; "eq"; "and"; "True"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "call_checkPA"; "entails_frA"; "J_ofPA"; "xs_framed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "nd_tv"; "JA"; "JAi"; "JAk"; "NDA"; "nd_am"; "nd_bd"; "nd_below"; "nd_fr"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@Stdlib.Lists.List"; "In"; "forallb"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "new_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "bd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK"; "keptR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "payA"; "site_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "JL_pure"; "J_pure_pre"; "alloc_lawsA"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymSoundW SymFrame SymEntail SymCFG SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface IfaceEx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.
Variable AInv : ltac2:(tb__ "0|0|
S1dSfS4S3eQ40A1A1S23OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S55Vsegs;VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S1bS49VCST;R1A2S19S4aZ0R2A2S4bR2S47A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S1bS49VXGL;R1A2S19S4aZ0R2A2S4bR2S47A2A2F_;Fa;").
Section Sum.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S4S8S8S1bS1bA2S1bA2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.

Let JAi : ltac2:(tb__ "0|0|
S30S1dS1bS1fFkc;FAi;Fnd;") := ltac2:(tb__ "0|0|
S33VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JA : ltac2:(tb__ "0|0|
S30S1fFnd;") := ltac2:(tb__ "0|0|
S32VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JAk : ltac2:(tb__ "0|0|
S30S1dS1fFAi;Fnd;") := ltac2:(tb__ "0|0|
S34VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let site_okA : ltac2:(tb__ "0|0|
S0S2fS4S11A1SfS30S9S1bA1S1dS22OF_;F_;OFextra;Fx;Fnd;Frho;FR;Fs;FCl;") := ltac2:(tb__ "0|0|
S51VAInv;VCST;VXGL;VNP;Vrho0;VP0f;VFB;VFF;A8").
Let payA : ltac2:(tb__ "0|1|
S4S14A1S12S1bS4S45A1M0G0OFbto;Fbfrom;FcostK;FcostV;Ffacts;") := ltac2:(tb__ "0|0|
S50VNP;Vrho0;VP0f;A3").
Let call_checkTA := call_checkTA NP.
Let cmaddrA := cmaddrA CST.
Let robjs_okA := robjs_okA CST.

Ltac chain_same_tv Hlink Hnb :=
  cbn zeta; intros ? ? _ _ Hut;
  eapply untracked_agree; [eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch] | | exact Hut];
  exact (proj1 (nd_below_split _ _ Hnb)).

Section CallT.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S1fS0SfS4S3eQ40A1A1S25S40S14S16R3A1S15S1R4A1A1A3VTR;S1eVsegs;R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S25S25S25S26R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S1fS1fS0S0S2fS4S11A1M0S4S8S0S27A2M1A1S4S8S12S12A2M2A1S25SfS4S3eQ40A1A1M3G2S3cG2R1R5A3S3cG2R2S3RbA1A3F_;Fr;S18S9G0A1S2aRaR9R8A3SaG0R7A2A3S18S5S29RbRaR9R8S3fG1S0SeS0S27A2R7A4A5S6A3SfG3VTR;S1eVsegs;RfRdR2R1A5S28Vsegs;S10S1RdA1A1R2R1RaA5A2Ftp1;Frho1;S4S24A1M4S22S23S20Vsegs;R9R8R10S7G4S3aR3S3bR2R1A2A4A5R13RaR9R4R2A4R13S2eS2dRbRfS21R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S0S27G4S22S23SfG3G4S22S23S3cG1S7S0S27RaR9A4R14A3S20Vsegs;R12R11R19S7G4S3aR9S3bR8R7A2A4A5R1cR13R12RaR8A4S42S10S1R1aA1A1S2eS2dR14R18S21R9R13RaA3A3R19A2R8A3S20Vsegs;R9R8ReS7G4S3aR7S3bR6R5A2A4A5ReS2eS2dR16R1aS21RbR15RcA3A3R1bA2R15RaR9R8R6A6S19S4cR17S21RcR16RdA3R1bR1cR1dR10R1eR19RbA9SfS43R18S21RdR17ReA3R1cR1dS1R1eA1S1R1fA1S1R11A1R1RcA9VTR;S1eVsegs;S2bR11S2eS2dR19R1dS21ReR18RfA3A3R1eA2R18RdRcA5S4dR1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S1eVsegs;R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Theorem purec_callT_k_xp : ltac2:(tb__ "0|5|
S1dSfOF_;F_;S0S4S0A1S0S2fS4S11A1M0SfS4S3eQ40A1A1M1S30S4S45A1S25S1dSfG1VTR;S1eVsegs;SfG1S4S24A1M2S23S19S54VAInv;R7VKc;R4R3R2R1A7R12R7R4A2A2Lm;Lt;Lp;Lr;RdR2R1A5S28Vsegs;S41R2R1S3fS0S8S0S27A2S0S7S0S27R1S53VAInv;VCST;VXGL;R4VKc;A5A4LL;RcA4A5A2Ftp1;Frho1;FAi;S18S1cS10S1RbA1A1S41A3S18S12S2RcA1S13S48A1A3S18S9G0A1S2aRbRdRaA3SaG0R9A2A3S18S5S29RcReRbRaRdA5S6A3S18S5Vcall_checkTA;RcA1S6A3S18S5S56VNP;S10S1ReA1A1A2S6A3S18S5S38S10S1RfA1A1RaA2S6A3S18S5S46S10S1R10A1A1RaA2S6A3VpayA;S15S1R11A1A1S13Z0M3A1G3S37RcA1RbA5S18S5S3dS0S0SbSbG0S5Lx;S44S1R15A1S1R1A1A2S6S11G0SdLl;Ls0;X4x2S2cR15R1A2A2S17S2R1A1S2R15A1A2A2LL;R13A3S6A3Vsite_okA;R13R12R11R10ReScS1bA1M4S1dS22S1aLms;LAi;A7S1dG2S22S23S20Vsegs;R15R14R18S7G2S3aR3S3bR2R1A2A4A5VAInv;R5R16R15R2A4S52VCST;VXGL;R6G4R17S3R1aA1A6R1eR7S2eS2dR18R19S21R4R17R5A3A3R1aA2A2F_;F_;F_;Fmd;Fms;Ftr;FAi;S0SfG1S3cS0R3R19A3S42S10S1R19A1A1R16R3A3S4eR17S31R15A1R4A3VTR;S1eVsegs;VJA;S35S31R16A1S39R16A1R15S36R16A1A4A1S4fR1dR1bR1aR19R6A5R5R4A5R14A2F_;F_;F_;Ftp';Frho';FL;VTR;S1eVsegs;VJA;R11A1R16R13R12A5RfA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;FLs;FPre;FXP;").
Proof using ALA HCST HXGL HKc TR_callP TR_ex TR_facts TR_pre.
  intros XP Pre Ls Cl s R rho tp nd bd' Q CALLEE HNF HbP He Hchk Htp Hnf Hnb Hbb HPAY Hshape HSITE HXP Tcont.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex AA (JAk nd)). intros Ai. apply (TR_ex Z (JAi nd Ai)). intros kc.
  eapply (TR_callP (JAi nd Ai kc) (fun r p t m => J_pure_pre AInv Ai Kc r p t m /\ XP Ai r) Cl Pre s R
            (map (fun L => (L, JL_pure AInv CST XGL Ai Kc)) Ls) (ax_X Cl) Q rho tp (fun r H => H) He).
  - rewrite map_map. cbn [fst]. rewrite map_id. exact Hchk.
  - intros rho1 tp1. rewrite HNF. apply CALLEE.
  -
    intros tr ms md Hsm HJ. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA NP rho0 Ai s rho Hav HT Htp)) as (HRok & HX & _).
    split; [|exact (HXP Ai tr ms md Hsm HM HX)].
    split; [eapply (AInv_absorb segs AInv CST ALA HCST); [exact HM | exact HRok]|]. split; [exact Hk|]. split; [eapply (tp_of_TPA NP rho0); eauto | exact (top_of_TPA NP rho0 Ai s rho _ _ Hav HT Htp)].
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA NP rho0 Ai s rho Hav HT Htp)) as (HRok & HX & _).
    pose proof (entails_frA_base _ _ _ _ SHADOW_OFF He HbP) as HbC.
    apply in_map_iff in HinL as (L0 & Heq & HinL). injection Heq as HJLe HL. subst L JL.
    pose proof (proj1 (forallb_forall _ _) Hshape L0 HinL) as HS. apply andb_prop in HS as [HS HbL]. apply andb_prop in HS as [Hnonew Hxf].
    apply sv_eqb_sound in HbL. rewrite HbP in HbL.
    assert (NONEW : forall o', In o' (new_objs (ax_S Pre) (ax_S L0)) -> False).
    { intros o' Hin'. destruct (new_objs (ax_S Pre) (ax_S L0)); [destruct Hin' | discriminate]. }
    destruct HJL as (HM2 & Htp2 & Hkept2 & Hk2).
    assert (Hsub : forall a, cmaddrA Ai None a -> cmaddrA Ai None a) by (intros a H; exact H).
    split.
    * split; [split; [exact (KEPT_stepA segs AInv CST XGL ALA Ai Ai None rho rhoL _ s R _ _ _ HM HRok Hsub Hkept2)|]|split].
      -- intros o' oR Hin' _. exfalso. exact (NONEW o' Hin').
      --
         intros r a j oR Hr Ha Hj HoR Hrng.
         unfold xs_framed in Hxf. pose proof (proj1 (forallb_forall _ _) Hxf r Hr) as Hrp. apply existsb_exists in Hrp as (rp & HinP & Heqr).
         apply xr_eqb_sound in Heqr. subst rp.
         pose proof Hsm as (HsmS & _ & HwfC & HshC & _).
         assert (HXcov : forallb (fun r0 => xr_covered (ss_facts (ax_S Cl)) (ax_X Cl) (xr_subst s r0)) (ax_X Pre) = true /\ axwf Pre = true).
         { clear - He. rewrite entails_frA_ref_eq in He. unfold entails_frA_ref in He. destruct (entails_fr (ax_S Cl) (ax_S Pre) s); [|discriminate].
           match type of He with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
           apply andb_prop in Hc as [Hc Hwf]. apply andb_prop in Hc as [Hc _]. auto. }
         destruct HXcov as [HXcov HwfP].
         pose proof (xr_covered_sound rho (ss_facts (ax_S Cl)) (ss_objs (ax_S Cl)) (bv_unsigned (eval rho (ax_base Cl))) (ax_X Cl) (xr_subst s r)
                       HF (proj1 (forallb_forall _ _) HXcov r HinP) HshC) as Hok.
         unfold axwf in HwfP. apply andb_prop in HwfP as [HwfX _]. pose proof (proj1 (forallb_forall _ _) HwfX r HinP) as Hrb.
         unfold xr_below in Hrb. apply andb_prop in Hrb as [Hrb1 Hrb2].
         assert (EV : forall e, sv_below (ss_next (ax_S Pre)) e = true -> eval rhoL e = eval rho (sv_subst s e)).
         { intros e He0. rewrite <- (eval_agree_vals _ _ _ e Hag1 He0). rewrite <- eval_subst. apply eval_absorb. }
         destruct r as [b l]. cbn [fst snd] in Ha, Hrb1, Hrb2. rewrite (EV b Hrb1), (EV l Hrb2) in Ha.
         unfold xr_ok, xr_subst in Hok. cbn [fst snd] in Hok. rewrite <- !eval_subst in Hok || idtac.
         destruct Hok as (_ & _ & Hok). destruct (Hok a ltac:(rewrite !eval_subst; rewrite !eval_subst in Ha || idtac; exact Ha)) as (_ & _ & Hwd & _).
         destruct (Hwd j Hj) as [Hout _].
         rewrite HbL in Hrng. rewrite HbC in Hout. cbn [eval] in Hrng, Hout.
         exact (proj1 (Forall_forall _ _) Hout oR (proj2 (proj2 (proj2 (proj2 (entails_frA_sound segs Cl Pre s R rho tp tr ms md He Hsm)))) oR HoR) Hrng).
      -- eapply (caller_X_kept segs AInv CST XGL ALA HCST HXGL Ai Ai None rho tp md R (vms md tp ms) s rhoL Cl); eauto.
         all: try (eapply (xrs_range segs AInv CST XGL ALA HCST HXGL); eauto). all: intros o' Hin'; exfalso; exact (NONEW o' Hin').
    * intros rho' Hlink.
      assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
      { eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]. }

      assert (KR : keptR rho (nd_tv nd) (rho_patch rho' (patchf rho rho' R))).
      { intros t0 z Ht0 Hnz0 Hz. destruct (proj1 (Forall_forall _ _) HN t0 Ht0 Hnz0) as (_ & Hl0 & _).
        exact (proj1 (live2_kept segs AInv CST XGL ALA HCST Ai Ai None rho rho' rhoL (vms md tp ms) s R tp md _ _ HM HRok Hkept2 (proj1 (proj2 Hlink)) Hl0 Hl0) z Hz). }
      eapply TR_pre; [ | apply (Tcont L0 (rho_patch rho' (patchf rho rho' R)) tpL HinL HagP KR)].
      intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
      destruct HJ' as (HM3 & Htp3 & Hkept3 & Hk3).
      destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
      split; [exact ((cont_smatchA segs) Cl Pre _ s R rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
      exists Ai, kc.
      destruct (law_budget _ _ _ ALA Ai _ _ _ HM3) as (_ & _ & HV0 & HKm0 & HKf0).
      pose proof Hnb as Hnb0. destruct (nd_below_split _ _ Hnb) as (Hbt & _ & _ & _).
      eapply (cont_JAi segs AInv CST XGL ALA HCST HXGL NP Kc rho0 P0f FB FF BX PA Cl Pre L0 s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc Ai None
                _ bd' (SLit 0) 0 He Hsm Hnf Hnb0 Hbb HJ HRok Hlink HM3 Hk3 Hsub); try assumption; try reflexivity.
      -- pose proof (uval_range rho (SLit 0)). lia.
      -- lia.
      -- cbn zeta. split; [|split].
         ++ apply (tvinA_agree FB Ai (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HN].
         ++ apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HD].
         ++ apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HZ].
      -- intros b m Hb _ _. exact Hb.
      -- chain_same_tv Hlink Hnb0.
      -- cen_same_tvG Hlink Hnb0 (eq_refl (aa_live Ai)).
      -- capN_sameG HCNi Hlink Hnb0 (eq_refl (aa_live Ai)).
Qed.
End CallT.
End Sum.
End WithSegs.
End Lib_build_line_index_rom_call.

(* [comment removed for export] *)
Module Lib_builderH_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sv_eqb"; "SLit"; "sobj"; "sprop"; "holds"; "ob_base"; "ob_hi"; "ob_lo"; "obj_range"; "ss_facts"; "ss_objs"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Datatypes"; "false"; "list"; "bool"; "prod"; "true"; "andb"; "None"; "nat"; "orb"; "fst"; "snd"; "option"; "pair"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "True"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "leb"; "add"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "bd_wpos"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.Lib_builderH_pf"; "extraOH"; "extraXH"; "in_callersH"; "litb"; "alb"; "bvecb"; "pieceb"; "textb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs"; "vb"; "vAL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf"; "baseF"; "basez"; "P0_builder"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "tB"; "tL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_ok"; "tvd"; "tvz"; "FBx"; "remove_nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "TPA"; "frinA"; "tvinA"; "fbinA"; "ffinA"; "ANone"; "NDA"; "PTrue"; "frozen"; "nd_below"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "pclMA"; "FFx"; "xr_eqb"; "xrs_okL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "robjs_checkF"; "xrs_checkL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT"; "robjs_checkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "is_shadowZ"; "payA"; "robjs_okA"; "site_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "robjs_okF"; "xrs_ok47"; "@Stdlib.Lists.List"; "In"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ng.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ny.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ny.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition litb (e : sv) (lo hi : Z) : bool := ltac2:(tb__ "0|3|
S0S12Le;Ve;SdS15S24Vlo;R1A2S24R1Vhi;A2A2Lz;SeS10Li;S26S0S0S10Lb;La;M0Lop;M1G1S27G0Lop;M2G2S12SfS0S10La;Lw;Lsgn;SeS0SdS10Lk;Li;Ll;X0x8").
Lemma litb_sound : ltac2:(tb__ "0|0|
S0SdSdS1dS12S2fR3R2R1A3S14A3S21SdSdS1eS1dS0R5S3R1A1A3S1eS22R4R1A2S22R1R3A2A2A2Lz;A2F_;Fhi;Flo;Fe;").
Proof. intros [z| | | | | | |] lo hi H; cbn in H; try discriminate. apply andb_prop in H as [A B]. exists z. apply Z.leb_le in A. apply Z.leb_le in B. auto. Qed.

Definition pieceb (o : sobj) : bool := ltac2:(tb__ "0|2|
S15S15S2S7Vo;A1S34A2S2fS9Vo;A1Z0M0Z518M1A3A2S2fS8Vo;A1G0G1A3A2").

Definition bvecb (o : sobj) : bool := ltac2:(tb__ "0|9|
S0S12Lx;S7Vo;A1SdS10Lz;SeS10Li;M0S26S0S0S26S12Lop;R3S0S12Lb0;R1SdS15S15S15S15S2R3S34A2S24Z0M1R1A2A2S24R1Z4f8A2A2S2S9Vo;A1S3G1A1A2A2S2S8Vo;A1S3Z20A1A2A2Lk;G0S26S0S0S10Lb1;La;M2Lop0;M3G3S27G2Lop0;M4G4S12SfS0S10La;Lw;Lsgn;M5SeS0SdS10Lk;Li;Ll;M6X0x8S10S10S10S10S10S10S10S10S10X26xaLb0;Lb;Lop;S26S0S0S10Lb;La;M7Lop;S27G7Lop;M8G8G5G6X0x8").
Definition alb (o : sobj) : bool := ltac2:(tb__ "0|0|
S15S15S2S7Vo;A1S35A2S2S9Vo;A1S3Z0A1A2A2S2S8Vo;A1S3Z30A1A2A2").
Definition textb (o : sobj) : bool := ltac2:(tb__ "0|0|
S15S15S2S7Vo;A1S3fA2S2S9Vo;A1S3Z0A1A2A2S2S8Vo;A1S40A2A2").
Definition extraOH (o : sobj) : bool := ltac2:(tb__ "0|0|
S18S18S18S32Vo;A1S31Vo;A1A2S30Vo;A1A2S33Vo;A1A2").

Definition extraXH (r : sv * sv) : bool := ltac2:(tb__ "0|a|
S18S18S18S53Vr;S1cS0S0S34S3Z518M0A1A4A2S53Vr;S1cS0S0S35S3Z30A1A4A2A2S53Vr;S1cS0S0S3fS40A4A2A2S13S0S0A2S12Lr;Vr;S0S0S0S12Ls;R2SdS10Lz;SeS10Li;M1S26S0S0S26S12Lop;R3S0S12Lb0;R1SdS0S12Ls0;R5SdS15S15S15S2R4S34A2S24Z0M2R2A2A2S24G2R1A2A2S24S25R2R1A2G0A2A2Ln;G1S26S0S0S10Lb1;La;M3Lop0;M4G4S27G3Lop0;M5G5S12SfS0S10La;Lw;Lsgn;M6SeS0SdS10Lk0;Li;Ll;X0x8Lk;G1G4G4G5G5G6SeS0SdS10Lk;Li;Ll;M7X0x8S10S10S10S10S10S10S10S10S10X26xaLb0;Lb;Lop;S26S0S0S10Lb;La;M8Lop;S27G8Lop;M9G9G6G7X0x8Ls0;Ls;X13x1A2").
Definition in_callersH (rho : valuation) (a : Z) : Prop := ltac2:(tb__ "0|3|
S1fS1eS22S28Vrho;S34A2M0Va;A2S23Va;S25G0Z518A2A2A2S1fS1eS22S28Vrho;S35A2M1Va;A2S23Va;S25G1Z30A2A2A2S1eS22S28Vrho;S3fA2M2Va;A2S23Va;S25G2S28Vrho;S40A2A2A2A2A2A2").

Lemma sv_eqb_eq : ltac2:(tb__ "0|0|
S0S0S1dS12S2R2R1A2S14A3S1dS0R3R2A3F_;Fb;Fa;").
Proof. intros a b H. apply sv_eqb_sound in H. exact H. Qed.

Lemma extraOH_sound : ltac2:(tb__ "0|1|
SdS1S4SdS3bR4R3A2S1dS12S2cR3A1S14A3S1eS22S19SdSdSaR5R4A2M0A3R3A2S23R3S1aSdSdG0A3A2A2S2eR6R4A2F_;F_;F_;Fa;Fo;Frho;FDW;").
Proof.
  intros DW rho o a [Bsp Bb Bal BL BB Btop] HE Hr. rewrite aceil_val in *. unfold IMG_HI in *.
  unfold extraOH in HE. unfold in_callersH.
  apply orb_prop in HE as [HE|HE]; [apply orb_prop in HE as [HE|HE]; [apply orb_prop in HE as [HE|HE]|]|].
  -   unfold pieceb in HE. apply andb_prop in HE as [HE Hh]. apply andb_prop in HE as [Hb Hl]. apply sv_eqb_eq in Hb.
    destruct (litb_sound _ _ _ Hl) as (lo & El & Rl). destruct (litb_sound _ _ _ Hh) as (hi & Eh & Rh).
    eapply obj_rangeZ in Hr; [| rewrite El; apply soff_lit_small; lia | rewrite Eh; apply soff_lit_small; lia]. rewrite Hb in Hr. left. lia.
  -   unfold bvecb in HE. destruct (ob_base o) as [|v|op b e| | | | |] eqn:EB; try discriminate.
    destruct op; try discriminate. destruct e as [k| | | | | | |]; try discriminate.
    apply andb_prop in HE as [HE Hh]. apply andb_prop in HE as [HE Hl]. apply andb_prop in HE as [HE Hk2]. apply andb_prop in HE as [Hb Hk1].
    apply sv_eqb_eq in Hb. apply sv_eqb_eq in Hl. apply sv_eqb_eq in Hh. apply Z.leb_le in Hk1. apply Z.leb_le in Hk2. subst b.
    eapply obj_rangeZ in Hr; [| rewrite Hl; apply soff_lit_small; lia | rewrite Hh; apply soff_lit_small; lia]. rewrite EB in Hr.
    pose proof (uval_range rho vb). rewrite (uval_add_litZ rho vb k) in Hr by lia. left. lia.
  -   unfold alb in HE. apply andb_prop in HE as [HE Hh]. apply andb_prop in HE as [Hb Hl]. apply sv_eqb_eq in Hb. apply sv_eqb_eq in Hl. apply sv_eqb_eq in Hh.
    eapply obj_rangeZ in Hr; [| rewrite Hl; apply soff_lit_small; lia | rewrite Hh; apply soff_lit_small; lia]. rewrite Hb in Hr. right; left. lia.
  -   unfold textb in HE. apply andb_prop in HE as [HE Hh]. apply andb_prop in HE as [Hb Hl]. apply sv_eqb_eq in Hb. apply sv_eqb_eq in Hl. apply sv_eqb_eq in Hh.
    eapply obj_rangeZ in Hr; [| rewrite Hl; apply soff_lit_small; lia | rewrite Hh; apply soff_smallu; change tL with vL; lia]. rewrite Hb in Hr. right; right. lia.
Qed.

Lemma extraXH_sound : ltac2:(tb__ "0|1|
SdS1S13S0S0A2SdS3bR4R3A2S1dS12S2dR3A1S14A3S1eS22S28R5S19S0S0R4A3A2M0R3A2S23R3S25G0S28R5S1aS0S0R4A3A2A2A2A2S2eR6R4A2F_;F_;F_;Fa;Fr;Frho;FDW;").
Proof.
  intros DW rho r a [Bsp Bb Bal BL BB Btop] HE Hr. rewrite aceil_val in *. unfold IMG_HI in *.
  unfold extraXH in HE. unfold in_callersH.
  apply orb_prop in HE as [HE|HE]; [apply orb_prop in HE as [HE|HE]; [apply orb_prop in HE as [HE|HE]|]|].
  - apply xr_eqb_sound in HE. subst r. cbn [fst snd] in Hr. rewrite uval_lit in Hr by lia. left. lia.
  - apply xr_eqb_sound in HE. subst r. cbn [fst snd] in Hr. rewrite uval_lit in Hr by lia. right; left. lia.
  - apply xr_eqb_sound in HE. subst r. cbn [fst snd] in Hr. right; right. exact Hr.
  - destruct r as [e n]. destruct e as [|v|op b e'| | | | |]; try discriminate. destruct op; try discriminate.
    destruct e' as [k| | | | | | |]; try discriminate. destruct n as [n| | | | | | |]; try discriminate.
    apply andb_prop in HE as [HE H3]. apply andb_prop in HE as [HE H2]. apply andb_prop in HE as [Hb H1].
    apply sv_eqb_eq in Hb. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. subst b. cbn [fst snd] in Hr.
    pose proof (uval_range rho vb). rewrite (uval_add_litZ rho vb k) in Hr by lia. rewrite uval_lit in Hr by lia. left. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S36S1S11S3dQ40A1A1S39OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
SdS5dVCST;R1A2S1eS22Z0R2A2S23R2S58A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
SdS5dVXGL;R1A2S1eS22Z0R2A2S23R2S58A2A2F_;Fa;").

Variable NPc : positive.
Hypothesis HNPc : (NF <= NPc)%positive.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S11S13S13SdSdA2SdA2A1").
Variable BX : bxt.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Hypothesis HP0b : ltac2:(tb__ "0|0|
S1VP0f;R1A1S3cVCST;VFB;VFF;R2A4F_;Fr;").
Variable DW : Z.
Hypothesis HDW : 0 <= DW < 2 ^ 40.

Lemma agree_NF : ltac2:(tb__ "0|0|
S1S2bVNPc;Vrho0;R1A3S2bS62Vrho0;R2A3F_;Frho;").
Proof.
  intros rho [H1 H2]. split; [|exact H2]. intros v Hv. apply H1. pose proof HNPc. lia.
Qed.

Lemma P0b_nowH : ltac2:(tb__ "0|1|
S1S2bVNPc;Vrho0;R1A3VP0f;Vrho0;A1S1eSdS1eS22S28R4S3fA2M0R1A2S23R1S25G0S28R4S40A2A2A2A2S51VCST;Vrho0;VFB;VFF;R2A5F_;Fa;S1eS59VFF;S28R3S34A2Z518A3S59VFF;S28R3S35A2Z30A3A2A2F_;F_;Frho;").
Proof. intros rho Hav HP. unfold tL, tB. fold vL vB. exact (P0b_now CST FB FF rho0 P0f HP0b rho (agree_NF rho Hav) HP). Qed.

Lemma in_callersH_ok : ltac2:(tb__ "0|0|
S1SdS11S13S0S0A2A1S11S13S13S0SdA2S0A2A1S2bVNPc;Vrho0;R4A3VP0f;Vrho0;A1S2eR6R5A2S51VCST;Vrho0;S44VFB;R7R5A3S52VFF;R7R4A3R6A5F_;F_;F_;Ffrs;Fkept;Fa;Frho;").
Proof.
  intros rho a kept frs Hav HP0 H. destruct (P0b_nowH rho Hav HP0) as (HT & Hb & Hal).
  destruct H as [H|[H|H]].
  - destruct Hb as (f & sz & fl & Hin & H1 & H2). right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
  - destruct Hal as (f & sz & fl & Hin & H1 & H2). right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
  - apply pclMA_mono. apply HT. exact H.
Qed.
Lemma extraOH_client : ltac2:(tb__ "0|1|
S1S4SdS11S13S0S0A2A1S11S13S13S0SdA2S0A2A1S3bVDW;R5A2S2bVNPc;Vrho0;R6A3VP0f;Vrho0;A1S1dS12S2cR7A1S14A3S1eS22S19SdSdSaR9R8A2M0A3R7A2S23R7S1aSdSdG0A3A2A2S51VCST;Vrho0;S44VFB;RaR7A3S52VFF;RaR6A3R8A5F_;F_;F_;F_;F_;Ffrs;Fkept;Fa;Fo;Frho;").
Proof.
  intros rho o a kept frs BZ Hav HP0 HE Hr. apply (in_callersH_ok rho a kept frs Hav HP0). exact (extraOH_sound DW rho o a BZ HE Hr).
Qed.

Lemma sitePH : ltac2:(tb__ "0|0|
S36S1S11S5A1S11S13S0S0A2A1S11S13S13S0SdA2S0A2A1S1bS17A1S11S4A1S1S11S3dQ40A1A1S39VAInv;RaR3R2R1A4S3eS5S6RaA1R9A3S1dS12S3aVDW;RaA2S14A3S2bVNPc;Vrho0;RcA3VP0f;Vrho0;A1S46Vrho0;RfA2S41RfS38S37R10A1A1A2S49VFB;R11A2S4aVFF;R12A2S48VFB;R13R12R10A4S42R13R11A2S43R14R12A2S47VFF;R16R15R12A4S1dS12S5cR15R14R13R12S2cR11A6S14A3S65VCST;R18S16SdA1R17R12A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr skip R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR Hchk.
  eapply (robjsP_okA segs AInv CST ALA rho0 FB FF Ai rho facts tv fr skip extraOH R rho1 tp1 md1 HM HF HT HTK HBf HFF HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraOH_client rho o a _ _ (basez_of DW rho facts HDW HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteFH : ltac2:(tb__ "0|0|
S36S1S11S5A1S11S13S0S0A2A1S11S13S13S0SdA2S0A2A1S11S4A1S1S11S3dQ40A1A1S39VAInv;R9R3R2R1A4S3eS5S6R9A1R8A3S1dS12S3aVDW;R9A2S14A3S2bVNPc;Vrho0;RbA3VP0f;Vrho0;A1S46Vrho0;ReA2S41ReS38S37RfA1A1A2S48VFB;R10RfRdA4S42R10ReA2S43R11RfA2S47VFF;R13R12RfA4S1dS12S5aR12R11R10S16S17A1S2cRfA6S14A3S68VCST;Vrho0;VFB;VFF;R14R12R11R10A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hchk.
  eapply (robjsP_okF segs AInv CST ALA rho0 FB FF Ai rho facts tv fr extraOH R rho1 tp1 md1 HM HF HT HTK HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraOH_client rho o a _ _ (basez_of DW rho facts HDW HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteHH : ltac2:(tb__ "0|1|
S36S1S11S5A1S11S13S0S0A2A1S11S13S13S0SdA2S0A2A1S11S4A1S1S11S3dQ40A1A1S39VAInv;R9R3R2R1A4S3eS5S6R9A1R8A3S1dS12S3aVDW;R9A2S14A3S2bVNPc;Vrho0;RbA3VP0f;Vrho0;A1S46Vrho0;ReA2S41ReS38S37RfA1A1A2S48VFB;R10RfRdA4S42R10ReA2S43R11RfA2S47VFF;R13R12RfA4S1dS12S5aR12R11R10S16S17A1S2cRfA6S14A3S4SdS6aS4R2R12A3S1eS22S19SdSdSaR17R3A2M0A3R2A2S23R2S1aSdSdG0A3A2A2S1fS51VCST;Vrho0;S44VFB;R18R16A3S52VFF;R18R15A3R3A5S1fS1eS22Z0R3A2S23R3S58A2A2S63R3A1A2A2F_;F_;Fa;Fo;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hchk.
  eapply (robjsP_hse segs AInv CST ALA rho0 FB FF Ai rho facts tv fr extraOH R rho1 tp1 md1 HM HF HT HTK HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraOH_client rho o a _ _ (basez_of DW rho facts HDW HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteXH : ltac2:(tb__ "0|4|
S36S1S11S5A1S11S13S0S0A2A1M0S11S13S13S0SdA2S0A2M1A1M2S1bS17A1M3S11S4A1G0S1S11S3dQ40A1A1S39VAInv;RbR3R2R1A4S3eS5S6RbA1RaA3S1dS12S3aVDW;RbA2S14A3S2bVNPc;Vrho0;RdA3VP0f;Vrho0;A1S46Vrho0;R10A2S41R10S38S37R11A1A1A2S49VFB;R12A2S4aVFF;R13A2S48VFB;R14R13R11A4S42R14R12A2S43R15R13A2S47VFF;R17R16R13A4S1dS12S5bVXGL;R16R15R14R13R12S2dR11A8S14A3S1eS54VCST;VXGL;Vrho0;VFB;VFF;R18R16G3G2Lskip;R14S17S45G1R1R16A3Li;R15X1bx2R12A9S1eS67VCST;VXGL;R19S16SdA1R18R12A6S69R18R12A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fobjs;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr skip objs X rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR Hchk.
  assert (HEX : forall r a, In r X -> extraXH r = true -> uval rho (fst r) <= a < uval rho (fst r) + uval rho (snd r) ->
            pclMA CST rho0 (FBx FB rho tv) (FFx FF rho (match skip with Some i => remove_nth i fr | None => fr end)) a \/ RtCells.in_rangesZ XGL a).
  { intros r a Hr HE Ha. left. apply (in_callersH_ok rho a _ _ Hav HP0). exact (extraXH_sound DW rho r a (basez_of DW rho facts HDW HF HB) HE Ha). }
  split; [exact (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho facts tv fr skip objs extraXH X rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HT HTK) HN HD HZ HFR Hchk HEX)|].
  exact (xrs_checkL_okA segs AInv CST XGL ALA HCST HXGL rho0 FB FF Ai rho facts tv fr skip objs extraXH X rho1 tp1 md1 HM HF HT HTK HBf HFF HN HD HZ HFR Hchk HEX).
Qed.
Lemma site_pureH : ltac2:(tb__ "0|2|
S57S60S11S4A1S1S11S13S0S0A2A1S11S13S13S0SdA2S0A2A1S11S29A1S1dS12S3aVDW;SbS55R7A1A1A2S14A3S1dS12S5cSbS55R8A1A1R4R3S16S17A1M0S2cR6A6S14A3S1dS12S5bVXGL;SbS55R9A1M1A1R5R4G0ScG1A1S2dS56R9A1A8S14A3S66VAInv;VCST;VXGL;VNPc;Vrho0;VP0f;VFB;VFF;RaR9R8R7S4cR6R5R4S4bA4S16SdA1S36S5eS20L_;L_;AfF_;F_;F_;Fbd;Ffr;Ftv;Frho;FR;Fs;FE;").
Proof.
  intros E s R rho tv fr bd HB HR HX Ai ms HF HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. cbn [nd_tv nd_fr] in HN, HD, HZ, HFR.
  split; [exact (sitePH Ai rho _ tv fr None R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HR)|].
  split; [exact (proj1 (proj2 (siteXH Ai rho _ tv fr None _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HX))) | exact I].
Qed.

Lemma frozen_stableH : ltac2:(tb__ "0|0|
SeSeS50S1S6bVNPc;R3A2S1dS12S4fR4R3A2S14A3S61S5fR6S4eVAInv;VCST;VXGL;VNPc;VKc;Vrho0;VP0f;VFB;VFF;VBX;S4dR4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;").
Proof.
  intros n m nd rho Hm Hb r r' tp tr md md' _ Hme (Ai & kc & HJ). exists Ai, kc.
  eapply (JAi_stable segs AInv CST XGL NPc Kc rho0 P0f FB FF BX PTrue HKc ALA m nd Ai kc rho rho tp tr md md'); [exact Hm | exact Hb | apply agree_below_refl | exact Hme | exact HJ].
Qed.
Lemma payA_sameH : ltac2:(tb__ "0|1|
S11S5A1S11S29A1S1dS12S2aR1A1S14A3S64VNPc;Vrho0;VP0f;R3S3Z0M0A1G0R2R2A8F_;Fbd;Ffacts;").
Proof.
  intros facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia.
  split; [lia|]. split; [lia | exact Hn].
Qed.
End Sum.
End Lib_builderH_pf.

(* [comment removed for export] *)
Module DrvSite.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sprop"; "valuation"; "SLit"; "ss_next"; "ss_facts"; "sstate"; "ss_objs"; "sprop_eqb"; "SPUle"; "rw"; "sv_eqb"; "holds"; "ss_lenient"; "cell"; "eval"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_regs"; "ss_resv"; "mkObj"; "obj_range"; "sprop_below"; "DUnknown"; "SAlu"; "SVar"; "ob_base"; "ob_hi"; "ob_lo"; "odefault"; "swf"; "SPEq"; "agree_below"; "rm"; "SAluW"; "SExt"; "SLBytes"; "SMd"; "SMdW"; "ob_cells"; "ob_dflt"; "tfact"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "False"; "or"; "ex"; "not"; "True"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "prod"; "nil"; "option"; "andb"; "nat"; "false"; "Some"; "cons"; "pair"; "app"; "fst"; "orb"; "None"; "snd"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "ax_X"; "ax_base"; "sym_runA"; "mkAX"; "la_state"; "mkLeafA"; "ax_setS"; "entailsA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "ExitEv"; "FdChannel"; "WriteEv"; "fd_lookup"; "m_fds"; "m_fs"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "pow"; "leb"; "lt"; "sub"; "opp"; "ltb"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "setregs"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "LQA"; "smatchA"; "stableA"; "@Stdlib.Lists.List"; "existsb"; "In"; "forallb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "nd_below"; "nd_tv"; "ANone"; "NDA"; "nd_am"; "JA"; "JAi"; "nd_bd"; "nd_fr"; "tvinA"; "TPA"; "am_eqb"; "am_subst"; "amode"; "fr_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface"; "FERR"; "PEND"; "Pre_exit"; "Pre_exitP"; "supportedP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite.SITE"; "sp0_factsb"; "sp0_off"; "drv_xrb"; "xrs_checkD"; "drv_objb"; "robjs_checkD"; "kept_nzb"; "ob_shapeb"; "one_leaf"; "HKV_K"; "arg1b"; "argtop_factsb"; "d6_okb"; "ex_pipe"; "fb_pipe"; "HKP_K"; "cst_rangeb"; "ex_S5c"; "ex_S6"; "sp0_rangeb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "tcons"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite.SITE.FbChain"; "CF"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "eqb"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "topG"; "cls_kept_freeA"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "seq"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.DrvExit"; "ch1"; "supported"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT"; "vB"; "PreF"; "vCap"; "s_fb"; "vTP"; "PostF"; "sp0"; "vA1"; "locate"; "CUTS_X"; "DEEP"; "FUEL_X"; "N_ex"; "s_ex"; "spM"; "spT"; "vL3"; "O_deepM"; "O_deepS"; "dropX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa"; "BX0"; "KV_T"; "KP_T"; "CST_drv"; "HKVrng_T"; "HCSTKV_T"; "SH0";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite.SITE.ExitHandoff"; "S5c"; "CX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueB"; "img_cell_apply"; "img_cell_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "ERRNO_A"; "acell"; "cells_ok"; "mkACell"; "view"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT.TAddr"; "TP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ"; "lcarve"; "lc_obj"; "JAK"; "carve_okb"; "JA_carve"; "JA_uncarve"; "pure_callJ"; "uncarve_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "entails_frA"; "call_checkA"; "call_checkPA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "KcA"; "Kc_ok"; "errno_addrA"; "AE_A"; "alloc_contractsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "rho_absorb"; "rho_sub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "RsCut"; "stop_reason"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "KU"; "bd_below"; "bud_pay"; "bitem"; "bd_subst"; "bud_le"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "is_prefix"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T0"; "T_ok"; "tvv"; "tvz"; "FBx"; "robj_tracked"; "tnz"; "tv_sub_eqb"; "tvd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "T_afterA"; "call_checkTA"; "cmaddrA"; "lit_in_ranges"; "xr_tracked"; "robjs_checkA"; "site_okA"; "xr_in_stack_obj"; "xrs_checkA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "IMG_HI"; "@Stdlib.Bool.Bool"; "Is_true"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.o1.DrvSite.SITE.FreeCall"; "ndJ"; "ndX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "pclMA"; "robjs_okF"; "xrs_okF"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform MuslWLA DrvGlueA DrvGlueB.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvJ DrvTLXa.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n6.Drv_printf0 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nu.DrvExit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Import PFAddr TAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma U_add_lit : ltac2:(tb__ "0|4|
S3S0S2dS31S60S65S61Z2M0Z3fA2M1A1R1A2S63R1G1A2A2S31S60Z0S5fS6bQ40M2S10R4R3A2A2R2A2M3A2S63G3S61G0Z40A2A2A2S30S2dS6bG2S10R5S1bSb2R4S4R3A1A3A2A2S5fS6bG2S10R5R4A2A2R3A2A3F_;F_;Fd;Fb;Frho;").
Proof.
  intros rho b d Hd Hr. rewrite U_add, U_lit. rewrite <- !M64v_eq.
  rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.

Lemma obj_range_lits : ltac2:(tb__ "0|2|
S3S0S2dS2dS38SfA1S20S60S65S61Z2Z3eA2M0A1R4A2S60R5R4A2S63R5G0A2S30S3aS2dS2dA2S18R9S17R8S4R7A1S4R6A1R5R4A5A2S42S2dS2dS5fS6bQ40S10R9R8A2A2M1R7A2S5fG1R6A2A4A3F_;F_;F_;Fd;Fcs;Fhi;Flo;Fb;Frho;").
Proof.
  intros. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. reflexivity.
Qed.

Section SITE.
Variable AInv : ltac2:(tb__ "0|0|
Sa8S3S38S6aQ40A1A1S57OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : alloc_lawsA segs AInv CST.
Hypothesis HCST : ltac2:(tb__ "0|0|
S2dSd4VCST;R1A2S31S60Z0R2A2S63R2S11aA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S2dSd4VXGL;R1A2S31S60Z0R2A2S63R2S11aA2A2F_;Fa;").
Hypothesis HLV : law_view_stmt AInv.
Hypothesis HCSTok : cst_ok CST.
Hypothesis HCSTdrv : ltac2:(tb__ "0|0|
S2dSd4SccR1A2Sd4VCST;R2A2F_;Fz;").
Hypothesis HLPP : law_pp_stmt AInv CST.
Variable ok : world -> Prop.
Variable Spec : list event -> Prop.
Hypothesis HOKJ : ltac2:(tb__ "0|0|
S6eS3S38S6aQ40A1A1S38S56A1S57R5R4R3R2R1A4Sa2VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;S6fS4aVok;R2A3F_;FJ;").
Hypothesis HOKP : ltac2:(tb__ "0|0|
S6eS3S38S6aQ40A1A1S38S56A1S57R5R4R3R2R1A4Sa2VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;S125S4aVok;R2A3F_;FJ;").
Hypothesis Hokh : ok_halted ok Spec.
Hypothesis AC : ltac2:(tb__ "0|0|
SebS4aSeaVAInv;VCST;VXGL;A5").

Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Hypothesis HP0SH : ltac2:(tb__ "0|0|
S3VP0f;R1A1ScfR2A1F_;Fr;").
Hypothesis HKtc : ltac2:(tb__ "0|0|
S38S56A1S57VKc;R2R1A2Sa2VSpec;R3A2F_;Fmd;Ftr;").

Variable PA : AA -> Prop.
Hypothesis HPAf : ltac2:(tb__ "0|0|
Sa8Sa8VPA;R2A1SabR3R2A2VPA;R3A1F_;F_;FA';FA;").

Let JK (nd : ndesc) : jpredA := ltac2:(tb__ "0|1|
S7dVAInv;VCST;VXGL;S68VKc;Vrho0;VP0f;S3bS3aS2dS2dA2M0A1S3bS3aG0S2dA2A1Sc9VPA;Vnd;Ac").

Lemma HKV_K : ltac2:(tb__ "0|1|
Sa8OF_;Se7S77Sa8S2dS3S38S6aQ40A1A1S38S56A1S57S7eVAInv;VCST;VXGL;S68R8Vrho0;VP0f;S3bS3aS2dS2dA2M0A1S3bS3aG0S2dA2A1Sc9R9R7R6R5R4R3R2R1A12Sd7Sd9S4aS24R5A1A2ScaA2F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;FKc';FPA';").
Proof.
  intros PA' Kc' nd Ai kc rho tp tr md (Hav & Hk & HM & HT & HB & HFF & HN & HFR & HK0 & HP0 & _).
  unfold KV_T. apply Forall_app. split; [|apply Forall_app; split; [|exact (KVpp_ok AInv CST HLPP Ai rho tp md HM)]].
  - pose proof (law_rtc _ _ _ ALA Ai rho tp md HM) as HR.
    apply Forall_forall. intros c Hc. exact (proj1 (Forall_forall _ _) HR c (KVrtc_in _ c Hc)).
  - destruct (HP0SH _ HP0) as [HZ _]. destruct HK0 as [K1 _].
    assert (BY : forall a, 0x800c0330 <= a < 0x800c0340 -> view segs (rm rho) a = Some (Z_to_bv 8 0)).
    { intros a Ha. rewrite view_in by lia. rewrite DrvJ.rd_of_high by lia.
      rewrite (K1 a ltac:(lia)).
      - exact (HZ a Ha).
      - right. split; [|rewrite (HZ a Ha); discriminate]. exists (8 * (a - SHADOW_OFF)). split; [unfold SHADOW_OFF; lia|]. split.
        + left. right. left. split; [apply HCSTdrv; exists 0x641968, 0x450; split; [cbn; tauto | unfold SHADOW_OFF; lia] | unfold errno_addrA, ERRNO_A, SHADOW_OFF; lia].
        + unfold Sh, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia. }
    unfold KVsh. repeat constructor; intros j Hj; cbn [c_addr c_w c_val] in Hj |- *;
      rewrite BY by lia; f_equal;
      do 8 (destruct j as [|j]; [reflexivity|]); lia.
Qed.

Lemma HKP_K : ltac2:(tb__ "0|3|
Sa8OF_;Se7S77Sa8S2dS3S38S6aQ40M0A1A1S38S56A1S57S2dS2dS2dS7eVAInv;VCST;VXGL;S68RbVrho0;VP0f;S3bS3aS2dS2dA2M1A1S3bS3aG1S2dA2A1Sc9RcRaR9R8R7R6R5R4A12S74G1S42S2dS2dR4R3A4ScbA3S31S60R5R3A2S63R3R4A2A2S31S31S60Z643000R4A2S63R4S61Z2Z40A2A2A2S35S30S3cS6aQ8A1M2A1S24RaS6cG0R4A2A2S46G2A1A3A1A2F_;F_;F_;Fz;Fhi;Flo;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;FKc';FPA';").
Proof.
  intros PA' Kc' nd Ai kc rho tp tr md lo hi z (Hav & Hk & HM & HT & HB & HFF & HN & HFR & HK0 & HP0 & _) Hin Hz.
  destruct (HP0SH _ HP0) as [_ [HP _]]. destruct HK0 as [K1 _].
  unfold KP_T in Hin. cbn in Hin.
  assert (RNG : 0x7fffc570 <= z < 0x7fffc758 \/ 0x80015238 <= z < 0x80015540).
  { destruct Hin as [E|[E|[]]]; injection E as <- <-; lia. }
  split; [lia|]. rewrite (K1 z ltac:(lia)); [exact (HP z RNG)|].
  right. split; [|exact (HP z RNG)]. exists (8 * (z - SHADOW_OFF)). split; [unfold SHADOW_OFF; lia|]. split.
  - left. right. left. split; [apply HCSTdrv; destruct RNG as [R|R]; [exists 0x22b80, 0xf40 | exists 0xe91c0, 0x1840]; (split; [cbn; tauto | unfold SHADOW_OFF; lia])
                             | unfold errno_addrA, ERRNO_A, SHADOW_OFF; destruct RNG; lia].
  - unfold Sh, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Let HCK := HCSTKV_T AInv CST HCSTok HLPP.
Let carveK : ltac2:(tb__ "0|3|
Se7S77S4cS3S38S6aQ40A1A1Sa1S38SdbA1S2eS6dS4aSddVAInv;VCST;VXGL;S68Vrho0;VP0f;S3bS3aS2dS2dA2M0A1M1S3bS3aG0S2dA2A1M2Sc9VPA;R8R7AcR6R5R4R3A6S4bR7A1S7S11S14R1A1S15R1A1S13R1A1S12R1A1S16R1A1S43S1S8R1A1SadSdbS1SdcR4A4A3S6R1A1R3SeR1A1A9S7S30S37S21R1A1S39A3S30S37Sa5S5R3A1R5A2S39A3S30S0S4fRbA1S4S119A1A3S30S37SdeS6R5A1S8R5A1S4eRcA1ScaScbS79RdA1R8A7S39A3S6dS4aSddVAInv;VCST;VXGL;S68Vrho0;VP0f;G1G2Sc9VPA;RfReAcS54RdR5A2RcRbRaA6F_;F_;F_;F_;TS';TS;F_;Fnx;FN;Fw;Ftp;Frho;FA;Fnd;FKc;") := ltac2:(tb__ "0|1|
SdfVAInv;VCST;VXGL;VALA;S68Vrho0;VP0f;S3bS3aS2dS2dA2M0A1S3bS3aG0S2dA2A1Sc9VPA;ScaS95VPA;A1ScdScbS9bVPA;A1A10").
Let uncarveK : ltac2:(tb__ "0|5|
Se7S77S4cS3S38S6aQ40A1A1S38S56A1M0Sf4S57S38S1A1M1S38SdbA1Se8RaA1S30G1S8S4bR9A1A1S43S1R3SadSdbS1SdcR2A4A3A3S30S37Se2ScaR3A2S39A3S30S85S7cRcA1S7aA3S30S37S78S5S4bRcA1A1RdA2S39A3S6dS4aSddVAInv;VCST;VXGL;S68Vrho0;VP0f;S3bS3aS2dS2dA2M2A1M3S3bS3aG2S2dA2A1M4Sc9VPA;RfReAcRdRcRbS42G0S103RaS105R9R8A2A4A6S6dS4aSddVAInv;VCST;VXGL;S68Vrho0;VP0f;G3G4Sc9VPA;R10RfAcS54ReSf1S4bReA1R8A2A2SeeRdSadSdbS1SdcR7A4S121R9RcRaA3A3RcS42G0S103RbS105RaR9A2A4A6F_;F_;F_;F_;F_;F_;FN;Fobjs;Fmd;Fms;Ftr;Ftp;Frho;FA;Fnd;FKc;") := ltac2:(tb__ "0|1|
Se0VAInv;VCST;VXGL;VALA;VHLV;S68Vrho0;VP0f;S3bS3aS2dS2dA2M0A1S3bS3aG0S2dA2A1Sc9VPA;ScaS95VPA;A1ScdVHCK;A10").
Let pcallK := pure_callJ AInv CST XGL ALA NF rho0 P0f [] [] BX0 PA ok.

Lemma JK_Kc : ltac2:(tb__ "0|0|
S77S3S38S6aQ40A1A1S38S56A1S57VJK;R5R4R3R2R1A5VKc;R3R2A2F_;Fmd;Ftr;Ftp;Frho;Fnd;").
Proof. intros nd rho tp tr md (Ai & kc & _ & H & _). exact H. Qed.

Lemma JK_stable : ltac2:(tb__ "0|0|
S77S2eSa7S68R1A2S30S37S78R2R3A2S39A3S72S4aR3VJK;R4A1A3F_;F_;Fn;Fnd;").
Proof. intros nd n Hn Hb. apply (stableA_JA segs AInv CST XGL NF _ rho0 P0f [] [] BX0 PA HKc ALA n nd Hn Hb). Qed.

Lemma JK_tcons : ltac2:(tb__ "0|0|
S77S3S38S6aQ40A1A1S38S56A1S57VJK;R5R4R3R2R1A5Sa2VSpec;R3A2F_;Fmd;Ftr;Ftp;Frho;Fnd;").
Proof. intros nd rho tp tr md H. apply (HKtc tr md). exact (JK_Kc _ _ _ _ _ H). Qed.

Lemma okKK : ok_frameKA segs Kc ok.
Proof. split; [apply HOKJ | apply HOKP]; intros rho tp tr md H; exact (HKtc tr md H). Qed.

Lemma JK_okframe : ltac2:(tb__ "0|0|
S77S6fS4aVok;VJK;R1A1A3Fnd;").
Proof. intros nd. apply HOKJ. apply JK_tcons. Qed.

Lemma JK_run : ltac2:(tb__ "0|1|
S77S3eS38S2dA1S4cS38S4dA1M0S3S38S6aQ40A1A1Sa3S30S3cG0A1S50S4aR7R6R5S39A5S40G0R4A2A3S30S37SeS4bR6A1A1S3fA3S30S37Sa5S68S5S4bR7A1A1A2S39A3S30S37S78S5S4bR8A1A1RbA2S39A3S4dS3S74S4dR2RaA3S23S5S4bRcA1A1RaR2A3Sa0S4aVok;S6dS4aVJK;R10A1S52R4A1R3RaA5R9A4F_;F_;Frho';FL;Sa0S4aVok;S6dS4aVJK;RdA1RaR8R7A5R6A4F_;F_;F_;F_;F_;FQ;Ftp;Frho;Fleaves;FA;Fcuts;Ffuel;Fnd;").
Proof.
  intros nd fuel cuts A leaves rho tp Q Hrun Hlen Hnf Hnb H. apply Pos.leb_le in Hnf.
  eapply (runA_tr segs ok fuel cuts A leaves (JK nd) rho tp Q Hrun Hlen (JK_okframe nd) (JK_stable nd _ Hnf Hnb) H).
Qed.

Lemma JK_entails : ltac2:(tb__ "0|1|
S4cS4cSedS77S77S3S38S6aQ40A1A1Sa1S30S37S55R8R7R6A3S39A3S30S37Sf0R7S68A2S39A3S30S37Sa5S68S5S4bRaA1A1A2S39A3S30S37S78S5S4bRbA1A1R8A2S39A3S30S37S10eRaS79R9A1S79R8A1A3S39A3S30S37S86RbS80RaA1S80R9A1A3S39A3S30S37S102S6S4bReA1A1S101RcS7fRaA1A2S7fRbA1A3S39A3S30S37S83S84RdS7cRbA1A2S7cRcA1A2S39A3S6dS4aVJK;RdA1M0R10RbRaR9A6S6dS4aG0R10SefRcRfA2RbRaA6F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fndj;Fndi;Fs;FT;FL;").
Proof.
  intros L T s ndi ndj rho tp w. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 P0f [] [] BX0 PA HKc).
Qed.

Definition sp0_off (b : sv) : option Z := ltac2:(tb__ "0|d|
S0S3cS2dA1M0Lb;Vb;S2dS46S2dA1M1Lz;M2S2eS2eG0Li;M3R1S2eG1Lp;M4G4S40S2dZ0A2X2ex3Li;Sb0S0S0Sb0G0Lop;R3S0G0La;R2G2S2eG3R1G4G4S0G0Lb0;R2S2dS40S2dR1A2Ld;S2eG1Li0;Sb0S0S0G1Lb1;La0;M5Lop0;M6G6Sb1G5Lop0;M7G7S37S2fS0G1La0;Lw;Lsgn;M8S2eS0S2dG1Lk;M9Li0;Ll;X0x8X2ex3Li;G6G6G7G7G8S2eS0G9Li;Ll;MaX0x8G1G1G1G1G1G1G1G1G1Xb0xaLb0;La;Lop;Sb0S0S0G1Lb0;La;MbLop;Sb1GbLop;McGcS37S2fS0G1La;Lw;Lsgn;GaX0x8").

Definition argtop_factsb (facts : list sprop) : bool := ltac2:(tb__ "0|0|
S3dS73S2S9SaS106SbbS4Z20A1A2SbcA2A1Vfacts;A3S73S2S9SaSbcS4S61Z2Z2fA2A1A2A1Vfacts;A3A2").
Definition sp0_rangeb (facts : list sprop) (b : sv) (l h : sv) : bool := ltac2:(tb__ "0|b|
S3cS2dA1S37Lx;S8dVb;A1S2dS0S37Ll;Vl;S2dS0S37Lh;Vh;S2dS3dS3dS3dS3dS3dS3dS62S65S61Z2M0Z14A2A1S5fR3R2A2A2S62R2R1A2A2S45S62S5fR3R1A2M1Z0M2A2S3dS62G1Z20A2S97Vfacts;A1A2A2A2S62S65S61G0Z28A2M3A1M4R2A2A2S66R1G3A2A2S62G4R3A2A2S62R3G2A2A2Lhi;S2eS3fLi;M5Sb0S0S0S3fLb0;La;M6Lop;M7G7Sb1G6Lop;M8G8S37S2fS0S3fLa;Lw;Lsgn;M9S2eS0S2dS3fLk;Li;Ll0;MaX0x8Llo;G5G7G7G8G8G9GaX0x8Ld;S3fX3cx2").
Lemma argtop_sound : ltac2:(tb__ "0|4|
S3S38S2A1SacS2SdR2A1R1A3S30S37S97R2A1S39A3S31S60Z7fff80000000S6bQ40M0SbR4P1M1A2A2M2A2S60G2S64S61Z2Z2fA2M3Ze0A2A2A2S60S5fS6bG0SbR5G1A2A2Z20A2G3A2F_;F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF H Hsp. unfold argtop_factsb in H. apply andb_prop in H as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as A1. pose proof (holds_mem _ _ _ HF H2) as A2. cbn [holds] in A1, A2.
  unfold vA1, sp0, add in A1, A2. cbn [eval] in A1, A2. rewrite add_val, !lit_unsigned in A1. rewrite lit_unsigned in A2.
  change (32 mod 2 ^ 64) with 32 in A1. change (2 ^ 47 mod 2 ^ 64) with (2 ^ 47) in A2.
  rewrite Z.mod_small in A1 by lia. lia.
Qed.
Definition cst_rangeb (b : sv) (l h : sv) : bool := ltac2:(tb__ "0|7|
S0S37Lb;Vb;S2dS2dS37Lz;R1S0S37Ll;Vl;S2dS0S37Lh;Vh;S2dS3dS3dS3dS3dS62Z0R2A2S62R2R1A2A2S66R1S61Z2Z3eA2A2A2S113SccR2S64R1R2A2A3A2S45S62R1Sd5A2S62S5fSd5Z4A2R2A2A2A2Lhi;S2eS3fLi;M0Sb0S0S0S3fLb0;La;M1Lop;M2G2Sb1G1Lop;M3G3S37S2fS0S3fLa;Lw;Lsgn;M4S2eS0S2dS3fLk;Li;Ll0;M5X0x8Llo;G0G2G2G3G3G4G5X0x8S2eS3fLp;M6G6X2dx3Lz;G0G2G2G3G3G4G5X0x8").

Definition arg1b (facts : list sprop) (o : sobj) : bool := ltac2:(tb__ "0|2|
S3dS3dS3dS3dS3dS3dScS1dVo;A1SbcA2ScS1fVo;A1S4Z0A1A2A2ScS1eVo;A1Sc5A2A2S73S2S9SaS106SbbS4Z20A1A2SbcA2A1Vfacts;A3A2S73S2S9SaSbcS4S61Z2M0Z2fA2A1M1A2A1Vfacts;A3A2S73S2S9SaS106SbcSc5A2G1A2A1Vfacts;A3A2S73S2S9SaSc5S4S61G0Z16A2A1A2A1Vfacts;A3A2").
Definition drv_objb (facts : list sprop) (o : sobj) : bool := ltac2:(tb__ "0|3|
S45S45S9cS1dVo;A1M0S1fVo;A1M1S1eVo;A1M2A3S9fVfacts;G0G1G2A4A2S96Vfacts;Vo;A2A2").

Definition robjs_checkD (facts : list sprop) (tv : list (sv * sv)) (skip : option nat) (R : list sobj) : bool := ltac2:(tb__ "0|0|
S115Vfacts;Vtv;Vskip;S90Vfacts;A1VR;A5").

Lemma arg1b_sound : ltac2:(tb__ "0|5|
S3S38S2A1S1S2dSacS2SdR4A1R3A3S31S60Z7fff80000000S6bQ40M0SbR5P1M1A2A2M2A2S60G2S64S61Z2Z2fA2M3Ze0A2A2A2S30S37S96R5R4A2S39A3S31S60S44S2dS2dS18R7R5A2M4A3R4A2S63R4S47S2dS2dG4A3A2A2S31S60S5fS6bG0SbR8G1A2A2Z20A2R5A2S63R5G3A2A2F_;F_;F_;F_;Fa;Fo;Ffacts;Frho;").
Proof.
  intros rho facts o a HF Hsp H Hr. unfold arg1b in H.
  apply andb_prop in H as [H F3]. apply andb_prop in H as [H F2]. apply andb_prop in H as [H F4]. apply andb_prop in H as [H F1].
  apply andb_prop in H as [H E3]. apply andb_prop in H as [E1 E2].
  apply sv_eqb_sound in E1. apply sv_eqb_sound in E2. apply sv_eqb_sound in E3.
  pose proof (holds_mem _ _ _ HF F1) as A1. pose proof (holds_mem _ _ _ HF F2) as A2. pose proof (holds_mem _ _ _ HF F3) as A3.
  pose proof (holds_mem _ _ _ HF F4) as A4.
  cbn [holds] in A1, A2, A3, A4. unfold vA1, vL3, add, sp0 in *. cbn [eval] in A1, A2, A3, A4.
  rewrite add_val, ?lit_unsigned in A1. rewrite ?lit_unsigned in A3. rewrite ?lit_unsigned in A4. rewrite !add_val, !lit_unsigned in A2.
  change (32 mod 2 ^ 64) with 32 in A1. rewrite Z.mod_small in A1 by lia. change (2 ^ 22 mod 2 ^ 64) with (2 ^ 22) in A3.
  change (2 ^ 47 mod 2 ^ 64) with (2 ^ 47) in A2, A4.
  pose proof (urange (rw rho 8%positive)) as R8. pose proof (urange (rw rho 10%positive)) as R10.
  rewrite Z.mod_small in A2 by lia.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite E1, E2, E3 in Hr. cbn [fst snd eval] in Hr.
  rewrite soff_lit_small in Hr by lia. rewrite soff_snorm in Hr. unfold U in Hr. cbn [eval] in Hr. rewrite snorm_small in Hr by lia.
  lia.
Qed.

Definition drv_xrb (r : sv * sv) : bool := ltac2:(tb__ "0|19|
S0S37Lx;M0S44S0S0Vr;A3S2dG0S47S0S0Vr;A3M1S2dS3dS3dS3dS3dS62Z0M2R2A2M3S62G2R1A2A2S66S5fR2R1A2M4S61Z2M5Z3eA2A2A2S113SccR2R1A3A2S45S62G4Sd5A2S62S5fSd5Z4A2R2A2A2A2Ll;S2eS3fLi;M6Sb0S0S0S3fLb0;M7La;M8Lop;M9G9Sb1G8Lop;MaGaS37S2fS0S3fLa;Lw;Lsgn;MbS2eS0S2dS3fLk;McLi;Ll;MdX0x8Lb;S2eG0G1S2dS3cS2dA1S37Lx;MeS8dS1cR2A1A1S2dS3dS3dS62S65S61G5Z14A2A1R1A2G3A2S62S5fR1R2A2G2A2A2Ld;MfS3fX3cx2Ll;S2eS3fLi0;M10G9G9GaGaGbS2eS0GcLi0;Ll;X0x8Li;Sb0S0S0G0G1S2dGeS8dS1bR4R3R2A3A1GfS3fX3cx2Ll;G6Sb0S0S0S3fLb1;La0;M11Lop0;M12G12Sb1G11Lop0;M13G13S37S2fS0S3fLa0;M14Lw;Lsgn;M15GdX0x8Lb0;La;Lop;Sb0S0S0G0G1S2dGeS8dS25R4R3R2A3A1GfS3fX3cx2Ll;G6G12G12G13G13G15GdX0x8Lb0;La;Lop;Sb1S0S0G0G1S2dGeS8dS28R4R3R2A3A1GfS3fX3cx2Ll;G6G12G12G13G13G15GdX0x8Lb0;La;Lop;Sb1S0S0G0G1S2dGeS8dS29R4R3R2A3A1GfS3fX3cx2Ll;G6G12G12G13G13G15GdX0x8Lb0;La;Lop;S37S2fS0G0G1S2dGeS8dS26R4R3R2A3A1GfS3fX3cx2Ll;G6Sb0S0G7La0;M16Lop;M17G17Sb1G16Lop;M18G18S37S2fG14Lw0;Lsgn0;GdX0x8La;Lw;Lsgn;S2eS0S2dG0G1S2dGeS8dS27R4R3R2A3A1GfS3fX3cx2Ll;G10G9G9GaGaGbS2eS0S2dS3fLk0;Li0;Ll;X0x8Lk;Li;Ll0;X0x8").

Definition sp0_factsb (facts : list sprop) : bool := ltac2:(tb__ "0|2|
S3dS3dS3dS73S2S9SaS4Z7fff80000000A1SbbA2A1Vfacts;A3S73S2S9SaSbbS4S64S61Z2Z2fA2Ze0A2A1A2A1Vfacts;A3A2S73S2S9SaS1bSb2S1cP1A1S4N800000A1A3M0S1cP1eA1M1A2A1Vfacts;A3A2S73S2S9SaG1G0A2A1Vfacts;A3A2").

Lemma sp0_facts_sound : ltac2:(tb__ "0|2|
S3S38S2A1SacS2SdR2A1R1A3S30S37S8cR2A1S39A3S31S31S60Z7fff80000000S6bQ40M0SbR4P1A2A2M1A2S60G1S64S61Z2Z2fA2Ze0A2A2A2S30S2dS6bG0SbR4P1eA2A2S64G1Z800000A2A3A2F_;F_;Ffacts;Frho;").
Proof.
  intros rho facts HF H. unfold sp0_factsb in H. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  pose proof (holds_mem _ _ _ HF H1) as A1. pose proof (holds_mem _ _ _ HF H2) as A2.
  pose proof (holds_mem _ _ _ HF H3) as A3. pose proof (holds_mem _ _ _ HF H4) as A4.
  cbn [holds] in A1, A2, A3, A4. unfold sp0 in A1, A2. cbn [eval] in A1, A2, A3, A4. rewrite lit_unsigned in A1, A2.
  rewrite Z.mod_small in A1 by lia. rewrite Z.mod_small in A2 by lia.
  rewrite add_val, lit_unsigned in A3, A4. pose proof (urange (rw rho 1%positive)) as R1.
  change ((-8388608) mod 2 ^ 64) with (2 ^ 64 - 8388608) in A3, A4.
  replace ((bv_unsigned (rw rho 1%positive) + (2 ^ 64 - 8388608)) mod 2 ^ 64) with (bv_unsigned (rw rho 1%positive) - 8388608) in A3, A4
    by (replace (bv_unsigned (rw rho 1%positive) + (2 ^ 64 - 8388608)) with ((bv_unsigned (rw rho 1%positive) - 8388608) + 1 * 2 ^ 64) by lia;
        rewrite Z.mod_add by lia; symmetry; apply Z.mod_small; lia).
  lia.
Qed.

Lemma sp0_off_sound : ltac2:(tb__ "0|2|
S3S0S2dS30S3cS2dA1S8dR2A1S40S2dR1A2A3S31S60S65S61Z2Z28A2A1R2A2S60R2Z0A2A2S60Z7fff80000000S6bQ40M0SbR5P1M1A2A2A2S30S2dS6bG0S10R6R5A2A2S5fS6bG0SbR6G1A2A2R4A2A3F_;F_;F_;Fd;Fb;Frho;").
Proof.
  intros rho b d H Hd Hsp. unfold sp0_off in H.
  destruct b as [z|v|op a1 b2|op a1 b2|op a1 b2|op a1 b2|sg w a1|l i k]; try discriminate.
  - destruct v; try discriminate. injection H as <-. cbn [eval]. lia.
  - destruct op; try discriminate. destruct a1 as [z|v|op a1' b2'|op a1' b2'|op a1' b2'|op a1' b2'|sg w a1'|l i k]; try discriminate.
    destruct v; try discriminate.
    destruct b2 as [d'|v'|op b1' b3'|op b1' b3'|op b1' b3'|op b1' b3'|sg w b1'|l i k]; try discriminate. injection H as <-.
    pose proof (urange (rw rho 1%positive)). rewrite U_add_lit; [cbn [eval]; reflexivity | lia | cbn [eval]; lia].
Qed.

Lemma drv_objb_core : ltac2:(tb__ "0|1|
S3S38S2A1S1S2dSacS2SdR4A1R3A3S30S37S8cR4A1S39A3S30S37S90R5R4A2S39A3S31S60S44S2dS2dS18R7R5A2M0A3R4A2S63R4S47S2dS2dG0A3A2A2S33S31S60S6bQ40SbR8P1eA2A2R5A2S63R5S61Z2Z2fA2A2A2S31Sd4VCST;R5A2S35Se9R5A1A1A2A2F_;F_;F_;F_;Fa;Fo;Ffacts;Frho;").
Proof using HCSTdrv.
  intros rho facts o a HF Hspf H Hr. pose proof (sp0_facts_sound rho facts HF Hspf) as [Hsp H30].
  unfold drv_objb in H. apply orb_prop in H as [H|H]; [|left; pose proof (arg1b_sound rho facts o a HF Hsp H Hr); lia].
  apply orb_prop in H as [H|H].
  - unfold cst_rangeb in H. destruct (ob_base o) as [z|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?] eqn:EB; try discriminate. destruct z; try discriminate.
    destruct (ob_lo o) as [lo|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?] eqn:EL; try discriminate.
    destruct (ob_hi o) as [hi|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?] eqn:EH; try discriminate.
    apply andb_prop in H as [H HE]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3.
    unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite EB, EL, EH in Hr. cbn [ob_base ob_lo ob_hi fst snd eval] in Hr.
    rewrite lit_unsigned, (Z.mod_small 0) in Hr by lia. rewrite !soff_lit_small in Hr by lia.
    right. split; [apply HCSTdrv; eapply lit_in_ranges_sound; [exact H4|]; lia|].
    unfold errno_addrA. apply orb_prop in HE as [HE|HE]; apply Z.leb_le in HE; lia.
  - unfold sp0_rangeb in H. destruct (sp0_off (ob_base o)) as [d|] eqn:ED; [|discriminate].
    destruct (ob_lo o) as [lo|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?] eqn:EL; try discriminate.
    destruct (ob_hi o) as [hi|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?] eqn:EH; try discriminate.
    apply andb_prop in H as [H H7]. apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H4. apply Z.ltb_lt in H5. apply Z.leb_le in H6. apply Z.leb_le in H7.
    assert (H3' : d + hi <= 0 \/ (d + hi <= 32 /\ bv_unsigned (rw rho 1%positive) + 32 <= 2 ^ 47)).
    { apply orb_prop in H3 as [H3|H3]; [left; apply Z.leb_le in H3; exact H3|].
      apply andb_prop in H3 as [H3 HT]. apply Z.leb_le in H3. right. split; [exact H3 | exact (argtop_sound rho facts HF HT Hsp)]. }
    left. unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite EL, EH in Hr. cbn [fst snd] in Hr.
    rewrite !soff_lit_small in Hr by lia. rewrite (sp0_off_sound rho (ob_base o) d ED ltac:(lia) ltac:(lia)) in Hr.
    lia.
Qed.

Lemma drv_xrb_core : ltac2:(tb__ "0|1|
S3S38S2A1S3aS0S0A2S2dSacS2SdR4A1R3A3S30S37S8cR4A1S39A3S30S37S8eR4A1S39A3S31S60SfcR7S44S0S0R5A3A2M0R4A2S63R4S5fG0SfcR7S47S0S0R5A3A2A2A2A2S33S31S60S6bQ40SbR8P1eA2A2R5A2S63R5S61Z2Z2fA2A2A2S31Sd4VCST;R5A2S35Se9R5A1A1A2A2F_;F_;F_;F_;Fa;Fr;Ffacts;Frho;").
Proof using HCSTdrv.
  intros rho facts [b l] a HF Hspf H Hr. pose proof (sp0_facts_sound rho facts HF Hspf) as [Hsp H30].
  unfold drv_xrb in H. cbn [fst snd] in H, Hr. unfold uval in Hr.
  destruct l as [l|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ?];
    [| destruct b; discriminate | destruct b; discriminate | destruct b; discriminate | destruct b; discriminate
     | destruct b; discriminate | destruct b; discriminate | destruct b; discriminate].
  replace (bv_unsigned (eval rho (SLit l))) with (l mod 2 ^ 64) in Hr by (cbn [eval]; rewrite lit_unsigned; reflexivity).
  destruct b as [bz|v|op a1 b2|op a1 b2|op a1 b2|op a1 b2|sg w a1|li i k]; try discriminate.
  - apply andb_prop in H as [H HE]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. rewrite Z.mod_small in Hr by lia.
    cbn [eval] in Hr. rewrite lit_unsigned, Z.mod_small in Hr by lia.
    right. split; [apply HCSTdrv; eapply lit_in_ranges_sound; [exact H4 | lia]|].
    unfold errno_addrA. apply orb_prop in HE as [HE|HE]; apply Z.leb_le in HE; lia.
  - cbn [sp0_off] in H. destruct v; try discriminate.
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    rewrite Z.mod_small in Hr by lia. cbn [eval] in Hr. left. lia.
  - destruct (sp0_off (SAlu op a1 b2)) as [d|] eqn:ED; [|discriminate].
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    rewrite Z.mod_small in Hr by lia. rewrite (sp0_off_sound rho _ d ED ltac:(lia) ltac:(lia)) in Hr. left. lia.
Qed.

Lemma drv_objb_sound : ltac2:(tb__ "0|1|
Sa8S3cS2dA1S3S38S2A1S1S2dSacS2SdR4A1R3A3S30S37S8cR4A1S39A3S108R6SaaSa9R8A1A1A2S30S37S90R6R5A2S39A3S31S60S44S2dS2dS18R8R6A2M0A3R5A2S63R5S47S2dS2dG0A3A2A2S112VCST;RbRaR6A4F_;F_;F_;F_;F_;Fa;Fo;Ffacts;Frho;Fx;FAi;").
Proof using HCSTdrv.
  intros Ai x rho facts o a HF Hs [HT _] H Hr. change (rw rho V_TOP) with (rw rho 30%positive) in HT.
  destruct (drv_objb_core rho facts o a HF Hs H Hr) as [X|X]; [left; rewrite <- HT; exact X | right; left; exact X].
Qed.
Lemma drv_xrb_sound : ltac2:(tb__ "0|1|
Sa8S3cS2dA1S3S38S2A1S3aS0S0A2S2dSacS2SdR4A1R3A3S30S37S8cR4A1S39A3S108R6SaaSa9R8A1A1A2S30S37S8eR5A1S39A3S31S60SfcR8S44S0S0R6A3A2M0R5A2S63R5S5fG0SfcR8S47S0S0R6A3A2A2A2A2S33S112VCST;RbRaR6A4Sd4VXGL;R6A2A2F_;F_;F_;F_;F_;Fa;Fr;Ffacts;Frho;Fx;FAi;").
Proof using HCSTdrv.
  intros Ai x rho facts r a HF Hs [HT _] H Hr. change (rw rho V_TOP) with (rw rho 30%positive) in HT.
  left. destruct (drv_xrb_core rho facts r a HF Hs H Hr) as [X|X]; [left; rewrite <- HT; exact X | right; left; exact X].
Qed.

Definition xrs_checkD (facts : list sprop) (tv : list (sv * sv)) (skip : option nat) (objs : list sobj)
           (extra : sv * sv -> bool) (X : list (sv * sv)) : bool := ltac2:(tb__ "0|2|
S75S3aS0S0A2M0G0S37S37L_;M1S114Vtv;Vskip;R1A3S39G1S73S1S117Vfacts;R1A2Vobjs;A3S39Vextra;R1A1X37x2X37x2Lr;VX;A3").
Lemma xrs_checkD_A : ltac2:(tb__ "0|2|
S38S2A1S38S3aS0S0A2M0A1M1S3cS3eA1S38S1A1G0S37F_;G1S30S37S8fR6R5R4R3R2R1A6S39A3S30S37S118VXGL;R7R6R5R4R3R2A7S39A3F_;FX;Fextra;Fobjs;Fskip;Ftv;Ffacts;").
Proof.
  intros facts tv skip objs extra X H. unfold xrs_checkD in H. rewrite xrs_checkA_ref_eq. unfold xrs_checkA_ref.
  apply forallb_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) H r Hr) as Hc. cbn beta in Hc.
  destruct (xr_lit_in XGL r); [reflexivity | exact Hc].
Qed.

Lemma site_ok_drv : ltac2:(tb__ "0|9|
S77S4cSedS38S1A1S3S3cS3eA1M0S3cS2dA1M1Sa8Sf4OF_;F_;S30S37S8cS6S4bR7A1A1A1S39A3S30S37S91S6S4bR8A1A1S79R9A1R4R6A4S39A3S30S37S8fS6S4bR9A1M2A1S79RaA1R5S8G2A1S8eS4eR9A1A6S39A3Sa8SacS2SdR8A1S6S4bRbA1A1A3S81S3bS3aS2dS2dA2M3A1M4R2R9S79RdA1A4S10aRaS79ReA1A2G0OLskip;RaS3eG1OLx;M5RaS2dS34S3aS0S0A2M6G6S31S30S3cG6A1S76G6S79R12A1M7R3A3S40G6R1A2A3S31S10dReR1A2S30S2dS44S2dS2dS109ReR1A2A3R2A3A2A2Lt;A2Lxb;S32X3cx2Li;G5R9S2dS32Lz;S36X3cx2X3cx2F_;F_;F_;FAi;Sa8Sf4SacS2SdRaA1S6S4bRdA1A1A3VP0f;Vrho0;A1S123S68Vrho0;RcA3S81G4R5RdS79R11A1A4S10fReG7A2S10aRfS79R13A1A2S34S3S3S34S38S6aQ40A1A1M8G8S34S57S57VAInv;RbR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2ReR9R8A2F_;F_;F_;F_;F_;F_;F_;Fms;FAi;S116VAInv;VCST;VXGL;S68Vrho0;VP0f;G4S3bS3aG3S2dA2A1RcRbRaR9RdR7R6AfF_;F_;F_;F_;F_;Fextra;Fx;Fskip;Frho;FR;Fs;FCl;Fnd;").
Proof using ALA HCSTdrv.
  intros nd Cl s R rho skip x extra Hspf Hro Hxr Hsx Hex Ai ms HF HP0 Hav HB HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HTPA HTok.
  split; [|split].
  - eapply (robjs_checkA_sound segs AInv CST ALA [] Ai rho _ (nd_tv nd) skip (drv_objb (ss_facts (ax_S Cl))) R x rho1 tp1 md1 HM HF HN HD HZ HTok Hro).
    + intros o a Ho He Hr. eapply drv_objb_sound; eauto.
    + exact (Hsx Ai HF HN HZ).
  - eapply (xrs_checkA_sound segs AInv CST XGL ALA [] Ai rho _ (nd_tv nd) skip (ss_objs (ax_S Cl)) drv_xrb (ax_X Cl) x rho1 tp1 md1 HM HF HN HD HZ HTok (xrs_checkD_A _ _ _ _ _ _ Hxr)).
    + intros r a Hr He Ha. eapply drv_xrb_sound; eauto.
    + exact (Hsx Ai HF HN HZ).
  - apply (Hex Ai ms HF HP0 Hav HN HD HZ). exists rho1, tp1, md1. exact HM.
Qed.

Definition kept_nzb (facts : list sprop) (kept : list (sv * sv)) : bool := ltac2:(tb__ "0|1|
S75S3aS0S0A2M0G0S73S2S9SaS4Z1000A1S44S0S0R1A3A2A1Vfacts;A3Lt;Vkept;A3").

Lemma kept_in_FBx : ltac2:(tb__ "0|4|
S3S3S38S2A1S38S3aS0S0A2M0A1G0S2dSacS2SdR5A1R4A3S30S37S92R5R4A2S39A3S74G0R4R5A3S31S60S44S2dS2dS109R8R5A2M1A3M2R4A2S63R4S5fG2S47S2dS2dG1A3A2A2A2S127VCST;RaS10bS3bS3aS2dS2dA2M3A1R9R7A3S126S3bS3aG3S2dA2A1R9S3bS3aS3aS0S2dA2S0A2A1A3R5A5F_;F_;F_;F_;Fa;Ft;Fkept;Ffacts;Frho;Fr0;").
Proof.
  intros r0 rho facts kept t a HF Hk Hin Ha. right; right; left. exists (fst (tvv rho t)), (snd (tvv rho t)). split; [|exact Ha].
  unfold FBx. cbn [app]. apply in_map_iff. exists t. rewrite <- surjective_pairing. split; [reflexivity|].
  apply filter_In. split; [exact Hin|]. apply (proj2 (tnzb_true rho t)).
  pose proof (holds_mem _ _ _ HF (proj1 (forallb_forall _ _) Hk t Hin)) as X. cbn [holds] in X.
  rewrite U_lit, <- M64v_eq, Z.mod_small in X by lia. unfold tnz. unfold tvv in Ha |- *. cbn [fst] in Ha, X |- *. lia.
Qed.

Lemma T0_of_site : ltac2:(tb__ "0|0|
S3S3Sa8S82R3R1A2S108R3SaaSa9R2A1A1A2S30S2dS107R5A1S6bQ40SbR4P1eA2A2A3F_;F_;FAi;Frho;Fr0;").
Proof. intros r0 rho Ai HTPA [HT _]. rewrite <- (TPA_top _ Ai HTPA). symmetry. exact HT. Qed.

Lemma robjs_okF_drv : ltac2:(tb__ "0|1|
S3S38S2A1S38S3aS0S0A2A1S38S1A1SacS2SdR4A1R3A3S30S37S8cR4A1S39A3S30S2dS107Vrho0;A1S6bQ40SbR6P1eA2A2A3S30S37S92R6R5A2S39A3S30S37S75S1S1S45S90R8R1A2S10cR7S46S3eA1R1A3A2Lo;R5A3S39A3S128VCST;Vrho0;S3bS3aS2dS2dA2M0A1S3bS3aG0S2dA2A1R9R7S3bS3aS3aS0S2dA2S0A2A1R6A8F_;F_;F_;F_;F_;FR;Fkept;Ffacts;Frho;").
Proof using HCSTdrv.
  intros rho facts kept R HF Hspf HT30 Hk Hchk o a Ho Hr.
  pose proof (proj1 (forallb_forall _ _) Hchk o Ho) as Hc. apply orb_prop in Hc as [Hc|Hc].
  - destruct (drv_objb_core rho facts o a HF Hspf Hc Hr) as [X|X]; [left; rewrite HT30; exact X | right; left; exact X].
  - destruct (robj_tracked_sound kept None o Hc) as (j & t & Hj & _ & Hb & Hl & Hh).
    destruct (tracked_range rho o t a Hb Hl Hh Hr) as [Ha _].
    eapply kept_in_FBx; [exact HF | exact Hk | eapply nth_error_In; exact Hj | exact Ha].
Qed.

Lemma xrs_okF_drv : ltac2:(tb__ "0|3|
S3S38S2A1S38S3aS0S0A2M0A1M1G1SacS2SdR4A1R3A3S30S37S8cR4A1S39A3S30S2dS107Vrho0;A1S6bQ40SbR6P1eA2A2A3S30S37S92R6R5A2S39A3S30S37S75G0G0S45S8eR1A1S114R7S46S3eA1R1A3A2Lr;R5A3S39A3S129VCST;VXGL;Vrho0;S3bS3aS2dS2dA2M2A1S3bS3aG2S2dA2A1R9R7S3bS3aS3aS0S2dA2S0A2A1R6A9F_;F_;F_;F_;F_;FX;Fkept;Ffacts;Frho;").
Proof using HCSTdrv.
  intros rho facts kept X HF Hspf HT30 Hk Hchk r a Hr Ha.
  pose proof (proj1 (forallb_forall _ _) Hchk r Hr) as Hc. apply orb_prop in Hc as [Hc|Hc].
  - left. destruct (drv_xrb_core rho facts r a HF Hspf Hc Ha) as [Y|Y]; [left; rewrite HT30; exact Y | right; left; exact Y].
  - left. unfold xr_tracked in Hc. destruct (robj_tracked_sound kept None _ Hc) as (j & t & Hj & _ & Hb & Hl & Hh). cbn [ob_base ob_lo ob_hi] in Hb, Hl, Hh.
    eapply kept_in_FBx; [exact HF | exact Hk | eapply nth_error_In; exact Hj |].
    destruct r as [b l]. cbn [fst snd] in Hb, Hh, Ha. subst. unfold tvv. destruct t as [tb tl]. cbn [fst snd] in Ha |- *. unfold uval in Ha. exact Ha.
Qed.

Lemma In_dropX : ltac2:(tb__ "0|3|
S3aS0S0A2M0S37F_;S38G0A1M1G0S74G0R1S11cG0G1S11eG0A1G0S11bR4R1A1M2A1Lx;G0S11dG2A1Lx;R2A6A3S74G0R2R3A3F_;Fr;FX;Ff;").
Proof.
  intros f X. induction X as [|x l IH]; intros r Hr; cbn in Hr; [exact Hr|].
  destruct (f x); cbn in Hr; [destruct Hr as [<-|Hr]; [left; reflexivity | right; apply IH; exact Hr] | right; apply IH; exact Hr].
Qed.

Lemma wcanon_nil : wcanon [].
Proof. exists 0%nat. split; [apply le_0_n | reflexivity]. Qed.

Lemma is_prefix_app_mono {A} : ltac2:(tb__ "0|1|
S38VA;A1M0G0G0S104VA;R2R1A3S104VA;S43VA;R4R3A3S43VA;R4R2A3A3F_;Fl2;Fl1;Fa;").
Proof. induction a; cbn; auto. Qed.
Lemma is_prefix_firstn {A} : ltac2:(tb__ "0|1|
S3eS38VA;A1M0G0S104VA;SaeVA;R3R2A3S43VA;R2R1A3A3Fr;Fl;Fk;").
Proof. induction k as [|k IH]; intros [|x l] r; cbn; auto. Qed.
Lemma firstn_map' {A B} : ltac2:(tb__ "0|0|
VA;VB;F_;S3eS38VA;A1S30S38VB;A1SaeVB;R2SadVA;VB;R3R1A4A3SadVA;VB;R3SaeVA;R2R1A3A4A3Fl;Fk;Ff;").
Proof. intros f k. induction k as [|k IH]; intros [|x l]; cbn; rewrite ?IH; reflexivity. Qed.

Section ExitCall.
Variable ph : bool.
Variable ndX : ndesc.
Variables n c : Z.
Variable CX : axst.
Variable s : wsub.
Variable R : list sobj.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S30S37Sa5S68S5S4bVCX;A1A1A2S39A3").
Hypothesis Hnb : ltac2:(tb__ "0|0|
S30S37S78S5S4bVCX;A1A1VndX;A2S39A3").
Hypothesis Hfr : ltac2:(tb__ "0|1|
S30S3cS38S1A1M0A1Se3VCX;S8aVph;Vn;Vc;A3Vs;A3S40G0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S30S37Se4VCX;S8aVph;Vn;Vc;A3Vs;VR;S3bS4cA1A5S39A3").
Hypothesis Hfb : ltac2:(tb__ "0|1|
S30S37S75S2S19S5S4bVCX;A1M0A1A1S6G0A1A3S39A3").
Hypothesis Hsupp : ltac2:(tb__ "0|0|
S74S3aS2dS2dA2S42S2dS2dVn;Vc;A4S8bVph;A1A3").

Hypothesis HSPEC : ltac2:(tb__ "0|0|
S38S56A1S57VKc;R2R1A2VSpec;S43S56R3S43S56SadS6aQ8A1S56S5bSb3A1S88Vn;A1A4S41S56S59S6cQ40Vc;A2S5eR2A1A2S3bS56A1A3A3A3A1F_;Fmd;Ftr;").
Hypothesis HKfd1 : ltac2:(tb__ "0|0|
S38S56A1S57VKc;R2R1A2S30S3cS58A1S5cS5dR2A1Sb3A2S40S58S5aSb3A1A2A3F_;Fmd;Ftr;").

Lemma X_exit_call : ltac2:(tb__ "0|0|
S3S38S6aQ40A1A1Sa0S4aVok;S6dS4aVJK;VndX;A1VCX;R2R1A5Sa1S32L_;A4Ftp;Frho;").
Proof.
  intros rho tp. pose proof Hnx as Hnx'. apply Pos.leb_le in Hnx'.
  set (Jp := fun (r : valuation) (t : list word) (tr : list event) (md : Model) => JK ndX rho t tr md).
  assert (JpK : forall r t tr md, Jp r t tr md -> Kc tr md) by (intros r t tr md HJ; exact (JK_Kc _ _ _ _ _ HJ)).
  assert (TC : forall k, ok_frameA segs ok (Kw Jp n k) /\ ok_pframeA segs ok (Kw Jp n k)).
  { intros k.
    assert (T : forall r t tr md, Kw Jp n k r t tr md -> tcons Spec tr).
    { intros r t tr md (tr0 & HJ & ->). pose proof (JpK _ _ _ _ HJ) as Hk.
      exists (tr0 ++ map (WriteEv ch1) (PEND n) ++ [ExitEv (Z_to_bv 64 c) (m_fs md)]). split; [exact (HSPEC tr0 md Hk)|].
      apply is_prefix_app_mono. unfold EVS.
      eapply is_prefix_trans; [| apply is_prefix_app]. clear. generalize (PEND n) as l. intros l.
      induction k as [|k IH] in l |- *; [apply is_prefix_nil|]. destruct l; cbn; [exact I|]. split; [reflexivity | apply IH]. }
    split; [apply HOKJ; exact T | apply HOKP; exact T]. }
  apply (pcallK Kc Kc CX (Pre_exitP ph n c) s R [] rho tp ndX
           Jp (fun r t tr md => False) (fun _ => False) HKc).
  -
    intros rho1 tp1. eapply triple_conseq; [intros w' Hw'; exact Hw' | | apply (exit_sumP ok Jp Spec n c) with (ph := ph)].
    + intros w' Hf. destruct Hf.
    +   intros r r' t tr md md' Hag Hme HJ. unfold Jp in HJ |- *.
      destruct HJ as (Ai & kc & HJi). exists Ai, kc.
      eapply (JAi_stable segs AInv CST XGL NF Kc rho0 P0f [] [] BX0 PA HKc ALA (ss_next (ax_S CX)) ndX Ai kc rho rho t tr md md');
        [exact Hnx' | exact Hnb | apply agree_below_refl | exact Hme | exact HJi].
    + intros r t tr md HJ. apply (HKfd1 tr md). exact (JpK _ _ _ _ HJ).
    + intros k. exact (proj1 (TC k)).
    + intros k. exact (proj2 (TC k)).
    + exact Hokh.
    + intros r t tr md HJ. exact (HSPEC tr md (JpK _ _ _ _ HJ)).
    + exact Hsupp.
  - exact Hfr.
  - exact Hcc.
  - exact Hnx.
  - exact Hnb.
  - exact Hfb.
  - intros tr ms md Hsm HJ. exact HJ.
  - intros rhoL tr' md' Hf. destruct Hf.
  - intros L rho' Hin. destruct Hin.
Qed.
End ExitCall.

Section ExitHandoff.
Variable ndX : ndesc.
Variables n c : Z.
Variable E : axst.

Variables S1 S4 S5 S6 : sstate.
Variable idxs : list nat.
Variable R : list sobj.
Hypothesis Hnx : ltac2:(tb__ "0|0|
S30S37Sa5S68S5S4bVE;A1A1A2S39A3").
Hypothesis Hnb : ltac2:(tb__ "0|0|
S30S37S78S5S4bVE;A1A1VndX;A2S39A3").
Hypothesis HbE : ltac2:(tb__ "0|0|
S30S0S4fVE;A1S4S119A1A3").

Variable iw : nat.
Hypothesis H1n : ltac2:(tb__ "0|0|
S30S3cS1A1S76S1S8S4bVE;A1A1Viw;A3S40S1S17Sc3S4S65SbfA1A1S4Z0A1S3bSfA1S1aA5A2A3").
Variable S0 : sstate.
Hypothesis H1e : ltac2:(tb__ "0|0|
S30S7SfbS4bVE;A1Viw;Sc7A3VS0;A3").
Hypothesis H1s : ltac2:(tb__ "0|0|
S30S37Sf5S4bVE;A1VS0;A2S39A3").

Variable ie : nat.
Let S0a : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|0|
Sd2VS0;Vie;S5fS87Z8cA2Z4S64S61Z2Z20A2Z1A2A5").
Let S0b : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|0|
Sd2VS0a;Vie;S5fS87Z10A2Z8Z0A5").
Let S0c : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|1|
Sd2VS0b;Vie;S5fS87Z8M0A2G0Z0A5").
Let S0d : ltac2:(tb__ "0|0|
S7") := ltac2:(tb__ "0|0|
Sd2VS0c;Vie;S5fS87Z38A2Z8Z0A5").
Hypothesis H1i : ltac2:(tb__ "0|2|
S31S30S37Sd3S4aVS0;Vie;S5fS87Z8cA2Z4S64S61Z2Z20A2Z1A2A6S39A3S31S30S37Sd3S4aVS0a;Vie;S5fS87Z10A2Z8M0Z0M1A6S39A3S31S30S37Sd3S4aVS0b;Vie;S5fS87G0A2G0G1A6S39A3S31S30S37Sd3S4aVS0c;Vie;S5fS87Z38A2G0G1A6S39A3S30S37Sd3S4aVS0d;Vie;S5fS87Z28A2G0G1A6S39A3A2A2A2A2").
Hypothesis H1j : ltac2:(tb__ "0|0|
S30S7Sd2VS0d;Vie;S5fS87Z28A2Z8Z0A5VS1;A3").

Hypothesis H2 : ltac2:(tb__ "0|0|
S30S37SfaS48S1S8VS1;A1A2Vidxs;A2S39A3").
Hypothesis H3 : ltac2:(tb__ "0|0|
S30S3cS7A1Sf8Sf1VS1;Sf7S8VS1;A1Vidxs;A2A2U0A2S40S7VS4;A2A3").
Hypothesis H4 : ltac2:(tb__ "0|0|
S30S3cS7A1Sf9VS4;U0S4N430A1A3S40S7VS5;A2A3").

Definition S5c : sstate := ltac2:(tb__ "0|0|
S11S14VS5;A1S15VS5;A1S13VS5;A1S12VS5;A1S16VS5;A1S43S1S8VS5;A1SadSdbS1SdcSc1A4A3S6VS5;A1S5VS5;A1SeVS5;A1A9").
Hypothesis H5n : ltac2:(tb__ "0|0|
S30S2eS5VS5;A1S5S4bVE;A1A1A3").
Hypothesis H5w : swf S5c = true.
Hypothesis H5c : ltac2:(tb__ "0|0|
S30S37SdeS6VS5;A1S8VS5;A1S3bS3aS0S0A2A1ScaScbS79VndX;A1Sc1A7S39A3").
Hypothesis H6e : ltac2:(tb__ "0|1|
S30S7S11S14Sd0A1S69S15Sd0A1S41S3aS3eS0A2M0S42S3eS0U4S4SdaA1A4S3bG0A1A3A2S13Sd0A1S12Sd0A1S16Sd0A1S8Sd0A1S6Sd0A1S5Sd0A1SeSd0A1A9VS6;A3").
Hypothesis H6w : swf S6 = true.
Variable d6 : list (sv * sv).
Hypothesis H6d : ltac2:(tb__ "0|3|
S30S3cS3aS38S3aS0S0A2A1M0S38S2A1M1A2M2A1Sf6Sd0VS6;A2S40G2S42G0G1Vd6;S3bS2A1A4A2A3").
Hypothesis H6v : ltac2:(tb__ "0|4|
S33S30S38S3aS0S0A2M0A1M1Vd6;S41G0S42S0S0Sb9S4SdaA1M2A4S3bG0A1M3A3A3S30G1Vd6;S41G0S42S0S0G2Sb9A4G3A3A3A2").
Hypothesis H6f : ltac2:(tb__ "0|0|
S30S37S73S2S9S22Sb9S4SdaA1A2A1S6S4bVE;A1A1A3S39A3").
Definition CX : axst := ltac2:(tb__ "0|0|
S51VS6;S3bS3aS0S0A2A1S4fVE;A1A3").

Hypothesis Hfr : ltac2:(tb__ "0|1|
S30S3cS38S1A1M0A1Se3Sd1S89Vn;Vc;A2Sc2Sd1Vn;Vc;A3A3S40G0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S30S37Se4Sd1S89Vn;Vc;A2Sc2Sd1Vn;Vc;A3VR;S3bS4cA1A5S39A3").
Hypothesis Hfb : ltac2:(tb__ "0|1|
S30S37S75S2S19S5S4bSd1A1M0A1A1S6G0A1A3S39A3").
Hypothesis Hsupp : ltac2:(tb__ "0|0|
S74S3aS2dS2dA2S42S2dS2dVn;Vc;A4Sb4A3").
Hypothesis HSPEC : ltac2:(tb__ "0|0|
S38S56A1S57VKc;R2R1A2VSpec;S43S56R3S43S56SadS6aQ8A1S56S5bSb3A1S88Vn;A1A4S41S56S59S6cQ40Vc;A2S5eR2A1A2S3bS56A1A3A3A3A1F_;Fmd;Ftr;").
Hypothesis HKfd1 : ltac2:(tb__ "0|0|
S38S56A1S57VKc;R2R1A2S30S3cS58A1S5cS5dR2A1Sb3A2S40S58S5aSb3A1A2A3F_;Fmd;Ftr;").

Hypothesis HspfE : ltac2:(tb__ "0|0|
S30S37S8cS6S4bVE;A1A1A1S39A3").

Lemma X_exit : ltac2:(tb__ "0|0|
S3S38S6aQ40A1A1Sa0S4aVok;S6dS4aVJK;VndX;A1VE;R2R1A5Sa1S32L_;A4Ftp;Frho;").
Proof.
  intros rho tp. apply triple_factsA. intros HF.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned (eval rho sp0) <= 2 ^ 47 - 224).
  { unfold sp0. cbn [eval]. eapply (fun r f HF' Hb => proj1 (sp0_facts_sound r f HF' Hb)); [exact HF | exact HspfE]. }
  assert (Htp : eval rho vTP = eval rho (SLit TP)).
  { pose proof (holds_mem _ _ _ HF H6f) as X. cbn [holds] in X. exact X. }
  assert (HnxC : ss_next (ax_S CX) = ss_next (ax_S E)).
  { unfold CX. cbn [ax_S]. rewrite <- H6e. cbn [ss_next]. exact H5n. }
  eapply (triple_conseq (P := SPA segs (JK ndX) CX rho tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  {
  assert (HS0 : SPA segs (JK ndX) (ax_setS E S0) rho tp w).
  { rewrite <- H1e. apply (SPA_reslice segs (JK ndX) rho E iw _ O_deepS tp w H1n); try reflexivity.
    - rewrite H1e. exact H1s.
    - unfold O_deepS, spM. rewrite !obj_range_lits by (unfold DEEP; lia). rewrite U_add_lit by lia. unfold DEEP. f_equal; lia.
    - unfold O_deepS, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold DEEP; lia). unfold DEEP; lia.
    - exact HS. }
  destruct H1i as (I1 & I2 & I3 & I4 & I5).
  assert (HS1 : SPA segs (JK ndX) (mkAX S1 (ax_X E) (ax_base E)) rho tp w).
  { rewrite <- H1j.
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0d (ax_X E) (ax_base E)) ie _ 8 0 tp w I5).
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0c (ax_X E) (ax_base E)) ie _ 8 0 tp w I4).
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0b (ax_X E) (ax_base E)) ie _ 8 0 tp w I3).
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0a (ax_X E) (ax_base E)) ie _ 8 0 tp w I2).
    apply (SPA_img_cell segs (JK ndX) rho (mkAX S0 (ax_X E) (ax_base E)) ie _ 4 _ tp w I1). exact HS0. }
  pose proof (AxXform.SPA_select segs (JK ndX) rho (mkAX S1 (ax_X E) (ax_base E)) idxs tp w H2 HS1) as HS2.
  pose proof (SPA_merge segs (JK ndX) rho (mkAX (set_objs S1 (select (ss_objs S1) idxs)) (ax_X E) (ax_base E)) 0 S4 tp w H3 HS2) as HS3.
  pose proof (SPA_split segs (JK ndX) rho (mkAX S4 (ax_X E) (ax_base E)) 0 (SLit (-1072)) S5 tp w H4 HS3) as HS4.
  apply (SPA_x_sub segs (JK ndX) rho (mkAX S5 (ax_X E) (ax_base E)) [] tp w ltac:(intros rr Hrr; destruct Hrr)) in HS4.
  change (ax_setX (mkAX S5 (ax_X E) (ax_base E)) []) with (mkAX S5 [] (ax_base E)) in HS4.
  assert (HS5 : SPA segs (JK ndX) (mkAX S5c [] (ax_base E)) rho tp w).
  { pose proof (carveK Kc ndX (mkAX S5 [] (ax_base E)) rho tp w N_ex (ss_next S5) HS4) as X.
    cbn zeta in X. cbn [ax_S ax_setS ax_X ax_base] in X. apply X.
    - exact H5w.
    - apply Pos.leb_refl.
    - exact HbE.
    - exact H5c. }
  assert (HS6 : SPA segs (JK ndX) (mkAX S6 [] (ax_base E)) rho tp w).
  { change (mkAX S6 [] (ax_base E)) with (ax_setS (mkAX S5c [] (ax_base E)) S6).
    apply (SPA_restate segs (JK ndX) rho (mkAX S5c [] (ax_base E)) S6 tp w d6 [] H6w H6d).
    - rewrite <- H6e. reflexivity.
    - unfold diffs_ok. destruct H6v as [-> | ->]; (constructor; [cbn [fst snd] | constructor]); [exact Htp | symmetry; exact Htp].
    - constructor.
    - exact HS5. }
  unfold CX. exact HS6. }
  apply (X_exit_call true ndX n c CX (s_ex CX n c) R); [rewrite HnxC; exact Hnx | rewrite HnxC; exact Hnb | exact Hfr | exact Hcc | exact Hfb | exact Hsupp | exact HSPEC | exact HKfd1].
Qed.
End ExitHandoff.

Definition ob_shapeb (o : sobj) (b lo hi : sv) : bool := ltac2:(tb__ "0|2|
S3dS3dS3dS3dScS1dVo;A1Vb;A2ScS1fVo;A1Vlo;A2A2ScS1eVo;A1Vhi;A2A2S38SfA1M0S37Lx;S2aVo;A1S39SfG0S3fLl;Lc;X38x2A2S20S37Lx;S2bVo;A1S39S3fS3fS2eS3fLl;M1G1S2dS0S38S3aS2dS2dA2A1S38S2cA1S3fLtmpl;Lflds;Lcnt;Lesz;X20x6A2").
Lemma ob_shapeb_sound : ltac2:(tb__ "0|0|
S1S0S0S0S30S37S93R4R3R2R1A4S39A3S30S1R5S17R4R3R2S3bSfA1S1aA5A3F_;Fhi;Flo;Fb;Fo;").
Proof.
  intros [ob ol oh oc od] b lo hi H. unfold ob_shapeb in H. cbn in H.
  apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3. subst.
  destruct oc; [|discriminate]. destruct od; try discriminate. reflexivity.
Qed.
Definition d6_okb (d : list (sv * sv)) : bool := ltac2:(tb__ "0|3|
S38S3aS0S0A2M0A1M1S37Ld;Vd;S3fG0G1G0S37Lp;R2S0S0G1S37Ll;R3S45S3dScR2Sb9A2ScR1S4SdaA1M2A2A2S3dScR2G2A2ScR1Sb9A2A2A2G0G1S3fLl0;Lp0;X38x2Lb;La;X3ax1Ll;Lp;X38x2").
Lemma d6_okb_sound : ltac2:(tb__ "0|4|
S38S3aS0S0A2M0A1M1S30S37S98R1A1S39A3S33S30G1R2S41G0S42S0S0Sb9S4SdaA1M2A4S3bG0A1M3A3A3S30G1R2S41G0S42S0S0G2Sb9A4G3A3A3A2F_;Fd;").
Proof.
  intros [|[a b] [|]] H; try discriminate. cbn in H. apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2];
  apply sv_eqb_sound in H1; apply sv_eqb_sound in H2; subst; auto.
Qed.

Definition ex_S5c (E : axst) (S5 : sstate) : sstate := ltac2:(tb__ "0|0|
S11S14VS5;A1S15VS5;A1S13VS5;A1S12VS5;A1S16VS5;A1S43S1S8VS5;A1SadSdbS1SdcSc1A4A3S6VS5;A1S5VS5;A1SeVS5;A1A9").
Definition ex_S6 (S5c : sstate) : sstate := ltac2:(tb__ "0|1|
S11S14VS5c;A1S69S15VS5c;A1S41S3aS3eS0A2M0S42S3eS0U4S4SdaA1A4S3bG0A1A3A2S13VS5c;A1S12VS5c;A1S16VS5c;A1S8VS5c;A1S6VS5c;A1S5VS5c;A1SeVS5c;A1A9").

Definition ex_pipe (ndX : ndesc) (E : axst) (n c : Z) : option (list sobj) := ltac2:(tb__ "0|1f|
S4bVE;A1S7S8R1A1S38S1A1M0SbdR1Sc3S4S65SbfA1A1M1A3S3eSbdR2SbbS4N80A1A3S3eS3cS1A1S3cG0A1M2Lx;S76S1R3R2A3S1S37G2L_;M3S93R1Sc3G1S4Z0M4A1M5A4SfbR5R3Sc7A3S7G3Sf5R6R1A2SbdR5G5S4S87A1A3S3eSd2R2R1S5fS87Z8cA2M6Z4M7S64S61Z2Z20A2Z1A2M8A5S7Sd2R1R2S5fS87Z10A2M9Z8MaG4A5S7Sd2R1R3S5fS87GaA2MbGaG4A5S7Sd2R1R4S5fS87Z38A2McGaG4A5S7Sd2R1R5S5fS87Z28A2MdGaG4A5S7G3S3dS3dS3dS3dSd3S4aR7R6G6G7G8A6Sd3S4aR5R6G9GaG4A6A2Sd3S4aR4R6GbGaG4A6A2Sd3S4aR3R6GcGaG4A6A2Sd3S4aR2R6GdGaG4A6A2S11cS3eS38S3eA1MeS11eS3eA1S3eS11bS49S73S3eS122R1A1S41S3eRbS41S3eRaS3bS3eA1A3A3MfA3A1M10A1Li;S3eS11dG10A1Lx;SafU0M11S48S1RbA2A2A6GeS43S3eGfR1A3GeG3SfaS48S1S8R3A1M12A2R1A2S3cS7A1G2Lx;M13Sf8Sf1R3Sf7G12R1A2A2G11A2S7G13Sf9R1G11S4N430A1A3S7S9dVE;R1A2S7S9eR1A1S7S51R1S3bS3aS0S0A2M14A1M15S4fVE;A1M16A3S4cG3S3dS3dS3dS3dS3dS3dS3dS3dS3dSa6S5R4A1S5R13A1M17A2S21R3A1A2SdeS6R4A1S8R4A1G15ScaScbS79VndX;A1Sc1A7A2S21R2A1A2S3cS3aS38G14A1M18S38S2A1M19A2M1aA1S37Lx;Sf6R3R2A2G1aG1aS37Lp;R1G18G19G19S37Ll;R1S98R2A1S2G19S3fLl0;Ls;X38x2Ll;Ld6;X3ax1Lp;S3fX3cx2A2S73S2S9S22Sb9S4SdaA1A2A1S6R13A1M1bA3A2S8cG1bA1A2Sa5S68G17A2A2S78G17VndX;A2A2ScG16S4S119A1A2A2G2G2Lx;Se3R1S89Vn;Vc;A2M1cSc2R1Vn;Vc;A3A3G0G3S3dSe4R2G1cSc2R2Vn;Vc;A3R1S3bS4cA1A5S75S2S19S5S4bR2A1M1dA1A1S6G1dA1A3A2S40G0R1A2S46G0A1M1eX37x2LR;G1eX3cx2G1eX37x2TC;TS6;TS5c;LS5;G1eX3cx2LS4;G1eX3cx2G1eX37x2Tidxs;Trest;G1eX37x2TS1;TS0d;TS0c;TS0b;TS0a;Tie;G1eX37x2TS0;G1eX37x2Lo;G1eX3cx2Tim;Tiw;Tobjs;TS;").

Lemma X_exit_pipe : ltac2:(tb__ "0|4|
S77S2dS2dS4cS38S1A1M0S30S3cG0A1S99R5R2R4R3A4S40G0R1A2A3S74S3aS2dS2dA2S42S2dS2dR5R4A4Sb4A3S38S56A1M1S57VKc;R2R1A2M2VSpec;S43S56R3S43S56SadS6aQ8A1S56S5bSb3A1S88R9A1A4S41S56S59S6cQ40M3R8A2S5eR2A1A2S3bS56A1A3A3A3A1F_;Fmd;Ftr;G1S57G2S30S3cS58A1S5cS5dR2A1Sb3A2S40S58S5aSb3A1A2A3F_;Fmd;Ftr;S3S38S6aG3A1A1Sa0S4aVok;S6dS4aVJK;RbA1R8R2R1A5Sa1S32L_;A4Ftp;Frho;F_;F_;F_;F_;FR;FE;Fc;Fn;FndX;").
Proof.
  intros ndX n c E R Hp Hsupp HSPEC HKfd1 rho tp. unfold ex_pipe in Hp. cbv zeta in Hp.
  destruct (nth_error (ss_objs (ax_S E)) (locate (ss_objs (ax_S E)) spM (SLit (- DEEP)))) as [o|] eqn:E1; [|discriminate].
  destruct (ob_shapeb o spM (SLit (- DEEP)) (SLit 0)) eqn:E2; [|discriminate]. apply ob_shapeb_sound in E2. subst o.
  destruct (same_but_objs _ _) eqn:E3; [|discriminate].
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:EI; [|discriminate] end.
  apply andb_prop in EI as [EI I5]. apply andb_prop in EI as [EI I4]. apply andb_prop in EI as [EI I3]. apply andb_prop in EI as [I1 I2].
  destruct (select_ok _ _) eqn:E4; [|discriminate].
  destruct (merge_objs_at _ 0) as [S4|] eqn:E5; [|discriminate].
  destruct (split_obj_at S4 0 (SLit (-1072))) as [S5|] eqn:E6; [|discriminate].
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:E7; [|discriminate] end.
  destruct (entails_frA _ _ _) as [R'|] eqn:E8; [|discriminate].
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:E9; [|discriminate] end. injection Hp as HR. subst R'.
  apply andb_prop in E9 as [E9 E10].
  apply andb_prop in E7 as [E7 E7j]. apply andb_prop in E7 as [E7 E7i]. apply andb_prop in E7 as [E7 E7h]. apply andb_prop in E7 as [E7 E7g].
  apply andb_prop in E7 as [E7 E7f]. apply andb_prop in E7 as [E7 E7e]. apply andb_prop in E7 as [E7 E7d]. apply andb_prop in E7 as [E7 E7c].
  apply andb_prop in E7 as [E7a E7b].
  destruct (state_diff (ex_S5c E S5) (ex_S6 (ex_S5c E S5))) as [[d6 [|]]|] eqn:E11; try discriminate.
  apply Pos.eqb_eq in E7a. apply sv_eqb_sound in E7j.
  eapply (X_exit ndX n c E _ S4 S5 (ex_S6 (ex_S5c E S5)) _ R E7h E7i E7j _ E1 _ eq_refl E3 _ (conj I1 (conj I2 (conj I3 (conj I4 I5)))) eq_refl
            E4 E5 E6 E7a E7b E7c eq_refl E7d d6 E11 (d6_okb_sound d6 E7e) E7f E8 E9 E10 Hsupp HSPEC HKfd1 E7g).
Qed.

Section FreeCall.
Variables tb tl : sv.
Let t : sv * sv := ltac2:(tb__ "0|0|
S42S0S0Vtb;Vtl;A4").
Variable kept : list (sv * sv).
Variables bdJ bdX : list bitem.
Definition ndJ : ndesc := ltac2:(tb__ "0|0|
S7bS41S3aS0S0A2Vt;Vkept;A3S3bS3aS3aS0S2dA2S0A2A1VbdJ;S7aA4").
Definition ndX : ndesc := ltac2:(tb__ "0|0|
S7bVkept;S3bS3aS3aS0S2dA2S0A2A1VbdX;S7aA4").
Variables (CF : axst) (s : wsub) (R : list sobj) (T : axst).
Hypothesis Hfr : ltac2:(tb__ "0|1|
S30S3cS38S1A1M0A1Se3VCF;Sb6Vs;A3S40G0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S30S37Se5VCF;Sb6Vs;VR;S41S4cSbaS3bS4cA1A3A5S39A3").
Hypothesis HcT : ltac2:(tb__ "0|0|
S30S37S111S68Vs;A2S39A3").
Hypothesis Hnx : ltac2:(tb__ "0|0|
S30S37Sa5S68S5S4bVCF;A1A1A2S39A3").
Hypothesis Hnb : ltac2:(tb__ "0|1|
S31S30S37S78S5S4bVCF;A1A1M0S11fA2S39A3S30S37SfeG0VbdX;A2S39A3A2").
Hypothesis Hs12 : ltac2:(tb__ "0|0|
S31S30S0SecVs;PcA2Vtb;A3S30S0SecVs;PdA2Vtl;A3A2").
Hypothesis Hpay : ltac2:(tb__ "0|0|
S30S37SffS6S4bVCF;A1A1S4Z0A1SfdVbdJ;VbdX;A5S39A3").
Hypothesis Hspf : ltac2:(tb__ "0|0|
S30S37S8cS6S4bVCF;A1A1A1S39A3").
Hypothesis Hro : ltac2:(tb__ "0|0|
S30S37S91S6S4bVCF;A1A1S41S3aS0S0A2Vt;Vkept;A3S40S3eU0A2VR;A4S39A3").
Hypothesis Hxr : ltac2:(tb__ "0|1|
S30S37S8fS6S4bVCF;A1M0A1S41S3aS0S0A2Vt;Vkept;A3S40S3eU0A2S8G0A1S8eS4eVCF;A1A6S39A3").
Hypothesis Hnz : ltac2:(tb__ "0|0|
S30S37S73S2S9SaS4Z1000A1Vtb;A2A1S6S4bVCF;A1A1A3S39A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S30S4cS110Sb6VCF;Vs;VR;SbaA5VT;A3").
Hypothesis HT' : ltac2:(tb__ "0|0|
S3S38S6aQ40A1A1Sa0S4aVok;S6dS4aVJK;S120A1VT;R2R1A5Sa1S32L_;A4Ftp';Frho';").

Lemma X_free_call : ltac2:(tb__ "0|0|
S3S38S6aQ40A1A1Sa0S4aVok;S6dS4aVJK;S11fA1VCF;R2R1A5Sa1S32L_;A4Ftp;Frho;").
Proof.
  intros rho tp. destruct Hnb as [Hnb1 Hnb2]. destruct Hs12 as [Hs12a Hs13].
  apply triple_factsA. intros HF.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned (eval rho sp0) <= 2 ^ 47 - 224).
  { unfold sp0. cbn [eval]. eapply (fun r f HF' Hb => proj1 (sp0_facts_sound r f HF' Hb)); [exact HF | exact Hspf]. }
  assert (Htnz : tnz rho t).
  { unfold tnz, t. cbn [fst]. pose proof (holds_mem _ _ _ HF Hnz) as X. cbn [holds] in X. rewrite U_lit in X. rewrite <- M64v_eq in X.
    rewrite Z.mod_small in X by lia. unfold uval in X |- *. lia. }
  apply (free_callA segs AE_A AInv CST XGL ALA HCST HXGL NF Kc rho0 P0f [] [] BX0 PA HKc ok [] UStopLe CF s R rho tp
           ndJ 0%nat t bdX (fun _ => False) free_shape_nil okKK AC Hfr Hcc HcT Hnx Hnb1 Hnb2 eq_refl).
  - apply payA_of_bud_pay. exact Hpay.
  - exact HPAf.
  -
    apply (site_ok_drv ndJ CF s R rho (Some 0%nat) (Some (uval rho (wsub_get s 12%positive)))); try assumption.
    + intros Ai HF' HN HZ. exists t. split; [reflexivity|]. rewrite Hs12a. split; [exact Htnz | reflexivity].
    + intros Ai ms HF' HP0 Hav HN HD HZ HM. split; [|split; [| exact I]].
      * exact Htnz.
      * rewrite Hs12a, Hs13. reflexivity.
  -
    intros rho' tp'. unfold PreF, PostF in HT. rewrite HT. cbn [nd_tv nd_fr nd_am ndJ remove_nth]. fold ndX. apply HT'.
Qed.
End FreeCall.

Section FbChain.
Variable A0 : axst.
Variable bdJ bdX : list bitem.
Let ndJ' : ndesc := ltac2:(tb__ "0|1|
S7bS41S3aS0S0A2M0S42S0S0Sb5Sb7A4S3bG0A1A3S3bS3aS3aS0S2dA2S0A2A1VbdJ;S7aA4").
Let ndX' : ndesc := ltac2:(tb__ "0|0|
S7bS3bS3aS0S0A2A1S3bS3aS3aS0S2dA2S0A2A1VbdX;S7aA4").
Variables (E : axst) (S2 S4 : sstate) (idxs : list nat) (R : list sobj) (T Ex : axst).
Variable iw : nat.

Hypothesis HJwf : ltac2:(tb__ "0|2|
S31S30S37Sa5S68S5S4bVA0;A1M0A1M1A2S39A3S31S30S37SeG0A1S3fA3S30S37S78G1VndJ';A2S39A3A2A2").
Hypothesis Hrun1 : ltac2:(tb__ "0|1|
S30S3cS38S4dA1M0A1S50S4aSc0SbeVA0;S39A5S40G0S41S4dS53VE;Sf2A2S3bS4dA1A3A2A3").

Hypothesis H1n : ltac2:(tb__ "0|0|
S30S3cS1A1S76S1S8S4bVE;A1A1Viw;A3S40S1S17Sc4S4S65S64SbfZ50A2A1A1S4Z0A1S3bSfA1S1aA5A2A3").
Hypothesis H1e : ltac2:(tb__ "0|0|
S30S7SfbS4bVE;A1Viw;Sc6A3VS2;A3").
Hypothesis H1s : ltac2:(tb__ "0|0|
S30S37Sf5S4bVE;A1VS2;A2S39A3").
Hypothesis H2 : ltac2:(tb__ "0|0|
S30S37SfaS48S1S8VS2;A1A2Vidxs;A2S39A3").
Hypothesis H3 : ltac2:(tb__ "0|0|
S30S3cS7A1Sf8Sf1VS2;Sf7S8VS2;A1Vidxs;A2A2U0A2S40S7VS4;A2A3").
Definition CF : axst := ltac2:(tb__ "0|0|
Sc8S42S0S0Sb5Sb7A4S51VS4;S4eVE;A1S4fVE;A1A3A2").
Hypothesis H4n : ltac2:(tb__ "0|0|
S30S2eS5VS4;A1S5S4bVE;A1A1A3").

Hypothesis Hfr : ltac2:(tb__ "0|1|
S30S3cS38S1A1M0A1Se3Sa4Sb6Sb8Sa4A1A3S40G0VR;A2A3").
Hypothesis Hcc : ltac2:(tb__ "0|0|
S30S37Se5Sa4Sb6Sb8Sa4A1VR;S41S4cSbaS3bS4cA1A3A5S39A3").
Hypothesis HcT : ltac2:(tb__ "0|0|
S30S37S111S68Sb8Sa4A1A2S39A3").
Hypothesis Hnx : ltac2:(tb__ "0|0|
S30S37Sa5S68S5S4bVE;A1A1A2S39A3").
Hypothesis Hnb : ltac2:(tb__ "0|1|
S31S30S37S78S5S4bVE;A1A1M0VndJ';A2S39A3S30S37SfeG0VbdX;A2S39A3A2").
Hypothesis Hs12 : ltac2:(tb__ "0|1|
S31S30S0SecSb8Sa4A1M0PcA2Sb5A3S30S0SecG0PdA2Sb7A3A2").
Hypothesis Hpay : ltac2:(tb__ "0|0|
S30S37SffS6S4bSa4A1A1S4Z0A1SfdVbdJ;VbdX;A5S39A3").
Hypothesis HspfE : ltac2:(tb__ "0|0|
S30S37S8cS6S4bVE;A1A1A1S39A3").
Hypothesis Hspf : ltac2:(tb__ "0|0|
S30S37S8cS6S4bSa4A1A1A1S39A3").
Hypothesis Hro : ltac2:(tb__ "0|1|
S30S37S91S6S4bSa4A1A1S41S3aS0S0A2M0S42S0S0Sb5Sb7A4S3bG0A1A3S40S3eU0A2VR;A4S39A3").
Hypothesis Hxr : ltac2:(tb__ "0|2|
S30S37S8fS6S4bSa4A1M0A1S41S3aS0S0A2M1S42S0S0Sb5Sb7A4S3bG1A1A3S40S3eU0A2S8G0A1S8eS4eSa4A1A6S39A3").
Hypothesis HvB : ltac2:(tb__ "0|0|
S30S37S73S2S9SaS4Z1000A1Sb5A2A1S6S4bSa4A1A1A3S39A3").
Hypothesis HT : ltac2:(tb__ "0|0|
S30S4cS110Sb6Sa4Sb8Sa4A1VR;SbaA5VT;A3").

Hypothesis HTwf : ltac2:(tb__ "0|2|
S31S30S37Sa5S68S5S4bVT;A1M0A1M1A2S39A3S31S30S37SeG0A1S3fA3S30S37S78G1VndX';A2S39A3A2A2").
Hypothesis Hrun2 : ltac2:(tb__ "0|1|
S30S3cS38S4dA1M0A1S50S4aSc0SbeVT;S39A5S40G0S41S4dS53VEx;Sf2A2S3bS4dA1A3A2A3").
Hypothesis HX : ltac2:(tb__ "0|0|
S3S38S6aQ40A1A1Sa0S4aVok;S6dS4aVJK;VndX';A1VEx;R2R1A5Sa1S32L_;A4Ftp;Frho;").

Lemma X_fb : ltac2:(tb__ "0|0|
S3S38S6aQ40A1A1Sa0S4aVok;S6dS4aVJK;VndJ';A1VA0;R2R1A5Sa1S32L_;A4Ftp;Frho;").
Proof.
  intros rho tp. destruct HJwf as (W1 & W2 & W3). destruct Hnb as [Hnb1 Hnb2]. destruct HTwf as (V1 & V2 & V3).
  eapply JK_run; [exact Hrun1 | exact W2 | exact W1 | exact W3 |].
  intros L rho1 [<-|[]] Hag1. cbn [la_state].
  apply triple_factsA. intros HF.
  assert (Hsp : 0x7fff80000000 <= bv_unsigned (eval rho1 sp0) <= 2 ^ 47 - 224).
  { unfold sp0. cbn [eval]. eapply (fun r f HF' Hb => proj1 (sp0_facts_sound r f HF' Hb)); [exact HF | exact HspfE]. }
  eapply (triple_conseq (P := SPA segs (JK ndJ') CF rho1 tp)); [intros w HS | intros w' Hw'; exact Hw' |].
  { assert (HS1 : SPA segs (JK ndJ') (ax_setS E S2) rho1 tp w).
    { rewrite <- H1e. apply (SPA_reslice segs (JK ndJ') rho1 E iw _ O_deepM tp w H1n); try reflexivity.
      - rewrite H1e. exact H1s.
      - unfold O_deepM, spT. rewrite !obj_range_lits by (unfold DEEP; lia). rewrite U_add_lit by lia. unfold DEEP. f_equal; lia.
      - unfold O_deepM, obj_lo_of, obj_hi_of. cbn [ob_lo ob_hi]. rewrite !soff_lit_small by (unfold DEEP; lia). unfold DEEP; lia.
      - exact HS. }
    pose proof (AxXform.SPA_select segs (JK ndJ') rho1 (mkAX S2 (ax_X E) (ax_base E)) idxs tp w H2 HS1) as HS2.
    pose proof (SPA_merge segs (JK ndJ') rho1 (mkAX (set_objs S2 (select (ss_objs S2) idxs)) (ax_X E) (ax_base E)) 0 S4 tp w H3 HS2) as HS3.
    unfold CF, dropX. apply SPA_x_sub; [|exact HS3]. cbn [ax_X]. apply In_dropX. }
  assert (HnxC : ss_next (ax_S CF) = ss_next (ax_S E)) by (unfold CF, dropX; cbn [ax_S ax_setX]; exact H4n).
  apply (X_free_call vB vCap [] bdJ bdX CF (s_fb CF) R T Hfr Hcc HcT); try assumption.
  - rewrite HnxC. exact Hnx.
  - rewrite HnxC. split; [exact Hnb1 | exact Hnb2].
  -
    intros rho' tp'. eapply JK_run; [exact Hrun2 | exact V2 | exact V1 | exact V3 |].
    intros L rho3 [<-|[]] Hag3. cbn [la_state]. apply HX.
Qed.
End FbChain.

Definition one_leaf (r : option (list leafA)) : option axst := ltac2:(tb__ "0|3|
S3cS38S4dA1M0A1S3cS4cA1M1Lr;Vr;G0G0G1Ll;R1S46S4cA1M2S4dG0S4dG1Ll0;R2S4cSf3Sf3G1Lla_reason;R1G2G0G1Ll1;R3S40S4cR2A2S4dG0G2Ll3;Ll2;X38x2G2G2G2G2G2Xf3x7Lla_reason;LE;X4dx1Ll1;Ll0;X38x2Ll;G2X3cx2").
Lemma one_leaf_sound : ltac2:(tb__ "0|2|
S3cS38S4dA1M0A1M1S4cS30S3cS4cA1S94R2A1S40S4cR1A2A3S30G1R3S40G0S41S4dS53R2Sf2A2S3bS4dA1A3A2A3F_;FE;Fr;").
Proof. intros r E H. unfold one_leaf in H. destruct r as [[|[E' [| | | | | |]] [|]]|]; try discriminate. injection H as <-. reflexivity. Qed.

Definition fb_pipe (bdJ bdX : list bitem) (A0 : axst) : option axst := ltac2:(tb__ "0|18|
VA0;S4cS7bS41S3aS0S0A2M0S42S0S0Sb5Sb7A4M1S3bG0A1M2A3M3S3bS3aS3aS0S2dA2S0A2A1M4VbdJ;S7aA4S77S7bG2G4VbdX;S7aA4S77S37S3cS4cA1M5L_;M6S3dS3dSa5S68S5S4bR3A1M7A1M8A2S49SeG7A1A1A2S78G8R2A2A2G5G5Lx;S94S50S4aSc0SbeR3S39A5A1S4cS4bR1A1M9S7S8R1A1S38S1A1MaSbdR1Sc4S4S65S64SbfZ50A2A1A1MbA3S3eSbdR2SbbS4Nd0A1A3S3eS3cS1A1G5Lx;S76S1R3R2A3S1G6S93R1Sc4GbS4Z0A1McA4SfbR5R3Sc6A3S7G6Sf5R6R1A2S11cS3eS38S3eA1MdS11eS3eA1S3eS11bS49S73S3eS122R1A1S41S3eR5S41S3eR4S3bS3eA1A3A3MeA3A1MfA1Li;S3eS11dGfA1Lx;SafU0M10S48S1R5A2A2A6GdS43S3eGeR1A3GdG6SfaS48S1S8R3A1M11A2R1A2S3cS7A1G5Lx;Sf8Sf1R3Sf7G11R1A2A2G10A2S7Sc8G1S51R1S4eRaA1S4fRaA1A3A2S4cS3cGaA1G5Lx;Se3R1Sb6Sb8R1A1A3GaS110Sb6R2Sb8R2A1R1SbaA5S4cG6S3dS3dS3dS3dS3dS3dS3dS3dS3dS3dS3dS3dS3dS3dS3dS3dSa6S5R4A1S5RcA1M12A2Se5R3Sb6Sb8R3A1M13R2S41S4cSbaS3bS4cA1A3A5A2S111S68G13A2A2Sa5S68G12A2A2S78G12RfA2A2SfeG12VbdX;A2A2ScSecG13PcA2Sb5A2A2ScSecG13PdA2Sb7A2A2SffS6G7A1M14GcSfdVbdJ;VbdX;A5A2S8cS6RcA1A1A2S8cG14A1A2S91G14G3S40S3eG10A2M15R2A4A2S8fG14G3G15S8G7A1S8eS4eR3A1A6A2S73S2S9SaS4Z1000A1Sb5A2A1G14A3A2Sa5S68S5G9A1M16A2A2S49SeG9A1A1A2S78G16ReA2A2S94S50S4aSc0SbeR1S39A5A1S46S4cA1M17X37x2TT;LR;G17X3cx2TC;LS4;G17X3cx2G17X37x2Tidxs;Trest;G17X37x2TS2;G17X37x2Lo;G17X3cx2Tit;Tiw;Tobjs;TS;LE;G17X3cx2G17X37x2TndX;TndJ;TJ;").

Lemma negb_true : ltac2:(tb__ "0|0|
S37S30S37S49R1A1S39A3S30S37R2S3fA3F_;Fb;"). Proof. intros [|]; [discriminate | reflexivity]. Qed.

Lemma X_fb_pipe : ltac2:(tb__ "0|6|
S38S100A1M0G0S4cS4cS30S3cS4cA1S9aR4R3R2A3S40S4cR1A2A3S3S38S6aQ40A1A1M1Sa0S4aVok;S6dS4aVJK;S7bS3bS3aS0S0A2M2A1M3S3bS3aS3aS0S2dA2S0A2A1M4R6S7aA4A1R4R2R1A5Sa1S32L_;M5A4Ftp;Frho;S3G1Sa0S4aVok;S6dS4aVJK;S7bS41G2S42S0S0Sb5Sb7A4G3A3G4R8S7aA4A1R6R2R1A5G5A4Ftp;Frho;F_;F_;FEx;FA0;FbdX;FbdJ;").
Proof.
  intros bdJ bdX A0 Ex Hp HX rho tp. unfold fb_pipe in Hp. cbv zeta in Hp.
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:E0; [|discriminate] end.
  apply andb_prop in E0 as [E0 E0c]. apply andb_prop in E0 as [E0a E0b]. apply negb_true in E0b.
  destruct (one_leaf (sym_runA segs FUEL_X CUTS_X A0 true)) as [E|] eqn:E1; [|discriminate]. apply one_leaf_sound in E1.
  destruct (nth_error (ss_objs (ax_S E)) _) as [o|] eqn:E2; [|discriminate].
  destruct (ob_shapeb o _ _ _) eqn:E3; [|discriminate]. apply ob_shapeb_sound in E3. subst o.
  destruct (same_but_objs _ _) eqn:E4; [|discriminate].
  destruct (select_ok _ _) eqn:E5; [|discriminate].
  destruct (merge_objs_at _ 0) as [S4|] eqn:E6; [|discriminate].
  destruct (entails_frA _ PreF _) as [R|] eqn:E7; [|discriminate].
  match type of Hp with (if ?b then _ else _) = _ => destruct b eqn:E8; [|discriminate] end.
  apply one_leaf_sound in Hp.
  apply andb_prop in E8 as [E8 Q3]. apply andb_prop in E8 as [E8 Q2]. apply andb_prop in E8 as [E8 Q1]. apply negb_true in Q2.
  apply andb_prop in E8 as [E8 P14]. apply andb_prop in E8 as [E8 P13]. apply andb_prop in E8 as [E8 P12].
  apply andb_prop in E8 as [E8 P11]. apply andb_prop in E8 as [E8 P10]. apply andb_prop in E8 as [E8 P9].
  apply andb_prop in E8 as [E8 P8]. apply andb_prop in E8 as [E8 P7]. apply andb_prop in E8 as [E8 P6].
  apply andb_prop in E8 as [E8 P5]. apply andb_prop in E8 as [E8 P4]. apply andb_prop in E8 as [E8 P3]. apply andb_prop in E8 as [P1 P2].
  apply Pos.eqb_eq in P1. apply sv_eqb_sound in P7. apply sv_eqb_sound in P8.
  eapply (X_fb A0 bdJ bdX E _ S4 _ R _ Ex _ (conj E0a (conj E0b E0c)) E1 E2 eq_refl E4 E5 E6 P1 E7 P2 P3 P4 (conj P5 P6) (conj P7 P8)
            P9 P10 P11 P12 P13 P14 eq_refl (conj Q1 (conj Q2 Q3)) Hp HX).
Qed.

Lemma X_join : ltac2:(tb__ "0|8|
S38S100A1M0G0S4cS2dS2dS4cS38S1A1M1S30S3cS4cA1S9aR7R6R5A3S40S4cR2A2A3S30S3cG1A1S99S7bS3bS3aS0S0A2M2A1M3S3bS3aS3aS0S2dA2S0A2A1M4R7S7aA4R3R5R4A4S40G1R2A2A3S74S3aS2dS2dA2S42S2dS2dR6R5A4Sb4A3S38S56A1M5S57VKc;R2R1A2M6VSpec;S43S56R3S43S56SadS6aQ8A1S56S5bSb3A1S88RaA1A4S41S56S59S6cQ40M7R9A2S5eR2A1A2S3bS56A1A3A3A3A1F_;Fmd;Ftr;G5S57G6S30S3cS58A1S5cS5dR2A1Sb3A2S40S58S5aSb3A1A2A3F_;Fmd;Ftr;S3S38S6aG7A1A1Sa0S4aVok;S6dS4aVJK;S7bS41G2S42S0S0Sb5Sb7A4G3A3G4ReS7aA4A1RcR2R1A5Sa1S32L_;A4Ftp;Frho;F_;F_;F_;F_;F_;FR;FEx;Fc;Fn;FA0;FbdX;FbdJ;").
Proof.
  intros bdJ bdX A0 n c Ex R Hfb Hex Hsupp HSPEC HKfd1.
  apply (X_fb_pipe bdJ bdX A0 Ex Hfb). apply (X_exit_pipe (NDA [] [] bdX ANone) n c Ex R Hex Hsupp HSPEC HKfd1).
Qed.

End SITE.
End DrvSite.

