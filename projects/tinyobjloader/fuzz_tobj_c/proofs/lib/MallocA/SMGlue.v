(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Datatypes"; "pair"; "cons"; "prod"; "nat"; "list"; "nil"; "bool"; "true"; "app"; "false"; "option"; "None"; "fst"; "snd"; "Some"; "andb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "valuation"; "rw"; "SLit"; "sprop"; "rm"; "SVar"; "eval"; "mkSS"; "ss_objs"; "FcsrFrm0"; "ss_facts"; "sprop_below"; "sstate"; "swf"; "SAlu"; "agree_below"; "mkObj"; "obj_range"; "smatch"; "SPUle"; "cell"; "enc_bytes"; "odefault"; "holds"; "mkVal"; "ranges_disjoint"; "rl"; "rom_ok"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "iff"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "sub"; "of_nat"; "pow"; "div"; "modulo"; "to_nat"; "mul"; "land"; "leb"; "ltb"; "opp"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "ag_fsb"; "ag_ctx"; "ag_dtls"; "ag_stack_bottom"; "ag_stack_top"; "ag_thread"; "ageom"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "NW"; "GW"; "win_hyp"; "gsv"; "shb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "Cgen"; "F_K"; "NIT"; "NWF"; "flagaddr"; "vT"; "RT_objs"; "TP_A"; "ffx"; "vCTX"; "vFSB"; "vHINT"; "X0"; "ret_regs"; "Cbusy"; "Ebusy0"; "F_found"; "F_geom"; "O_own"; "vDTLS"; "zero_cells"; "Cfree"; "Ebusy"; "FLOFF"; "MASK"; "O_flagc"; "O_flagw"; "O_frame"; "O_fshadow"; "P0"; "POS"; "RT_fixed"; "vBOT"; "vGF"; "vH"; "vK"; "vTOP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "entailsA"; "axst"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "stableA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "KcA"; "AE_A"; "V_DEPTH"; "ae_ret_stack_malloc"; "A_globals"; "Kc_ok"; "F_sp_high"; "Pre_stack_mallocI"; "ae_stack_malloc"; "pre_facts"; "stack_malloc_depth"; "stack_win"; "J_stack_malloc_preT"; "L_stack_malloc"; "O_got"; "O_rtc"; "base_sv"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SMGlue.SM"; "posof"; "JC"; "RVi"; "N_fixed"; "hint_of"; "s_0"; "s_b"; "RV0"; "facts_E"; "kept_sm"; "rho1_of"; "spec_range"; "JE"; "coverb"; "sa"; "spec_covered"; "spec_small"; "st6"; "zseq"; "Cfree0"; "N_free"; "N_rt"; "R_sm"; "hexp"; "img_zone_okb"; "rhoF_of"; "sb"; "st4"; "st5"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "NF"; "setregs"; "pre_regs"; "cut_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "fs_frame_size"; "FS_total"; "fs_frame"; "FS_LOG"; "K_HIGH_MEM_END"; "PG"; "forall_rangeZ"; "fs_flags_off_nat"; "fs_num_iter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "geom_ok"; "busyb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world";
"@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "rho_sub"; "wsub_id_below"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "withGA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "cells_in_view"; "rd_of"; "carved"; "cells_inside"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@Corelib.Init.Peano"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM"; "rt_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "G0"; "RTC_A"; "cells_footb"; "rtc_cells_img"; "view"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Iface Inv GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.RebuildSM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section SM.
Let segs : list Segment := segsA.
Variables CST XGL : list (Z * Z).
Hypothesis HCST : cst_ok CST.
Hypothesis HXGL : xgl_ok XGL.
Let AInv : AA -> valuation -> list word -> Model -> Prop := AInvA segs.
Let J (c : Z) (A : AA) (Kc : KcA) : jpredA := ltac2:(tb__ "0|0|
S98VAInv;Vc;VA;VKc;A4").
Variable hi : bool.

Definition hint_of (A : AA) (c : Z) : Z := nthZ (aa_fs_hint A) c 0.
Definition rho1_of (A : AA) (c : Z) (rho : valuation) : valuation := ltac2:(tb__ "0|3|
S4fVA;A1S56S5fVrho;S4S5S1S4bQ40M0A1M1A2M2S3S1G1P97S4aG0S55R1A1A2A4S4G2S3S1G1P98S4aG0S51R1A1A2A4S4G2S3S1G1P99S4aG0S54R1A1A2A4S4G2S3S1G1P9aS4aG0S53R1A1A2A4S4G2S3S1G1P9bS4aG0S50R1A1A2A4S4G2S3S1G1P9cS4aG0S52R1A1A2A4S4G2S3S1G1P9dS4aG0Sa2VA;Vc;A2A2A4S8G2A1A3A3A3A3A3A3A3A2TG;").

Lemma rho1_agree : ltac2:(tb__ "0|0|
S4eS0S15S24Sc1R1Sa8R3R2R1A3A3Frho;Fc;FA;").
Proof.
  intros. apply agree_below_rho_sets. intros j v Hin. cbn in Hin. unfold NF.
  repeat (destruct Hin as [E|Hin]; [injection E; intros; subst; cbv; discriminate|]). destruct Hin.
Qed.

Lemma J_rm_only : ltac2:(tb__ "0|4|
S0S4eS8cS15S15S7S4bQ40A1M0A1S7SbeA1SbfS38G0SdS4bQ8A1A1F_;S19R4A1S19R5A1A3S38G0S16R5PcM1A2S16R6G1A2A3S38G0S16R6P18M2A2S16R7G2A2A3S38G0S16R7PaM3A2S16R8G3A2A3S38G0S16R8S8eA2S16R9S8eA2A3VJ;RdRcRbRaR8R7R6A7VJ;ReRdRcRaR9R8R7A7F_;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;FKc;FA;Fc;").
Proof.
  intros c A Kc rho rho' tp tr md Hrm H12 H24 H10 H15 (HA & HK & Htp & Hn & Hsz & Htop).
  unfold J, J_stack_malloc_preT, tp_ok, top_high. rewrite H12, H24, H10, H15. split; [|repeat split; auto].
  unfold AInv, AInvA in *. rewrite Hrm. exact HA.
Qed.

Lemma own_lo : ltac2:(tb__ "0|2|
S15S7S29A1S2bS38S0SfS0S0S26R3S25S1aPaM0A1S1aS8eA1S17Z0A1R2R1A5A2A3S3dS4cQ40M1S16R3G0A2A2S4dG1S16R3S8eA2A2A2A3Fd;Fcells;Frho;").
Proof. intros. reflexivity. Qed.

Definition N_rt (c : Z) : list carve_spec := ltac2:(tb__ "0|28|
S4S5S5S5S13S0A2M0S0A2M1S7S5S5S0S6A2M2S13A2M3A1M4A2M5S3G1G4S3G0S0S3S13S0S17Z0M6A1M7Zf20d8M8A4Zf20daA4S4G3S3G2S13S3S0S6G8U1M9A4S17Z1A1MaA4S4G3S3G2S13S3S0S6Zf20d9G9A4GaA4S8G3A1MbA3A3A4S4G5S3G1G4S3G0S0S3S13S0G7Zf20e0McA4Zf20f8A4S4G3S3G2S13S3S0S6GcU8MdA4S17Sc9A1A4S4G3S3G2S13S3S0S6Zf20e8GdA4G7A4S4G3S3G2S13S3S0S6Zf20f0GdA4G7A4GbA3A3A3A4S4G5S3G1G4S3G0S0S3S13S0G7Zf0c5cMeA4Zf0c5dA4S4G3S3G2S13S3S0S6GeG9A4GaA4GbA3A4S4G5S3G1G4S3G0S0S3S13S0G7Zf0c60MfA4Zf0c61A4S4G3S3G2S13S3S0S6GfG9A4GaA4GbA3A4S4G5S3G1G4S3G0S0S3S13S0G7Zf0c64M10A4Zf0c68A4S4G3S3G2S13S3S0S6G10U4M11A4G7A4GbA3A4S4G5S3G1G4S3G0S0S3S13S0G7Ze9a20M12A4Ze9a28A4S4G3S3G2S13S3S0S6G12GdA4S17Zdeb68A1A4GbA3A4S4G5S3G1G4S3G0S0S3S13S0G7Z624560M13A4Z624568A4S4G3S3G2S13S3S0S6G13GdA4S17Z645960M14A1A4GbA3A4S4G5S3G1G4S3G0S0S3S13S0G7Z6245b0M15A4Z6245c0M16A4S4G3S3G2S13S3S0S6G15GdA4S17Z6245d8A1A4S4G3S3G2S13S3S0S6Z6245b8GdA4S6aA4GbA3A3A4S4G5S3G1G4S3G0S0S3S13S0G7G16A4Z6245c8M17A4S4G3S3G2S13S3S0S6G16GdA4S73A4GbA3A4S4G5S3G1G4S3G0S0S3S13S0G7G17A4Z6245ccA4S4G3S3G2S13S3S0S6G17G11A4G7A4GbA3A4S4G5S3G1G4S3G0S0S3S13S0G7Z6245e0M18A4Z6245e8A4S4G3S3G2S13S3S0S6G18GdA4S17Z624db8A1A4GbA3A4S4G5S3G1G4S3G0S0S3S13S0G7G14A4Z645968A4S4G3S3G2S13S3S0S6G14GdA4S69A4GbA3A4S4G5S3G1G4S3G0S0S3S13S0S69Z8M19A4ZcA4S4G3S3G2S13S3S0S6G19G11A4G7A4GbA3A4S4G5S3G1G4S3G0S0S3S13S0S69Z98M1aA4Za0A4S4G3S3G2S13S3S0S6G1aGdA4S65A4GbA3A4S4G5S3G1G4S3G0S0S3S13S0S65G6A4Z18M1bA4S4G3S3G2S13S3S0S6G6GdA4S69A4S4G3S3G2S13S3S0S6G19GdA4S84A4S4G3S3G2S13S3S0S6Z10GdA4S80A4GbA3A3A3A4S4G5S3G1G4S3G0S0S3S13S0S65Z28M1cA4Z29A4S4G3S3G2S13S3S0S6G1cG9A4G7A4GbA3A4S4G5S3G1G4S3G0S0S3S13S0S65Z30M1dA4Z40A4S4G3S3G2S13S3S0S6G1dGdA4S17Z624cf0A1A4S4G3S3G2S13S3S0S6Z38GdA4S17Z624dccA1A4GbA3A3A4S4G5S3G1G4S3G0S0S3S13S0S65Z48M1eA4Z50A4S4G3S3G2S13S3S0S6G1eGdA4S6aA4GbA3A4S4G5S3G1G4S3G0S0S3S13S0S73G1bA4Z20A4S4G3S3G2S13S3S0S6G1bGdA4S17S67A1A4GbA3A4S4G5S3G1G4S3G0S0S3S13S0G7Z182f4aM1fA4Z182f4bA4S4G3S3G2S13S3S0S6G1fG9A4GaA4GbA3A4S4G5S3G1G4S3G0S0S3S13S0G7Z182fa0M20A4Z182fa8A4S4G3S3G2S13S3S0S6G20GdA4S17ZffffffffffffffffA1A4GbA3A4S4G5S3G1G4S3G0S0S3S13S0G7Z182fb1M21A4Z182fb2A4S4G3S3G2S13S3S0S6G21G9A4GaA4GbA3A4S4G5S3G1G4S3G0S0S3S13S0G7Z182fb8M22A4Z182fc0A4S4G3S3G2S13S3S0S6G22GdA4G7A4GbA3A4S4G5S3G1G4S3G0S0S3S13S0G7Z18302cM23A4Z18302dA4S4G3S3G2S13S3S0S6G23G9A4G7A4GbA3A4S4G5S3G1G4S3G0S0S3S13S0G7Z180e98M24A4Z180e9cA4S4G3S3G2S13S3S0S6G24G11A4G7A4GbA3A4S4G5S3G1G4S3G0S0S3S13S0G7Z180ea0M25A4Z180ea8A4S4G3S3G2S13S3S0S6G25GdA4S17ScaA1A4GbA3A4S4G5S3G1G4S3G0S0S3S13S0S6aZ58M26A4Z61A4S4G3S3G2S13S3S0S6G26GdA4S17Sc8A1A4S4G3S3G2S13S3S0S6Z60G9A4G7A4GbA3A3A4S4G5S3G1G4S3G0S0S3S13S0S6aS45G19Vc;A2M27A4S3dG27G19A2A4S4G3S3G2S13S3S0S6G27GdA4S6bA4GbA3A4S8G5A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma N_rt_ok : ltac2:(tb__ "0|0|
S0S38S7S14A1Se0S5dS14S5eSb3R1A1A4S66R1S6bA2A3Fc;").
Proof. intros. reflexivity. Qed.

Definition sa (c : Z) : sstate := ltac2:(tb__ "0|1|
S1cS94S8dVc;A2Sc2Sc3S4S5S6S13A2M0S3S6S13U4S17S67A1A4S8G0A1A3A2Sc0S1eSeS13A1SbS14S4S14S97S8S14A1A3S90A3S95S96A1Sc1ScA9").
Definition sb (c : Z) : sstate := ltac2:(tb__ "0|1|
S1cS94S8dVc;A2Sc2Sc3S4S5S6S13A2M0S3S6S13U4S17S67A1A4S8G0A1A3A2Sc0S1eSeS13A1SbS14SbS14S4S14S97S8S14A1A3S90A3S66Vc;S6bA2A3S95S96A1S58ScA9").

Local Ltac civ_tryF HR E n :=
  eapply (civ_nth _ _ _ n);
  [ exact HR | reflexivity | unfold fs_log_cell, fs_needs_gc_cell; reflexivity | cbn [eval]; E; reflexivity
  | unfold fs_log_cell, fs_needs_gc_cell; lia | unfold fs_log_cell, fs_needs_gc_cell; lia ].
Local Ltac civ_anyF HR E := first [ civ_tryF HR E 43%nat | civ_tryF HR E 44%nat | civ_tryF HR E 45%nat | civ_tryF HR E 46%nat | civ_tryF HR E 47%nat | civ_tryF HR E 48%nat | civ_tryF HR E 49%nat | civ_tryF HR E 50%nat | civ_tryF HR E 51%nat | civ_tryF HR E 52%nat | civ_tryF HR E 53%nat | civ_tryF HR E 54%nat | civ_tryF HR E 0%nat | civ_tryF HR E 1%nat | civ_tryF HR E 2%nat | civ_tryF HR E 3%nat | civ_tryF HR E 4%nat | civ_tryF HR E 5%nat | civ_tryF HR E 6%nat | civ_tryF HR E 7%nat | civ_tryF HR E 8%nat | civ_tryF HR E 9%nat | civ_tryF HR E 10%nat | civ_tryF HR E 11%nat | civ_tryF HR E 12%nat | civ_tryF HR E 13%nat | civ_tryF HR E 14%nat | civ_tryF HR E 15%nat | civ_tryF HR E 16%nat | civ_tryF HR E 17%nat | civ_tryF HR E 18%nat | civ_tryF HR E 19%nat | civ_tryF HR E 20%nat | civ_tryF HR E 21%nat | civ_tryF HR E 22%nat | civ_tryF HR E 23%nat | civ_tryF HR E 24%nat | civ_tryF HR E 25%nat | civ_tryF HR E 26%nat | civ_tryF HR E 27%nat | civ_tryF HR E 28%nat | civ_tryF HR E 29%nat | civ_tryF HR E 30%nat | civ_tryF HR E 31%nat | civ_tryF HR E 32%nat | civ_tryF HR E 33%nat | civ_tryF HR E 34%nat | civ_tryF HR E 35%nat | civ_tryF HR E 36%nat | civ_tryF HR E 37%nat | civ_tryF HR E 38%nat | civ_tryF HR E 39%nat | civ_tryF HR E 40%nat | civ_tryF HR E 41%nat | civ_tryF HR E 42%nat ].

Local Ltac lia_only v := repeat match goal with H : context [v] |- _ => revert H end; clear - v; intros; lia.
Local Ltac wr_cell2F HR n off tacW :=
  eapply (cell_wok_rd2 _ _ _ _ _ (cells_ok_nth _ _ n _ HR eq_refl)); cbn [c_addr c_w Z.of_nat]; unfold fs_log_cell, fs_needs_gc_cell;
  [ lazymatch goal with |- ?x + _ <= ?x + _ < _ => idtac end; lia_only off | lia | tacW | lia ].
Local Ltac wr_any2F HR off tacW := first [ wr_cell2F HR 43%nat off tacW | wr_cell2F HR 44%nat off tacW | wr_cell2F HR 45%nat off tacW | wr_cell2F HR 46%nat off tacW | wr_cell2F HR 47%nat off tacW | wr_cell2F HR 48%nat off tacW | wr_cell2F HR 49%nat off tacW | wr_cell2F HR 50%nat off tacW | wr_cell2F HR 51%nat off tacW | wr_cell2F HR 52%nat off tacW | wr_cell2F HR 53%nat off tacW | wr_cell2F HR 54%nat off tacW ].

Lemma sm_instantiate : ltac2:(tb__ "0|5|
S0S4eS8cS15S7S4bQ40A1A1Sd0S37S3cZ0R6A2S3eR6ZbA2A2S38S9S22SacR7A1A1SaA3S38SdS5S7S5S13S13A2M0A1M1S7S18A1M2A2M3A1Se8S85S93S8dR8A2A1SacR8A1A2S11G3S3G1G2S4G0S3S13S13S1aP18A1S17S67A1A4S8G0A1A3S8S18A1M4A4A2A3S38S9S22Sb8R9A1A1SaA3S38S9SbcS18S20S58A1SbS18S4S18S28S1aPcA1S17Sc5RaA1A1A2G4A3S71Vhi;A1A3A3SaA3S5aVhi;S50S4fRaA1A1Sc6A3S89Vsegs;VJ;RcRbRaA3S93S8dRcA2R9R8R7A6S89Vsegs;VJ;RdRcRbA3S7dVhi;RdA2Sa8RcRdRaA3R9R8A6F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FKc;FA;Fc;").
Proof.
  intros c A Kc rho tp w Hc Wa Da Wb Fb Hwin H.
  set (rho1 := rho1_of A c rho).
  pose proof H as [HsmA HJ]. destruct HJ as (HA & HK & Htp & Hnf & Hsz & Htop).
  pose proof HA as (HG & HR & HF & HRest & HM).
  pose proof HG as HG0. pose proof (geom_old _ HG0) as HG'. rewrite FS_total_val, kSpaceSize_val in HG'. unfold HIGH_SHADOW_END, IMG_HI, PG in HG'.
  destruct HG' as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22 & G23 & G24).
  assert (TOPlo : topG (aa_geom A) <= fst (obj_range rho1 stack_win)) by (unfold stack_win; rewrite own_lo; exact Htop).
  assert (E12 : rw rho1 12%positive = rw rho 12%positive) by reflexivity.
  assert (E24 : rw rho1 24%positive = rw rho 24%positive) by reflexivity.
  assert (Erm : rm rho1 = rm rho) by reflexivity.
  assert (E151 : rw rho1 151%positive = Z_to_bv 64 (ag_thread (aa_geom A))) by reflexivity.
  assert (E152 : rw rho1 152%positive = Z_to_bv 64 (ag_ctx (aa_geom A))) by reflexivity.
  assert (E153 : rw rho1 153%positive = Z_to_bv 64 (ag_stack_top (aa_geom A))) by reflexivity.
  assert (E154 : rw rho1 154%positive = Z_to_bv 64 (ag_stack_bottom (aa_geom A))) by reflexivity.
  assert (E155 : rw rho1 155%positive = Z_to_bv 64 (ag_fsb (aa_geom A))) by reflexivity.
  assert (E156 : rw rho1 156%positive = Z_to_bv 64 (ag_dtls (aa_geom A))) by reflexivity.
  assert (E157 : rw rho1 157%positive = Z_to_bv 64 (hint_of A c)) by reflexivity.

  assert (H1 : SPA segs (J c A Kc) (Pre_stack_mallocI AE_A c) rho1 tp w).
  { eapply SPA_agree; [| |exact H]; [eapply agree_below_le; [|apply rho1_agree]; cbv; discriminate | apply J_rm_only; reflexivity]. }
  clear H HsmA.

  assert (H2 : SPA segs (J c A Kc) (mkAX (sa c) [] base_sv) rho1 tp w).
  { change (mkAX (sa c) [] base_sv) with (ax_setS (Pre_stack_mallocI AE_A c) (sa c)).
    eapply SPA_restate; [exact Wa | exact Da | reflexivity | | constructor | exact H1].
    constructor; [|constructor]. cbn [fst snd eval]. rewrite E24. unfold tp_ok in Htp. apply bv_eq. rewrite u64_lit by (unfold TP_A; lia).
    rewrite Htp, G4. reflexivity. }
  clear H1.

  destruct HF as (Flen & Fcls & [Fhl Fhint] & Fflags & Ffree & Fsh).
  destruct (Fhint c ltac:(unfold FS_NCLASSES; lia)) as [Hhr Hhc]. unfold fs_hint_cell in Hhc.
  change (nthZ (aa_fs_hint A) c 0) with (hint_of A c) in Hhr, Hhc.
  assert (HINTS : forall z, ag_fsb (aa_geom A) <= z < ag_fsb (aa_geom A) + 88 -> exists x, rd_of segs (rm rho1) (Z_to_bv 64 z) = Some x).
  { intros z Hz. destruct (Fhint ((z - ag_fsb (aa_geom A)) / 8) ltac:(unfold FS_NCLASSES; lia)) as [_ Hc'].
    specialize (Hc' (Z.to_nat ((z - ag_fsb (aa_geom A)) mod 8)) ltac:(cbn [c_w]; pose proof (Z.mod_pos_bound (z - ag_fsb (aa_geom A)) 8); lia)).
    cbn [c_addr c_w c_val] in Hc'. unfold fs_hint_cell in Hc'.
    unfold restrictv in Hc'. rewrite fs_footb_true1 in Hc' by (pose proof (Z.div_mod (z - ag_fsb (aa_geom A)) 8); pose proof (Z.mod_pos_bound (z - ag_fsb (aa_geom A)) 8); lia).
    rewrite view_in in Hc' by (pose proof (Z.div_mod (z - ag_fsb (aa_geom A)) 8); pose proof (Z.mod_pos_bound (z - ag_fsb (aa_geom A)) 8); lia).
    replace (ag_fsb (aa_geom A) + 8 * ((z - ag_fsb (aa_geom A)) / 8) + Z.of_nat (Z.to_nat ((z - ag_fsb (aa_geom A)) mod 8))) with z in Hc'
      by (pose proof (Z.div_mod (z - ag_fsb (aa_geom A)) 8); pose proof (Z.mod_pos_bound (z - ag_fsb (aa_geom A)) 8); lia).
    rewrite Erm. eexists. exact Hc'. }
  assert (HHC : cell_ok (view segs (rm rho)) (mkACell (ag_fsb (aa_geom A) + 8 * c) 8 (hint_of A c))).
  { intros k Hk. specialize (Hhc k Hk). cbn [c_addr c_w c_val] in Hhc |- *. unfold restrictv in Hhc.
    rewrite fs_footb_true1 in Hhc by (cbn [c_w] in Hk; lia). exact Hhc. }
  assert (H3 : SPA segs (J c A Kc) (mkAX (sb c) [] base_sv) rho1 tp w).
  { change (mkAX (sb c) [] base_sv) with
      (ax_setS (mkAX (sa c) [] base_sv) (let S := ax_S (mkAX (sa c) [] base_sv) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ map carve_obj (N_rt c)) (ss_facts S) NW (ss_lenient S))).
    eapply SPA_carve_list; [exact H2 | exact Wb | cbv; discriminate | | |].
    -
      unfold N_rt. pose proof (urange (rw rho 12%positive)) as R12.
      unfold vT, vCTX, vTOP, vBOT, vFSB, vDTLS, vHINT.
      clear G15 G16 G17 G18 G19 G20 G21.
      repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?E151, ?E152, ?E155, ?E156, ?u64_lit by lia.
      all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
      all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
      all: split; [|split; [|apply xwords_clear_nil]].
      all: rewrite ?Erm.
      all: match goal with
           | |- cells_in_view _ _ (ag_fsb _) [(8 * ?cc, _, _)] =>
               unfold cells_in_view; apply Forall_cons; [|apply Forall_nil];
               eapply civ_cell; [exact HHC | cbn [eval]; rewrite E157; reflexivity | lia | lia]
           | |- cells_in_view _ _ _ _ => unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; civ_anyF HR ltac:(rewrite ?E151, ?E152, ?E153, ?E154, ?E155, ?E156, ?E157)
           | |- forall off, _ -> wok_of _ _ (Z_to_bv 64 (0 + off)) = true /\ _ => intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]
           | |- forall off, 8 * ?cc <= off < 8 * ?cc + 8 -> _ =>
               intros off Hoff; eapply (cell_wok_rd _ _ _ _ _ HHC); cbn [c_addr c_w Z.of_nat]; lia
           | |- forall off, _ -> wok_of _ _ _ = true /\ _ =>
               intros off Hoff;
               first [ wr_any2F HR off ltac:(pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & DI); unfold IMG_LO, IMG_HI in *; lia)
                     | destruct (Z_lt_dec off 8); [|destruct (Z_lt_dec off 16)]; wr_any2F HR off ltac:(pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & DI); unfold IMG_LO, IMG_HI in *; lia)
                     | destruct (Z_lt_dec off 56); wr_any2F HR off ltac:(pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & DI); unfold IMG_LO, IMG_HI in *; lia)
                     | destruct (Z_lt_dec off 96); wr_any2F HR off ltac:(pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & DI); unfold IMG_LO, IMG_HI in *; lia) ]
           | _ => idtac end.
      all: fail "sm_instantiate: carve obligation left".
    -
      pose proof (proj1 H2) as (Hsm1 & _). unfold virt in Hsm1. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm1.
      pose proof (smatch_facts_hold _ _ _ _ Hsm1) as HFa.
      assert (Hhigh : holds rho1 F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa); cbn; tauto).
      destruct (stack_win_range _ rho1 _ _ Hsm1 ltac:(cbn; tauto) Hhigh) as (SW1 & SW2 & SW3).
      unfold N_rt. cbn [map carve_obj ss_objs ax_S sa app]. unfold carved, vT, vCTX, vTOP, vBOT, vFSB, vDTLS, vHINT.
      unfold A_globals. unfold O_got, O_rtc. unfold GOT_LO, GOT_HI, RTC_LO, RTC_HI.
      clear G15 G16 G17 G18 G19 G20 G21.
      pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & DI). unfold IMG_LO, IMG_HI in TI, CI, DI.
      repeat apply Forall_cons; try apply Forall_nil;
        (repeat apply Forall_cons; try apply Forall_nil); unfold ranges_disjoint;
        rewrite ?obj_range_mk by (clear TI CI DI; lia); cbn [fst snd eval]; rewrite ?E151, ?E152, ?E155, ?E156, ?u64_lit by (clear TI CI DI; lia);
        first [ clear - Hc G2 G3 G5 G6 G8 G9 G10 G11 G24; lia
              | clear - Hc G2 G3 G5 G6 G8 G9 G10 G11 G24 TI; lia
              | clear - Hc G2 G3 G5 G6 G8 G9 G10 G11 G24 CI; lia
              | clear - Hc G2 G3 G5 G6 G8 G9 G10 G11 G24 DI; lia
              | destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *; clear - Hc G2 G3 G5 G6 G8 G9 G10 G11 G24 TOPlo; lia
              | clear TI CI DI TOPlo; lia
              | destruct (obj_range rho1 stack_win) as [lo' hi']; cbn [fst snd] in *; clear TI CI DI; lia
              | clear TOPlo; lia ].
    -
      pose proof (geom_bands _ HG0) as (_ & _ & _ & _ & TI & CI & DI). unfold IMG_LO, IMG_HI in TI, CI, DI.
      unfold N_rt. cbn [map carve_obj pairwise_disjoint]. unfold carved, vT, vCTX, vTOP, vBOT, vFSB, vDTLS, vHINT.
      repeat split; repeat apply Forall_cons; try apply Forall_nil; try exact I; unfold ranges_disjoint;
        rewrite ?obj_range_mk by (clear TI CI DI G15 G16 G17 G18 G19 G20 G21; lia); cbn [fst snd eval];
        rewrite ?E151, ?E152, ?E155, ?E156, ?u64_lit by (clear TI CI DI G15 G16 G17 G18 G19 G20 G21; lia);
        first [ clear - Hc G2 G3 G5 G6 G8 G9 G10 G11 G24; lia | clear - Hc G2 G3 G5 G6 G8 G9 G10 G11 G24 TI; lia | clear - Hc G2 G3 G5 G6 G8 G9 G10 G11 G24 CI; lia | clear - Hc G2 G3 G5 G6 G8 G9 G10 G11 G24 DI; lia | clear - Hc G2 G3 G5 G6 G8 G9 G10 G11 G24 G15; lia | clear - Hc G2 G3 G5 G6 G8 G9 G10 G11 G24 G16; lia | clear - Hc G2 G3 G5 G6 G8 G9 G10 G11 G24 G17; lia | clear - Hc G2 G3 G5 G6 G8 G9 G10 G11 G24 G19; lia | clear - Hc G2 G3 G5 G6 G8 G9 G10 G11 G24 G20; lia | clear - Hc G2 G3 G5 G6 G8 G9 G10 G11 G24 G21; lia | clear - Hc G2 G3 G5 G6 G8 G9 G10 G11 G24 G18 G12 G13 G14; lia
              | clear TI CI DI G15 G16 G17 G18 G19 G20 G21; lia | clear TI CI DI; lia | clear G15 G16 G17 G18 G19 G20 G21; lia ]. }
  clear H2.

  change (P0 hi c) with (ax_with_facts (mkAX (sb c) [] base_sv) ([SPUle (SVar 12) (SLit (fs_frame_size c))] ++ F_geom hi)).
  eapply SPA_refacts; [exact H3 | exact Fb |].
  intros Hold. apply Forall_cons.
  { cbn [holds eval]. rewrite E12, u64_lit by (pose proof (fs_frame_size_pos c ltac:(lia)); pose proof (fs_class_ok c Hc); lia). exact Hsz. }
  clear G15 G16 G17 G18 G19 G20 G21.
  unfold F_geom. apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split; [|exact Hold]]].
  - unfold vT, vCTX, vTOP, vBOT.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E151, ?E152, ?E153, ?E154; rewrite ?u64_lit by lia; try lia.
  -
    destruct hi; unfold win_hyp in Hwin; rewrite ?FS_total_val in Hwin; unfold F_winB, vFSB, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_HI in *;
      rewrite ?FS_total_val; repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E155; rewrite ?u64_lit by lia; lia.
  - unfold vFSB, vDTLS.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E155, ?E156; rewrite ?u64_lit by lia; try lia.
Qed.

Lemma nth0_enc1_one : ltac2:(tb__ "0|3|
S15S38S4bQ8M0A1M1Se1G1U0S2aU1S1bR1S17Z1M2A1A2A2S4aG0Z0A2A4S4aG0G2A2A3Frho;").
Proof. intros. reflexivity. Qed.

Lemma Z_to_bv64_add : ltac2:(tb__ "0|1|
S0S0S38S4bQ40M0A1Se7Sd3S4aG0R2A2S4aG0R1A2A3S4aG0S3dR2R1A2A2A3Fb;Fa;").
Proof.
  intros a b. apply bv_eq. rewrite add_val, !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  rewrite <- Z.add_mod by lia. reflexivity.
Qed.

Lemma smatchA_rom : ltac2:(tb__ "0|1|
S15S7S4bQ40A1A1S87S7SbeA1M0Se5SbfS8bVsegs;R6R5R4S3G0Sd1R3Sd2R2R1A2A4A5S30Vsegs;SecR2R6R3A3A2F_;Fmd;Fms;Ftr;FX;Ftp;Frho;").
Proof. intros rho tp X tr ms md [Hsm _]. unfold virt in Hsm. cbn in Hsm. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hsm))))). Qed.

Lemma valuation_eta : ltac2:(tb__ "0|0|
S15S38S15S2dS16R1A1S2fR1A1S19R1A1A3R1A3Frho;").
Proof. intros [a b m]. reflexivity. Qed.

Definition RVi (A : AA) (c : Z) (rho0 : valuation) (i : Z) (rho : valuation) : Prop := ltac2:(tb__ "0|3|
S4fVA;A1S56S37S38S4bQ40M0A1M1S16Vrho;P97A2S4aG0S55R1A1A2A3S37S38G1S16Vrho;P98A2S4aG0S51R1A1A2A3S37S38G1S16Vrho;P99A2S4aG0S54R1A1A2A3S37S38G1S16Vrho;P9aA2S4aG0S53R1A1A2A3S37S38G1S16Vrho;P9bA2S4aG0S50R1A1A2A3S37S38G1S16Vrho;P9cA2S4aG0S52R1A1A2A3S37S38G1S16Vrho;P9dA2S4aG0Sa2VA;Vc;A2M2A2A3S37S38G1S16Vrho;P9eA2S4aG0S3dG2Vi;A2A2A3S37S38G1S16Vrho;P9fA2S4aG0S3fS62Vc;A1Vi;A2A2A3S37Se6Sc1Vrho0;Vrho;A3S38G1SdS4bQ8A1A1F_;S19Vrho;A1S19Vrho0;A1A3A2A2A2A2A2A2A2A2A2A2TG;").

Lemma RVi_stable : ltac2:(tb__ "0|0|
S4eS0S15S0S15S15Sa0R6R5R4R3R2A5S24S59R3R2A3Sa0R8R7R6R5R3A5F_;F_;Fr';Fr;Fi;Frho0;Fc;FA;").
Proof.
  intros A c rho0 i r r' (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & [RA RB] & RC) (Hw & Hl & Hm).
  unfold RVi, GW, NF in *.
  rewrite <- !Hw by lia. repeat (split; [assumption|]). split.
  - split; [intros j Hj; rewrite <- Hw by lia; apply RA; exact Hj | intros l; rewrite <- Hl; apply RB].
  - rewrite <- RC. apply functional_extensionality. intros a. symmetry. apply Hm.
Qed.

Definition JC (c : Z) (A : AA) (Kc : KcA) (rho0 : valuation) (i : Z) : jpredA := ltac2:(tb__ "0|0|
SdaSa0VA;Vc;Vrho0;Vi;A4VJ;Vc;VA;VKc;A3A2").

Lemma J_stableA : ltac2:(tb__ "0|0|
S0S4eS8cS91R1A1S8aVsegs;S59VJ;R4R3R2A3A3F_;FKc;FA;Fc;").
Proof.
  intros c A Kc HKc rho rho' tp tr md md' Hag Hme (HA & HK & Htp & Hnf & Hsz & Htop).
  destruct Hag as (Hw & Hl & Hm).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply Hm).
  assert (E12 : rw rho' 12%positive = rw rho 12%positive) by (symmetry; apply Hw; unfold GW; lia).
  assert (E24 : rw rho' 24%positive = rw rho 24%positive) by (symmetry; apply Hw; unfold GW; lia).
  assert (E10 : rw rho' 10%positive = rw rho 10%positive) by (symmetry; apply Hw; unfold GW; lia).
  assert (E15 : rw rho' V_DEPTH = rw rho V_DEPTH) by (symmetry; apply Hw; unfold GW, V_DEPTH; lia).
  split; [|split; [|split; [|split; [|split; [|unfold top_high; rewrite E10, E15; exact Htop]]]]].
  - apply (AInvA_mat segs A rho' tp md md'); [|exact Hme]. unfold AInv, AInvA in *. rewrite Erm. exact HA.
  - destruct Hme as ((mat' & ->) & _). rewrite with_vm_backing_with_vm. apply HKc. exact HK.
  - unfold tp_ok in *. rewrite E24. exact Htp.
  - exact Hnf.
  - rewrite E12. exact Hsz.
Qed.

Lemma JC_stableA : ltac2:(tb__ "0|0|
S0S4eS8cS15S0S91R3A1S8aVsegs;S59S9fR6R5R4R3R2A5A3F_;Fi;Frho0;FKc;FA;Fc;").
Proof. intros. apply stableA_withG; [intros r r' H1 H2; eapply RVi_stable; eauto | apply J_stableA; assumption]. Qed.

Definition s_0 (c : Z) : wsub := ltac2:(tb__ "0|0|
Se3P9eS85S6cVhi;Vc;A2A1S85S60Vhi;S58Vc;S8S14A1S8S18A1A5A1A3").
Definition s_b (c : Z) : wsub := ltac2:(tb__ "0|0|
Se3P9eS85S6fVhi;Vc;A2A1S85S60Vhi;S58Vc;S8S14A1S8S18A1A5A1A3").

Definition posof (A : AA) (c : Z) (i : Z) : Z := ltac2:(tb__ "0|0|
S46S43S3dSa2VA;Vc;A2Vi;A2S41Z2Z40A2A2S78Vc;A1A2").

Lemma NIT_pow : ltac2:(tb__ "0|0|
S0S37S3cZ0R1A2S3eR1ZbA2A2S38S0ScdR2A1S41Z2S3fZeR2A2A2A3F_;Fc;").
Proof. intros c Hc. unfold fs_num_iter, FS_LOG. rewrite Z.shiftl_mul_pow2 by lia. replace (20 - 6 - c) with (14 - c) by lia. lia. Qed.

Lemma posof_range : ltac2:(tb__ "0|2|
S4eS0S0S37S3cZ0M0R2A2S3eR2ZbA2A2S37S3cG0S9eR4R3R2A3M1A2S3eG1S62R3A1A2A2F_;Fi;Fc;FA;").
Proof.
  intros A c i Hc. unfold posof, MASK, NIT. rewrite NIT_pow by lia.
  replace (2 ^ (14 - c) - 1) with (Z.ones (14 - c)) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma posof_mod : ltac2:(tb__ "0|0|
S4eS0S0S37S3cZ0R2A2S3eR2ZbA2A2S38S0S9eR4R3R2A3S43S3dSa2R4R3A2R2A2S41Z2S3fZeR3A2A2A2A3F_;Fi;Fc;FA;").
Proof.
  intros A c i Hc. unfold posof, MASK. rewrite NIT_pow by lia.
  replace (2 ^ (14 - c) - 1) with (Z.ones (14 - c)) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
  rewrite Z.land_ones by lia. apply Z.mod_mod_divide.
  exists (2 ^ (64 - (14 - c))). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma eval_flagaddr : ltac2:(tb__ "0|0|
S4eS0S15S0S15S37S3cZ0R4A2S3eR4ZbA2A2SceS4fR6A1A1Sa0R7R6R5R4R3A5S38S0S4cQ40S1bR4S64R7A1A2A2S3dS3dS50S4fR8A1A1S77R7A1A2S9eR8R7R5A3A2A3F_;F_;F_;Frho;Fi;Frho0;Fc;FA;").
Proof.
  intros A c rho0 i rho Hc HG (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & _).
  pose proof (posof_range A c i Hc) as PR. pose proof (fs_class_ok c Hc) as (K1 & _ & _ & _ & K4 & _ & K6).
  destruct (geom_old _ HG) as (G1 & G2 & G3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TG). rewrite FS_total_val in G3. unfold IMG_HI in G2.
  unfold flagaddr, POS, vFSB, vH. cbn [eval]. rewrite !add_val, and_val, R5, R8. unfold FLOFF, fs_flags. unfold NIT in PR.
  rewrite FS_kFlagsOffset_val. rewrite (u64_lit (ag_fsb (aa_geom A))) by lia.
  rewrite (u64_lit (0 + 4096 + _)) by lia. rewrite (u64_lit (MASK c)) by (unfold MASK; lia).
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 (hint_of A c + i)) with ((hint_of A c + i) mod bv_modulus 64). rewrite two64.
  fold (posof A c i). rewrite !Z.mod_small by lia. lia.
Qed.

Lemma busy_step : ltac2:(tb__ "0|5|
S0S4eS8cS15S0S15OF_;S15S7S4bQ40A1A1Sd0S37S3cZ0M0R9A2S3eR9ZbA2A2S3cG0R6A2S3cS3dS3dR7Z1M1A2Z2A2S62RbA1A2S38S9ScfRbRcS9eRbRcR8A3A3SaA3S38S9S86S6fVhi;RdA2S60Vhi;S58RdS8S14A1M2S8S18A1M3A5Sa4RdA1A3SaA3S38S9Sd8Sa4ReA1P9eM4A2SaA3S38S13Sd6Sa4RfA1G4A2S23Sd3S82S17G1A1A3A3S38S13Sd6Sa4R10A1P9fA2S23Sd3S83S17N1A1A3A3S38S9SbcS18S20S58A1SbS18S61R11A1S1fS85S60Vhi;S58R11G2G3A5A1A1A3A3SaA3S89Vsegs;SdaRdS9fR12R11R10RfReA5A2S76Vhi;R12A2RcRbRaA6S89Vsegs;S9fR13R12R11R10S3dRfG1A2A5S60Vhi;S58R13G2S61R13A1A5Sd7RdSa4R13A1A2RcRbA6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;FrhoE;FG0;Fi;Frho0;FKc;FA;Fc;").
Proof.
  intros c A Kc rho0 i G0 rhoE tp w Hc Hi HiN Hbusy Hent Hid Hs158 Hs159 Hfb H.
  destruct w as [tr [ms md]]. destruct H as [HsmA [_ [HR HJ]]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof HR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & RA & RC).
  destruct HJ as (HA & HK & Htp & Hnf & Hsz). pose proof HA as (HG & HRt & HF & HRest & HM).
  pose proof (eval_flagaddr A c rho0 i rhoE Hc HG HR) as EFL.
  pose proof (posof_range A c i Hc) as PR.
  pose proof (fs_geom_nums (aa_geom A) c (posof A c i) HG Hc PR) as NUM. cbn zeta in NUM.
  rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in NUM. destruct NUM as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10).
  unfold IMG_HI in N8. pose proof (topG_range (aa_geom A)) as TG.
  unfold FLOFF, fs_flags in EFL. rewrite FS_kFlagsOffset_val, Z.add_0_l in EFL. unfold fs_flags in N6, N7. rewrite FS_kFlagsOffset_val in N6, N7.
  set (fl := ag_fsb (aa_geom A) + (4096 + fs_flags_off_nat (Z.to_nat c)) + posof A c i) in EFL.
  assert (Efl : fl = ag_fsb (aa_geom A) + 4096 + fs_flags_off_nat (Z.to_nat c) + posof A c i) by (unfold fl; lia).
  clearbody fl.

  pose proof (SPA_unobj segs (fun _ _ t m => Kc t m) rhoE (Ebusy hi c) (ss_objs (ax_S (Ebusy0 hi c))) [O_flagc c 1] tp tr ms md
                eq_refl (conj HsmA HK) (fun k => k)) as Hb.
  cbn zeta in Hb. set (rho' := rho_absorb rhoE [O_flagc c 1] (vms md tp ms)) in Hb.
  assert (E' : rho' = rhoE).
  { unfold rho'. rewrite <- (valuation_eta rhoE) at 2. unfold rho_absorb. f_equal.
    apply functional_extensionality. intros a. destruct (in_ranges_dec rhoE [O_flagc c 1] a) as [Hin|Hn]; [|reflexivity].
    destruct Hin as (o & [<-|[]] & Hr). unfold O_flagc, carved in Hr. rewrite obj_range_mk in Hr by lia. cbn [fst snd ob_base] in Hr.
    rewrite EFL in Hr.

    pose proof (absorb_carved_cells segs rhoE (ax_S (Ebusy hi c)) tr (vms md tp ms) (vmd md) (ss_objs (ax_S (Ebusy0 hi c))) [O_flagc c 1]
                  (flagaddr c) 0 1 [(0, 1%nat, SLit 1)] ltac:(exact (proj1 HsmA)) eq_refl ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(unfold cells_inside; apply Forall_cons; [cbn; lia|apply Forall_nil])) as [C _].
    unfold cells_in_view in C. apply Forall_inv in C. specialize (C 0%nat ltac:(lia)). rewrite nth0_enc1_one in C. cbn [Z.of_nat] in C.
    rewrite EFL, !Z.add_0_r in C.
    assert (Ea : a = Z_to_bv 64 fl).
    { apply bv_eq. rewrite u64_lit by lia. lia. }
    rewrite Ea. rewrite (rd_of_absorb_in segs rhoE [O_flagc c 1] (vms md tp ms) _) in C.
    2:{ exact (smatchA_rom _ _ _ _ _ _ HsmA). }
    2:{ exists (O_flagc c 1). split; [left; reflexivity|]. unfold O_flagc, carved. rewrite obj_range_mk by lia. cbn [fst snd ob_base]. rewrite EFL, u64_lit by lia. lia. }
    destruct HF as (_ & _ & _ & Fflags & _). specialize (Fflags c (posof A c i) ltac:(unfold FS_NCLASSES; lia) ltac:(unfold NIT in PR; lia)).
    rewrite Hbusy in Fflags. unfold restrictv in Fflags. unfold fs_flags in Fflags. rewrite FS_kFlagsOffset_val in Fflags.
    rewrite fs_footb_true2 in Fflags by (rewrite FS_kFlagsOffset_val, FS_total_val; lia).
    rewrite view_in in Fflags by lia. rewrite <- Efl in Fflags.
    assert (BFL : 0x646000 <= fl < 2 ^ 64) by (clear -Efl N6 N7 N8 N9 TG PR; lia).
    pose proof (rd_off_image (rm rhoE) _ _ BFL Fflags) as M1.
    unfold rd, ms_read_byte in C. rewrite M1.
    destruct (ms_mem (vms md tp ms) _) as [b|] eqn:EM; [congruence|].
    exfalso. rewrite (smatchA_rom _ _ _ _ _ _ HsmA _) in C. rewrite image_byte_A_off in C by lia. discriminate. }
  rewrite E' in Hb. clear rho' E'.
  change (ax_setS (Ebusy hi c) (set_objs (ax_S (Ebusy hi c)) (ss_objs (ax_S (Ebusy0 hi c))))) with (Ebusy0 hi c) in Hb.

  pose proof (smatchA_entails segs _ _ _ rhoE tp _ Hent (proj1 Hb)) as Hsm2.
  set (rho2 := rho_sub rhoE (s_b c)) in *.
  assert (Hlow : forall k, (k < 158)%positive -> rw rho2 k = rw rhoE k).
  { intros k Hk. unfold rho2. cbn [rho_sub rw]. rewrite (wsub_get_id _ _ _ Hid Hk). reflexivity. }
  assert (E158 : rw rho2 158%positive = Z_to_bv 64 (hint_of A c + (i + 1))).
  { unfold rho2. cbn [rho_sub rw]. rewrite Hs158. unfold vH. cbn [eval]. rewrite R8, Z_to_bv64_add. f_equal. lia. }
  assert (E159 : rw rho2 159%positive = Z_to_bv 64 (NIT c - (i + 1))).
  { unfold rho2. cbn [rho_sub rw]. rewrite Hs159. unfold vK. cbn [eval]. rewrite R9, Z_to_bv64_add. f_equal. lia. }
  assert (Erm2 : rm rho2 = rm rhoE) by reflexivity.

  change (Cgen hi NW c [] (F_K c)) with (ax_with_facts (mkAX (ax_S (Cgen hi NW c [] [])) [] base_sv) (F_K c ++ ss_facts (ax_S (Cgen hi NW c [] [])))).
  apply SPA_refacts; [| exact Hfb |].
  - split; [exact Hsm2|]. cbn [w_tr w_cfg cfg_model fst snd]. split.
    + unfold RVi. rewrite !Hlow by (cbv; reflexivity). rewrite E158, E159, Erm2.
      repeat (split; [first [assumption | reflexivity]|]). split; [|exact RC].
      destruct RA as [RA1 RA2]. split; [intros k Hk; rewrite Hlow by (unfold NF in Hk; lia); apply RA1; exact Hk | intros l; unfold rho2; cbn; apply RA2].
    + unfold J, J_stack_malloc_preT, tp_ok, top_high in *. rewrite !Hlow by (cbv; reflexivity). unfold AInv, AInvA in *. rewrite Erm2. auto.
  - intros Hold. apply Forall_app. split; [|exact Hold].
    unfold F_K, vK. repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite E159, !u64_lit by (unfold NIT in *; pose proof (fs_class_ok c Hc); lia); unfold NIT in *; lia.
Qed.

Definition RV0 (A : AA) (c : Z) (rho0 : valuation) (rho : valuation) : Prop := ltac2:(tb__ "0|2|
S4fVA;A1S56S37S38S4bQ40M0A1M1S16Vrho;P97A2S4aG0S55R1A1A2A3S37S38G1S16Vrho;P98A2S4aG0S51R1A1A2A3S37S38G1S16Vrho;P99A2S4aG0S54R1A1A2A3S37S38G1S16Vrho;P9aA2S4aG0S53R1A1A2A3S37S38G1S16Vrho;P9bA2S4aG0S50R1A1A2A3S37S38G1S16Vrho;P9cA2S4aG0S52R1A1A2A3S37S38G1S16Vrho;P9dA2S4aG0Sa2VA;Vc;A2A2A3S37Se6Sc1Vrho0;Vrho;A3S38G1SdS4bQ8A1A1F_;S19Vrho;A1S19Vrho0;A1A3A2A2A2A2A2A2A2A2TG;").
Lemma RV0_stable : ltac2:(tb__ "0|0|
S4eS0S15S15S15Sa5R5R4R3R2A4S24S59R3R2A3Sa5R7R6R5R3A4F_;F_;Fr';Fr;Frho0;Fc;FA;").
Proof.
  intros A c rho0 r r' (R1 & R2 & R3 & R4 & R5 & R6 & R7 & [RA RB] & RC) (Hw & Hl & Hm).
  unfold RV0, GW, NF in *.
  rewrite <- !Hw by lia. repeat (split; [assumption|]). split.
  - split; [intros j Hj; rewrite <- Hw by lia; apply RA; exact Hj | intros l; rewrite <- Hl; apply RB].
  - rewrite <- RC. apply functional_extensionality. intros a. symmetry. apply Hm.
Qed.
Definition JE (c : Z) (A : AA) (Kc : KcA) (rho0 : valuation) : jpredA := ltac2:(tb__ "0|0|
SdaSa5VA;Vc;Vrho0;A3VJ;Vc;VA;VKc;A3A2").
Lemma JE_stableA : ltac2:(tb__ "0|0|
S0S4eS8cS15S91R2A1S8aVsegs;S59SaaR5R4R3R2A4A3F_;Frho0;FKc;FA;Fc;").
Proof. intros. apply stableA_withG; [intros r r' H1 H2; eapply RV0_stable; eauto | apply J_stableA; assumption]. Qed.

Lemma RV0_rho1 : ltac2:(tb__ "0|0|
S4eS0S15Sa5R3R2R1Sa8R3R2R1A3A4Frho;Fc;FA;").
Proof.
  intros A c rho. unfold RV0. repeat (split; [reflexivity|]). split; [|reflexivity].
  apply agree_below_vals. apply rho1_agree.
Qed.

Lemma entry_step : ltac2:(tb__ "0|4|
S0S4eS8cS15S15OF_;S15S7S4bQ40A1A1Sd0S37S3cZ0M0R8A2S3eR8ZbA2A2S3cZ3S62R9A1A2S38S9S86S6cVhi;RaA2S60Vhi;S58RaS8S14A1M1S8S18A1M2A5Sa3RaA1A3SaA3S38S9Sd8Sa3RbA1P9eM3A2SaA3S38S13Sd6Sa3RcA1G3A2S6bA3S38S13Sd6Sa3RdA1P9fA2S17S62RdA1A1A3S38S9SbcS18S20S58A1SbS18S61ReA1S1fS85S60Vhi;S58ReG1G2A5A1A1A3A3SaA3S89Vsegs;SdaRbSaaRfReRdRcA4A2S6cVhi;RfA2RaR9R8A6S89Vsegs;S9fR10RfReRdG0A5S60Vhi;S58R10G1S61R10A1A5Sd7RbSa3R10A1A2RaR9A6F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;FrhoE;FG0;Frho0;FKc;FA;Fc;").
Proof.
  intros c A Kc rho0 G0 rhoE tp w Hc HN Hent Hid Hs158 Hs159 Hfb H.
  destruct w as [tr [ms md]]. destruct H as [HsmA [_ [HR HJ]]]. cbn [w_tr w_cfg cfg_model fst snd] in HJ.
  pose proof HR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & RA & RC).
  pose proof (smatchA_entails segs _ _ _ rhoE tp _ Hent HsmA) as Hsm2.
  set (rho2 := rho_sub rhoE (s_0 c)) in *.
  assert (Hlow : forall k, (k < 158)%positive -> rw rho2 k = rw rhoE k).
  { intros k Hk. unfold rho2. cbn [rho_sub rw]. rewrite (wsub_get_id _ _ _ Hid Hk). reflexivity. }
  assert (E158 : rw rho2 158%positive = Z_to_bv 64 (hint_of A c + 0)).
  { unfold rho2. cbn [rho_sub rw]. rewrite Hs158. unfold vHINT. cbn [eval]. rewrite R7. f_equal. lia. }
  assert (E159 : rw rho2 159%positive = Z_to_bv 64 (NIT c - 0)).
  { unfold rho2. cbn [rho_sub rw]. rewrite Hs159. cbn [eval]. f_equal. lia. }
  assert (Erm2 : rm rho2 = rm rhoE) by reflexivity.
  change (Cgen hi NW c [] (F_K c)) with (ax_with_facts (mkAX (ax_S (Cgen hi NW c [] [])) [] base_sv) (F_K c ++ ss_facts (ax_S (Cgen hi NW c [] [])))).
  apply SPA_refacts; [| exact Hfb |].
  - split; [exact Hsm2|]. cbn [w_tr w_cfg cfg_model fst snd]. split.
    + unfold RVi. rewrite !Hlow by (cbv; reflexivity). rewrite E158, E159, Erm2.
      repeat (split; [first [assumption | reflexivity]|]). split; [|exact RC].
      destruct RA as [RA1 RA2]. split; [intros k Hk; rewrite Hlow by (unfold NF in Hk; lia); apply RA1; exact Hk | intros l; unfold rho2; cbn; apply RA2].
    + destruct HJ as (HA & HK & Htp & Hnf & Hsz & Htop). unfold J, J_stack_malloc_preT, tp_ok, top_high in *. rewrite !Hlow by (cbv; reflexivity). unfold AInv, AInvA in *. rewrite Erm2. split; [exact HA|]. repeat split; auto.
  - intros Hold. apply Forall_app. split; [|exact Hold].
    unfold F_K, vK. repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite E159, !u64_lit by (unfold NIT in *; pose proof (fs_class_ok c Hc); lia); unfold NIT in *; lia.
Qed.

Lemma geom_numsS : ltac2:(tb__ "0|d|
S56SceR1A1S37S38S0S43S50R2A1M0Z1000M1A2Z0M2A3S37S3cZ646000G0A2S37S3cS3dG0Zb09000A2M3S57R2A1M4A2S37S3cG1S55R2A1M5A2S37S3cS3dG5G1A2M6G4A2S37S3cG1S51R2A1M7A2S37S3cS3dG7G1A2M8G4A2S37S3cG1S52R2A1M9A2S37S3cS3dG9G1A2MaG4A2S37S39S3cG3G5A2S3cG6G0A2A2S37S39S3cG3G7A2S3cG8G0A2A2S37S39S3cG3G9A2S3cGaG0A2A2S37S39S3cG6G7A2S3cG8G5A2A2S37S39S3cG6G9A2S3cGaG5A2A2S37S39S3cG8G9A2S3cGaG7A2A2S37S37S3cG2S53R2A1MbA2S3eGbS54R2A1McA2A2S37S3cGcS41Z2Z2fA2A2S37S3cZ7fff7f800000G4A2S3cG4Z7fffff800000A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2F_;FG;").
Proof.
  intros G HG. pose proof (geom_old G HG) as X. rewrite FS_total_val, kSpaceSize_val in X. unfold IMG_HI, PG in X. tauto.
Qed.

Lemma own_range : ltac2:(tb__ "0|5|
S15S21S5S7SbeA1Sd1A2S7S29A1S2bS27Vsegs;R5R4R3A4SbbS14S25S1aPaA1M0S1aS8eA1M1S17Z0A1M2R3R2A5S1dR5A1A3S2cR7S92A2S37S3cZ7fff7f800000SfS0S0S26R8S25G0G1G2R5R4A5A2M3A3M4A2S3cG4S10S0S0G3A3A2A2F_;F_;F_;Fd;Fcells;Fw;FS;Frho;").
Proof.
  intros rho S w cells d Hsm Hin Hf.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _).
  pose proof (proj1 (Forall_forall _ _) Hall _ Hin) as Ho.
  unfold obj_holds, obj_lo_of, obj_hi_of in Ho. cbn [ob_base ob_lo ob_hi] in Ho.
  destruct Ho as ((B1 & B2 & B3 & B4) & _).
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd].
  rewrite soff_lit in *. replace (snorm 0) with 0 in * by reflexivity.
  cbn [eval] in *. unfold holds, F_sp_high in Hf. cbn [eval] in Hf. rewrite add_val in Hf.
  rewrite u64_lit in Hf by lia.
  rewrite soff_snorm in *. unfold U in *. cbn [eval] in *.
  pose proof (urange (rw rho 10%positive)) as R10. pose proof (urange (rw rho V_DEPTH)) as R15.
  unfold snorm in *.
  rewrite (Z.mod_small (bv_unsigned (rw rho V_DEPTH)) (2 ^ 64)) in * by lia.
  destruct (Z.ltb_spec (bv_unsigned (rw rho V_DEPTH)) (2 ^ 63)).
  - assert (bv_unsigned (rw rho V_DEPTH) = 0) by lia. rewrite H0 in *. rewrite Z.add_0_r, Z.mod_small in Hf by lia. lia.
  - replace ((bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH)) mod 2 ^ 64)
      with (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH) - 2 ^ 64) in Hf.
    2:{ symmetry. replace (bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH)) with
          ((bv_unsigned (rw rho 10%positive) + bv_unsigned (rw rho V_DEPTH) - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    lia.
Qed.

Lemma loop_objs_clear : ltac2:(tb__ "0|1|
S0S4eS15S0S15S21S5S7SbeA1Sd1A2S13S0S0S37S3cZ0RaA2S3eRaZbA2A2SceS4fRaA1A1Sa0RbRcRaR9R8A5S9dRcR9A2S27Vsegs;RaR9R8A4S38S7S14A1S1dRaA1SbS14S4S14S72S8S14A1A3SbS14S90S66RfR8A2A3A3A3SbbS18S92S1fRbA1A3S39S37S3cS3dS50S4fR10A1A1M0Z1000A2R9A2S3cR8S3dG0Sc6A2A2A2S37S3cZ7fff8000R9A2S3cR8Z10007fff8000A2A2A2SdfS14S14S2eS26RfR1A2S3S0S0RbRaA4A2Lo';S1dRdA1A3F_;F_;F_;F_;F_;F_;F_;F_;Fhi0;Flo0;Fh;Fw;FS;Frho;Fi;Frho0;FA;Fc;").
Proof.
  intros c A rho0 i rho S w h lo hi' Hc HG HR Htop Hsm Hobjs Hfact Hrng.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & TG).
  pose proof (geom_bands _ HG) as (BF & BT & BC & BD & TI & CI & DI).
  rewrite FS_total_val in BF. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_LO, IMG_HI in BF, BT, BC, BD, TI, CI, DI.
  pose proof HR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & RA & RC).
  rewrite FS_total_val in Hrng.
  pose proof (smatch_facts_hold _ _ _ _ Hsm) as HFa.
  assert (Hhigh : holds rho F_sp_high) by (apply (proj1 (Forall_forall _ _) HFa); exact Hfact).
  destruct (own_range rho S w _ _ Hsm ltac:(rewrite Hobjs; left; reflexivity) Hhigh) as [SW1 SW3].
  assert (SW0 : topG (aa_geom A) <= fst (obj_range rho O_own)) by (unfold O_own; rewrite own_lo; exact Htop).
  rewrite Hobjs. unfold RT_objs, RT_fixed. cbn [app]. unfold A_globals, O_got, O_rtc, GOT_LO, GOT_HI, RTC_LO, RTC_HI,
    O_rt1a, O_rt1b, O_tsda, O_tsdb, O_tsdc, O_realtls, O_self_tsd, O_tlsa, O_tlsb, O_tlsc, O_tlsd, O_tsd0, O_ctx8, O_ctx98, O_T0, O_T40, O_T30, O_T48,
    O_dtls, O_cfa, O_cfb, O_cfc, O_cfd, O_cfe, O_pga, O_pgb, O_fsh_l, O_fsh_h, carved,
    vT, vCTX, vTOP, vBOT, vFSB, vDTLS, vHINT.
  apply Forall_cons.
  { unfold ranges_disjoint, O_own in *. destruct (obj_range rho (mkObj (SVar 10) (SVar V_DEPTH) (SLit 0) _ _)) as [lo' hi'']; cbn [fst snd] in *.
    clear BT BC BD TI CI DI. lia. }
  repeat apply Forall_cons; try apply Forall_nil; unfold ranges_disjoint;
    rewrite obj_range_mk by lia; cbn [fst snd eval]; rewrite ?R1, ?R2, ?R5, ?R6, ?u64_lit by lia;
    first [ clear BF BT BC BD TI CI DI; lia
          | clear BF BC BD CI DI; lia
          | clear BF BT BD TI DI; lia
          | clear BF BT BC TI CI; lia
          | clear BT BC BD TI CI DI; lia
          | lia ].
Qed.

Lemma loop_facts : ltac2:(tb__ "0|7|
S0S4eS8cS15S0S15S7S4bQ40M0A1A1S7SbeA1SbfS37S3cZ0M1R9A2S3eR9ZbA2A2S9fRaR9R8R7R6R5R4R3R2A9S50S4fRaA1A1S0S9eRbRcR8A3S0S3dS3dS3dR2Z1000M2A2SccS44RdA1A1A2R1A2S0S37Sa0RdReRbRaR9A5S37VAInv;RdR9R8R6A4S37SceS4fRdA1M3A1S37S37S3cG1R2A2S3eR2S62ReA1A2A2S37S38S0S4cG0S1bR9S64ReA1A2A2R1A3S37S3cS3dR3G2A2R1A2S37S3cS3dR1Z1M4A2S3dR3Z9000A2A2S37S3cZ646000R3A2S37S3cS3dR3Zb09000A2S57G3A1A2S37S38S0S43R3G2A2G1A3S38SdS4bQ8M5A1M6A1Sf2Vsegs;S19R9A1R1A3S11G6S4aG5S9S0L_;ScfRdReR2A3G4G1X9x2A2A2A3A2A2A2A2A2A2A2A2A2A2Tfl;Tpos;TF;F_;F_;Fmd;Ftr;Ftp;Frho;Fi;Frho0;FKc;FA;Fc;").
Proof.
  intros c A Kc rho0 i rho tp tr md Hc [HR HJ] F pos fl.
  destruct HJ as (HA & HK & Htp & Hnf & Hsz & Htop). pose proof HA as (HG & HRt & HF & HRest & HM).
  pose proof (eval_flagaddr A c rho0 i rho Hc HG HR) as EFL.
  pose proof (posof_range A c i Hc) as PR. unfold NIT in PR.
  pose proof (fs_geom_nums (aa_geom A) c (posof A c i) HG Hc PR) as NUM. cbn zeta in NUM.
  rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in NUM. destruct NUM as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10).
  unfold IMG_HI in N8. unfold fs_flags in N6, N7. rewrite FS_kFlagsOffset_val in N6, N7. unfold PG in N10.
  unfold FLOFF, fs_flags in EFL. rewrite FS_kFlagsOffset_val, Z.add_0_l in EFL.
  destruct HF as (_ & _ & _ & Fflags & _). specialize (Fflags c (posof A c i) ltac:(unfold FS_NCLASSES; lia) PR).
  unfold restrictv in Fflags. unfold fs_flags in Fflags. rewrite FS_kFlagsOffset_val in Fflags.
  rewrite fs_footb_true2 in Fflags by (rewrite FS_kFlagsOffset_val, FS_total_val; lia).
  subst F pos fl. split; [exact HR|]. split; [exact HA|]. split; [exact HG|]. split; [unfold NIT; exact PR|].
  split; [rewrite EFL; lia|]. repeat (split; [lia|]). exact Fflags.
Qed.

Lemma busy_carve : ltac2:(tb__ "0|0|
S0S4eS8cS15S0S15S7S4bQ40A1A1Sd0S37S3cZ0R8A2S3eR8ZbA2A2S38S9ScfR8R9S9eR8R9R5A3A3SaA3S38S9S22S85S6eVhi;RaA2A1A1SaA3S89Vsegs;S9fRbRaR9R8R7A5S60Vhi;S58RbS8S14A1S61RbA1A5R6R5R4A6S89Vsegs;S9fRcRbRaR9R8A5S6eVhi;RcA2R7R6R5A6F_;F_;F_;F_;Fw;Ftp;Frho;Fi;Frho0;FKc;FA;Fc;").
Proof.
  intros c A Kc rho0 i rho tp w Hc Hbusy Hwf H.
  destruct w as [tr [ms md]]. pose proof H as [HsmA HJC].
  destruct (loop_facts c A Kc rho0 i rho tp tr md Hc HJC) as (HR & HA & HG & PR & EFL & N6 & N7 & N8 & N9 & N10 & FL).
  cbn zeta in EFL, N6, N7, FL. rewrite Hbusy in FL. pose proof (topG_range (aa_geom A)) as TG.
  assert (Htop : top_high A rho) by (destruct HJC as [_ HJ]; exact (proj2 (proj2 (proj2 (proj2 (proj2 HJ)))))).
  set (fl := ag_fsb (aa_geom A) + 4096 + fs_flags_off_nat (Z.to_nat c) + posof A c i) in *.
  change (Cbusy hi c) with
    (ax_setS (Cgen hi NW c [] (F_K c)) (let S := ax_S (Cgen hi NW c [] (F_K c)) in
       mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ [carved (flagaddr c) 0 1 [(0, 1%nat, SLit 1)]]) (ss_facts S) NW (ss_lenient S))).
  eapply SPA_carve_obj; [exact H | exact Hwf | cbv; discriminate | rewrite ?EFL; try lia ..].
  all: rewrite ?EFL; try lia.
  - unfold cells_inside. apply Forall_cons; [cbn; lia | apply Forall_nil].
  - pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
    eapply (loop_objs_clear c A rho0 i rho _ _ vHINT); [exact Hc | exact HG | exact HR | exact Htop | exact Hsm | reflexivity | | left; rewrite FS_total_val; lia].
    cbn. unfold F_K, F_geom, F_winB, pre_facts. destruct hi; cbn; tauto.
  - intros off Hoff. rewrite view_in in FL by lia. replace (fl + off) with fl by lia. eapply wok_rd_off_image; [lia | exact FL].
  - unfold cells_in_view. apply Forall_cons; [|apply Forall_nil]. intros j Hj. rewrite nth0_enc1_one at 1 || idtac.
    replace j with 0%nat by lia. rewrite nth0_enc1_one. cbn [Z.of_nat]. rewrite !Z.add_0_r. rewrite view_in in FL by lia. exact FL.
  - apply xwords_clear_nil.
Qed.

Lemma eval_POS : ltac2:(tb__ "0|0|
S4eS0S15S0S15S37S3cZ0R4A2S3eR4ZbA2A2Sa0R6R5R4R3R2A5S38S0S4cQ40S1bR3S7eR6A1A2A2S9eR7R6R4A3A3F_;F_;Frho;Fi;Frho0;Fc;FA;").
Proof.
  intros A c rho0 i rho Hc (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & _).
  pose proof (fs_class_ok c Hc) as (K1 & _ & _ & _ & K4 & _ & K6).
  unfold POS, vH. cbn [eval]. rewrite and_val, R8. rewrite (u64_lit (MASK c)) by (unfold MASK, NIT; lia).
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 (hint_of A c + i)) with ((hint_of A c + i) mod bv_modulus 64). rewrite two64.
  reflexivity.
Qed.

Lemma eval_ffx : ltac2:(tb__ "0|0|
S4eS0S15S0S15S37S3cZ0R4A2S3eR4ZbA2A2SceS4fR6A1A1Sa0R7R6R5R4R3A5S38S0S4cQ40S1bR4S68R7A1A2A2Sc7S50S4fR8A1A1R7S9eR8R7R5A3A3A3F_;F_;F_;Frho;Fi;Frho0;Fc;FA;").
Proof.
  intros A c rho0 i rho Hc HG HR. pose proof HR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & _).
  pose proof (posof_range A c i Hc) as PR. pose proof (fs_class_ok c Hc) as (K1 & K2 & K3 & _ & K4 & K5 & K6). unfold NIT in PR.
  destruct (geom_numsS _ HG) as (G1 & G2 & G3 & _). pose proof (topG_range (aa_geom A)) as TG.
  pose proof (fs_geom_nums (aa_geom A) c (posof A c i) HG Hc PR) as NUM. cbn zeta in NUM.
  rewrite FS_frames_off_val, FS_total_val in NUM. destruct NUM as (N1 & N2 & _).
  assert (SZ : fs_frame_size c = 2 ^ (6 + c)) by (unfold fs_frame_size; rewrite Z.shiftl_mul_pow2 by lia; change 64 with (2 ^ 6); rewrite <- Z.pow_add_r by lia; reflexivity).
  assert (PS : 0 <= posof A c i * fs_frame_size c /\ posof A c i * fs_frame_size c + fs_frame_size c <= 2 ^ 20) by nia.
  assert (SL : bv_unsigned (eval rho (SAlu ALU_SLL (POS c) (SLit (6 + c)))) = posof A c i * fs_frame_size c).
  { remember (POS c) as pe. cbn [eval]. subst pe. rewrite sll_val, (eval_POS A c rho0 i rho Hc HR). rewrite (Z.mod_small (6 + c) 64) by lia.
    rewrite Z.shiftl_mul_pow2 by lia. rewrite <- SZ. apply Z.mod_small. lia. }
  unfold ffx. unfold fs_frame. rewrite FS_frames_off_val. unfold FS_LOG. change (Z.shiftl 1 20) with (2 ^ 20).
  destruct (Z.eqb_spec c 0) as [->|Hne].
  - change (SAlu ALU_SLL (POS 0) (SLit 6)) with (SAlu ALU_SLL (POS 0) (SLit (6 + 0))).
    remember (SAlu ALU_SLL (POS 0) (SLit (6 + 0))) as e. cbn [eval]. rewrite !add_val. subst e. rewrite SL. unfold vFSB. cbn [eval]. rewrite R5.
    rewrite !u64_lit by lia. rewrite !Z.mod_small by lia. lia.
  - remember (SAlu ALU_SLL (POS c) (SLit (6 + c))) as e. cbn [eval]. rewrite !add_val. subst e. rewrite SL. unfold vFSB. cbn [eval]. rewrite R5.
    rewrite !u64_lit by lia. rewrite !Z.mod_small by lia. lia.
Qed.

Definition N_free (c : Z) : list carve_spec := ltac2:(tb__ "0|c|
S4S5S5S5S13S0A2M0S0A2M1S7S5S5S0S6A2M2S13A2M3A1M4A2M5S3G1G4S3G0S0S3S13S0S64Vc;A1Z0M6A4Z1A4S4G3S3G2S13S3S0S6G6U1A4S17G6A1A4S8G3A1M7A3A4S4G5S3G1G4S3G0S0S3S13S0S68Vc;A1M8G6A4S3fSc5Vc;A1M9Z8MaA2MbA4G7A4S4G5S3G1G4S3G0S0S3S13S0G8GbA4G9A4G7A4S4G5S3G1G4S3G0S0S3S13S0S23Sd3S5bG8A1S5cA3G6A4S42G9GaA2A4G7A4S8G5A1A3A3A3A3").
Definition Cfree0 (c : Z) : sstate := ltac2:(tb__ "0|0|
S85S60Vhi;S58Vc;S8S14A1S61Vc;A1A5A1S21S1cS34R1A1S35R1A1S32R1A1S31R1A1S36R1A1SbS14S1dR1A1Se0S5dS14S5eSb2Vc;A1A4A3S1fR1A1S63S33R1A1A9TS;").
Definition rhoF_of (A : AA) (c i : Z) (rho : valuation) : valuation := ltac2:(tb__ "0|0|
Se9Vrho;S81S4aQ40S42Sc7S50S4fVA;A1A1Vc;S9eVA;Vc;Vi;A3A3Z8A2A2A3").

Lemma free_carve : ltac2:(tb__ "0|1|
S0S4eS8cS15S0S15S7S4bQ40A1A1Sd0S37S3cZ0R8A2S3eR8ZbA2A2S38S9ScfR8R9S9eR8R9R5A3A3ScA3S38S9S22Sb1RaA1A1SaA3S38S9SbcS18S20S63A1SbS18SbS18S61RbA1S70Vhi;RbA2A3S1fS85S60Vhi;S58RbS8S14A1M0S8S18A1A5A1A1A3A3SaA3S5aVhi;S50S4fRbA1A1Sc6A3S89Vsegs;S9fRdRcRbRaR9A5S60Vhi;S58RdG0S61RdA1A5R8R7R6A6S89Vsegs;S9fReRdRcRbRaA5S75Vhi;ReA2Sb7RdReRaR9A4R8R7A6F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fi;Frho0;FKc;FA;Fc;").
Proof.
  intros c A Kc rho0 i rho tp w Hc Hfree Hwf Hfb Hwin H.
  destruct w as [tr [ms md]]. set (rhoF := rhoF_of A c i rho).

  assert (H1 : SPA segs (JC c A Kc rho0 i) (Cgen hi NW c [] (F_K c)) rhoF tp (tr, mkCfg ms md)).
  { eapply SPA_agree; [| |exact H].
    - unfold rhoF, rhoF_of. split; [|split; [intros; reflexivity|intros; reflexivity]]. intros k Hk. rewrite rho_set_rw_other; [reflexivity|]. unfold vGF. cbn [ss_next ax_S Cgen Cst mkA] in Hk. unfold NW in Hk. lia.
    - intros [HR HJ]. split; [eapply RVi_stable; [exact HR|] | destruct HJ as (HA & HK & Htp & Hnf & Hsz)].
      + unfold rhoF, rhoF_of. split; [|split; [intros; reflexivity|intros; reflexivity]]. intros k Hk. rewrite rho_set_rw_other; [reflexivity|]. unfold vGF, GW in *. lia.
      + unfold J, J_stack_malloc_preT, tp_ok, top_high, AInv, AInvA in *. cbn. unfold rhoF, rhoF_of. cbn in HA, HK |- *. tauto. }
  clear H. pose proof H1 as [HsmA HJC].
  assert (Htop : top_high A rhoF) by (destruct HJC as [_ HJ]; exact (proj2 (proj2 (proj2 (proj2 (proj2 HJ)))))).
  destruct (loop_facts c A Kc rho0 i rhoF tp tr md Hc HJC) as (HR & HA & HG & PR & EFL & N6 & N7 & N8 & N9 & N10 & FL).
  cbn zeta in EFL, N6, N7, FL. rewrite Hfree in FL. pose proof (topG_range (aa_geom A)) as TG.
  pose proof (proj1 (geom_bands _ HG)) as WB. rewrite FS_total_val in WB. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in WB.
  set (fl := ag_fsb (aa_geom A) + 4096 + fs_flags_off_nat (Z.to_nat c) + posof A c i) in *.
  set (F := ag_fsb (aa_geom A)) in *. set (pos := posof A c i) in *. set (ff := fs_frame F c pos).
  pose proof (eval_ffx A c rho0 i rhoF Hc HG HR) as EFF. fold F pos ff in EFF.
  pose proof (fs_geom_nums (aa_geom A) c pos HG Hc ltac:(unfold NIT in PR; exact PR)) as NUM. cbn zeta in NUM. fold F ff in NUM.
  rewrite FS_frames_off_val, FS_total_val, FS_kFlagsOffset_val in NUM. destruct NUM as (M1 & M2 & M3 & M4 & M5 & _).
  assert (EvG : rw rhoF vGF = Z_to_bv 64 (ff / 8)) by (unfold rhoF, rhoF_of; rewrite rho_set_rw_at; reflexivity).
  assert (Esh : bv_unsigned (eval rhoF (SAlu ALU_ADD (gsv (ffx c)) shb)) = Sh ff).
  { unfold shb. cbn [eval]. rewrite add_val, gsv_val, EFF. rewrite !u64_lit by (unfold SHADOW_OFF; lia). unfold Sh, SHADOW_OFF. rewrite Z.mod_small by lia. reflexivity. }
  assert (ShF : Sh (F + 36864) <= Sh ff) by (apply Sh_mono; lia).
  assert (ShE : Sh ff + fs_frame_size c / 8 <= Sh (F + 11571200)).
  { unfold Sh. replace (ff / 8 + SHADOW_OFF + fs_frame_size c / 8) with ((ff + fs_frame_size c) / 8 + SHADOW_OFF).
    - apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
    - replace ff with (ff / 8 * 8) at 1 by (pose proof (Z.div_mod ff 8); pose proof (Z.mod_divide ff 64); lia).
      rewrite Z.div_add_l by lia. lia. }
  assert (ShLo : 0x800b7600 <= Sh (F + 36864)) by (unfold Sh, SHADOW_OFF; lia).
  assert (ShHi : Sh (F + 11571200) < 17594333495296) by (unfold Sh, SHADOW_OFF; lia).
  assert (SZ8 : 0 <= fs_frame_size c / 8) by (apply Z.div_pos; lia).
  pose proof HA as (_ & _ & HF & _). destruct HF as (Flen & Fcls & Fhint & Fflags & Ffree & Fsh). fold F in Ffree, Fsh.
  rewrite FS_frames_off_val, FS_total_val in Fsh.
  specialize (Ffree c pos ltac:(unfold FS_NCLASSES; lia) ltac:(unfold NIT in PR; exact PR) Hfree). fold ff in Ffree.

  assert (H2 : SPA segs (JC c A Kc rho0 i) (mkAX (Cfree0 c) [] base_sv) rhoF tp (tr, mkCfg ms md)).
  { change (mkAX (Cfree0 c) [] base_sv) with
      (ax_setS (Cgen hi NW c [] (F_K c)) (let S := ax_S (Cgen hi NW c [] (F_K c)) in
         mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) (ss_objs S ++ map carve_obj (N_free c)) (ss_facts S) NWF (ss_lenient S))).
    pose proof (proj1 HsmA) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model ax_S] in Hsm.
    eapply SPA_carve_list; [exact H1 | exact Hwf | cbv; discriminate | | |].
    - unfold N_free. repeat apply Forall_cons; try apply Forall_nil; rewrite ?EFL, ?EFF, ?Esh.
      + repeat (split; [lia|]). split; [unfold cells_inside; apply Forall_cons; [cbn; lia|apply Forall_nil]|].
        split; [|split; [|apply xwords_clear_nil]].
        * intros off Hoff. rewrite view_in in FL by lia. replace (fl + off) with fl by lia. eapply wok_rd_off_image; [lia | exact FL].
        * unfold cells_in_view. apply Forall_cons; [|apply Forall_nil]. intros j Hj. replace j with 0%nat by lia.
          rewrite nth0_enc1_zero. cbn [Z.of_nat]. rewrite !Z.add_0_r. rewrite view_in in FL by lia. exact FL.
      + repeat (split; [lia|]). split; [constructor|]. split; [|split; [constructor | apply xwords_clear_nil]].
        intros off Hoff. destruct (Ffree (ff + off) ltac:(lia)) as [b Hb]. unfold restrictv in Hb.
        rewrite fs_footb_true2 in Hb by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia). rewrite view_in in Hb by lia.
        eapply wok_rd_off_image; [lia | exact Hb].
      + repeat (split; [lia|]). split; [constructor|]. split; [|split; [constructor | apply xwords_clear_nil]].
        intros off Hoff. destruct (Ffree (ff + off) ltac:(lia)) as [b Hb]. unfold restrictv in Hb.
        rewrite fs_footb_true2 in Hb by (fold F; rewrite FS_kFlagsOffset_val, FS_total_val; lia). rewrite view_in in Hb by lia.
        eapply wok_rd_off_image; [lia | exact Hb].
      + repeat (split; [lia|]). split; [constructor|]. split; [|split; [constructor | apply xwords_clear_nil]].
        intros off Hoff. destruct (Fsh (Sh ff + off) ltac:(lia)) as [b Hb]. unfold restrictv in Hb.
        rewrite fs_footb_true3 in Hb by (fold F; rewrite FS_frames_off_val, FS_total_val; lia).
        rewrite view_in in Hb by (unfold Sh, SHADOW_OFF in *; lia).
        eapply wok_rd_off_image; [unfold Sh, SHADOW_OFF in *; lia | exact Hb].
    - unfold N_free. cbn [map carve_obj].
      assert (LC : forall lo hi', (F + 4096 <= lo /\ hi' <= F + 11571200) \/ (2147450880 <= lo /\ hi' <= 17594333495296) ->
                Forall (fun o' => ranges_disjoint (obj_range rhoF o') (lo, hi')) (ss_objs (ax_S (Cgen hi NW c [] (F_K c))))).
      { intros lo hi' Hlh. eapply (loop_objs_clear c A rho0 i rhoF _ _ vHINT); [exact Hc | exact HG | exact HR | exact Htop | exact Hsm | reflexivity | cbn; unfold F_K, F_geom, F_winB, pre_facts; destruct hi; cbn; tauto | fold F; rewrite FS_total_val; lia]. }
      unfold carved.
      apply Forall_cons; [rewrite obj_range_mk by lia; cbn [fst snd ob_base]; rewrite EFL; apply LC; lia|].
      apply Forall_cons; [rewrite obj_range_mk by lia; cbn [fst snd ob_base]; rewrite EFF; apply LC; lia|].
      apply Forall_cons; [rewrite obj_range_mk by lia; cbn [fst snd ob_base]; rewrite EFF; apply LC; lia|].
      apply Forall_cons; [rewrite obj_range_mk by lia; cbn [fst snd ob_base]; rewrite Esh; apply LC; unfold Sh, SHADOW_OFF in *; lia|].
      apply Forall_nil.
    - unfold N_free. cbn [map carve_obj pairwise_disjoint]. unfold carved.
      repeat split; repeat apply Forall_cons; try apply Forall_nil; try exact I; unfold ranges_disjoint;
        rewrite !obj_range_mk by lia; cbn [fst snd ob_base]; rewrite ?EFL, ?EFF, ?Esh; lia. }
  clear H1.

  change (Cfree hi c) with (ax_with_facts (mkAX (Cfree0 c) [] base_sv) ((F_K c ++ F_found hi c) ++ ss_facts (ax_S (Cgen hi NW c [] [])))).
  eapply SPA_refacts; [exact H2 | exact Hfb |].
  intros Hold. rewrite <- app_assoc. apply Forall_app. split.
  {   apply Forall_forall. intros p Hp. apply (proj1 (Forall_forall _ _) Hold). cbn. unfold F_K in Hp. cbn in Hp. tauto. }
  apply Forall_app. split.
  2:{ apply Forall_forall. intros p Hp. apply (proj1 (Forall_forall _ _) Hold). cbn. right. right. exact Hp. }
  unfold F_found. pose proof (urange (rw rhoF 12%positive)) as R12.
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & _). fold F in G2, G3.

  destruct hi; unfold win_hyp in Hwin; fold F in Hwin; rewrite ?FS_total_val in Hwin; unfold F_win, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, IMG_HI in Hwin |- *;
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds].
  all: remember (ffx c) as e; cbn [eval]; subst e; rewrite ?add_val, ?EFF; rewrite ?u64_lit by lia; try lia.
  all: try (rewrite Z.mod_small by lia; lia).
Qed.

Definition spec_range (rho : valuation) (k : carve_spec) : Z * Z := ltac2:(tb__ "0|5|
S5S5S5S13S0A2M0S0A2M1S7S5S5S0S6A2S13A2A1M2A2S5S0S0A2M3Lk;Vk;G1G2G1G3Lp;R2G0S0G0G3Lp0;R2S13S0S3S0S0S3dS4cQ40S1bVrho;R2A2A2M4R1A2S3dG4R3A2A4Llo;Lbase;X5x1Lhi;Lp0;X5x1Lcs;Lp;X5x1").
Definition spec_covered (k : carve_spec) : Prop := ltac2:(tb__ "0|5|
S5S5S5S13S0A2M0S0A2M1S7S5S5S0S6A2M2S13A2M3A1M4A2OLk;Vk;G1G4G1OLp;R2G0S0G0OLp0;R2S13S0S0S37S3cR2R1A2S3eR1R4A2A2S3aS0S0S3aS6S6S3aS13S13S37SbbG3S3G2S13S3S0S6R3R2A4R1A4RaA3S37S3cR3R5A2S3eR5S3dR3S40R2A1A2A2A2A2Le;A2Ln;A2Lo;A2F_;Foff;Llo;Lbase;X5x1Lhi;Lp0;X5x1Lcs;Lp;X5x1").
Definition spec_small (k : carve_spec) : Prop := ltac2:(tb__ "0|4|
S5S5S5S13S0A2M0S0A2M1S7S5S5S0S6A2S13A2A1M2A2OLk;Vk;G1G2G1OLp;R2G0S0G0OLp0;R2S13S0S37S3cS49S41Z2Z3eA2M3A1R1A2S37S3cR1R3A2S37S3eR3G3A2SdeR1R3R5A3A2A2A2Llo;Lbase;X5x1Lhi;Lp0;X5x1Lcs;Lp;X5x1").

Lemma view_eq_cells : ltac2:(tb__ "0|6|
S15S4bQ40M0A1SdS4bQ8A1A1M1F_;M2G2S0S7S5S5S0S6A2M3S13A2M4A1S0S0SdbR7R6R4R3A4SdbR8R6R5R4A4S0S37S3cR5R1A2S3eR1R4A2A2S3aS0S0S3aS6S6S3aS13S13S37SbbG4S3G3S13S3S0S6R3R2A4R1A4RaA3S37S3cR3R5A2S3eR5S3dR3S40R2A1A2A2A2A2Le;A2Ln;A2Lo;A2F_;Foff;S0S37S3cR6R1A2S3eR1R5A2A2S38G1RbS4aG0S3dR9R2A2A2M5A1RaG5A1A3F_;Foff;F_;F_;F_;Fhi;Flo;Fcs;Fb;Frdv2;Frdv1;Frho;").
Proof.
  intros rho rdv1 rdv2 b cs lo hi_ H1 H2 Hcov off Hoff.
  destruct (Hcov off Hoff) as (o & n & e & Hin & Ho).
  pose proof (proj1 (Forall_forall _ _) H1 _ Hin) as C1. pose proof (proj1 (Forall_forall _ _) H2 _ Hin) as C2. cbn zeta in C1, C2.
  specialize (C1 (Z.to_nat (off - o)) ltac:(lia)). specialize (C2 (Z.to_nat (off - o)) ltac:(lia)).
  replace (b + o + Z.of_nat (Z.to_nat (off - o))) with (b + off) in C1, C2 by lia. rewrite C1, C2. reflexivity.
Qed.

Fixpoint zseq (lo : Z) (n : nat) : list Z := match n with O => [] | S n' => lo :: zseq (lo + 1) n' end.
Lemma in_zseq : ltac2:(tb__ "0|0|
S0S6S0S3bSbbS0R1Sb0R3R2A2A3S37S3cR3R1A2S3eR1S3dR3S40R2A1A2A2A2A2Fz;Fn;Flo;").
Proof.
  intros lo n. revert lo. induction n as [|n IH]; intros lo z; cbn [zseq].
  - split; [intros []|lia].
  - rewrite Nat2Z.inj_succ. split.
    + intros [<-|H]; [lia|]. apply IH in H. lia.
    + intros H. destruct (Z.eq_dec lo z); [left; lia|right]. apply IH. lia.
Qed.
Definition coverb (k : carve_spec) : bool := ltac2:(tb__ "0|5|
S5S5S5S13S0A2M0S0A2M1S7S5S5S0S6A2M2S13A2M3A1M4A2S9Lk;Vk;G1G4G1S9Lp;R2G0S0G0S9Lp0;R2S13S0SbcS0S0SbdG3G3G3S9Lc;R1G2S13G2S9Lp;R2S0S6S12S47R2R6A2S48R6S3dR2S40R1A1A2A2A2Ln;Lo;X5x1Ls;Lp;X5x1Lc;R6A3Loff;Sb0R1S44S3fR3R1A2A1A2A3Llo;Lbase;X5x1Lhi;Lp0;X5x1Lcs;Lp;X5x1").
Lemma coverb_sound : ltac2:(tb__ "0|0|
S5dS38S9SabR1A1SaA3SadR2A1F_;Fk;").
Proof.
  intros [[[base lo] hi_] cs] H off Hoff. unfold coverb in H.
  pose proof (proj1 (forallb_forall _ _) H off ltac:(apply in_zseq; lia)) as X.
  apply existsb_exists in X as ([[o n] e] & Hin & Hb). apply andb_prop in Hb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
  exists o, n, e. auto.
Qed.

Lemma absorb_specs_view : ltac2:(tb__ "0|a|
S15S21S7SbeA1M0Se5SbfS7S14A1M1G1S7S5dA1S4bQ40M2A1SdS4bQ8A1A1M3F_;S27Vsegs;R9R8S3G0Sd1R7Sd2R6R5A2A4A4S38G1S1dR9A1SbS14R5R4A3A3S5dSbbS5dR1R5A3S37SbbS14S5eR2A1R7A3S37SaeR2A1S37SadR2A1SdbRdR5S3fSfS0S0Sa9RdR2A2A3S5S5S5S13S0A2M4S0A2M5S7S5S5S0S6A2S13A2A1M6A2M7S0Lk;R2G5G6G5S0Lp;R2G4S0G4S0Lp0;R2S13S0R1Llo;Ls;X5x1Lz;Lp0;X5x1Ll;Lp;X5x1A2G7G6Lk;R2G5G6G5G6Lp;R2G4S0G4G6Lp0;R2S13S0R5Lz0;Ls;X5x1Lz;Lp0;X5x1Lcs;Lp;X5x1A4A2A2A2F_;Fk;S0S5dSbbS5dR1R7A3S37S3cSfS0S0Sa9RfR2A2M8A3R3A2S3eR3S10S0S0G8A3A2A2S38G3SdcVsegs;S19Sd9R10RaRdA3A1S4aG2R4A2M9A3R8G9A1A3F_;F_;Fk;Fz;F_;F_;F_;Frdv;FN;FR;Fobjs;Fmd;Fms;Ftr;FS;Frho;").
Proof.
  intros rho S tr ms md objs R N rdv Hsm Ho HN z k Hk Hz.
  destruct (HN k Hk) as (HinR & Hsmall & Hcov & Hciv). destruct k as [[[base lo] hi_] cs]. cbn [spec_range fst snd] in Hz, Hciv.
  destruct Hsmall as (S1 & S2 & S3 & S4).
  replace (bv_unsigned (eval rho base) + lo - lo) with (bv_unsigned (eval rho base)) in Hciv by lia.
  destruct (absorb_carved_cells segs rho S tr ms md objs R base lo hi_ cs Hsm Ho HinR ltac:(lia) ltac:(lia) ltac:(lia) S4) as [C _].
  rewrite eval_absorb in C |- * || idtac.
  replace z with (bv_unsigned (eval rho base) + (z - bv_unsigned (eval rho base))) by lia.
  apply (view_eq_cells (rho_absorb rho R ms) _ rdv (bv_unsigned (eval rho base)) cs lo hi_); [exact C | | exact Hcov | lia].

  unfold cells_in_view in *. apply Forall_forall. intros [[o n] e] Hin j Hj. rewrite eval_absorb. exact (proj1 (Forall_forall _ _) Hciv _ Hin j Hj).
Qed.

Definition N_fixed (c : Z) : list carve_spec := removelast (N_rt c).
Lemma N_fixed_ok : ltac2:(tb__ "0|0|
S0S38S7S14A1Se0S5dS14S5eSa1R1A1A4S7fA3Fc;").
Proof. intros. reflexivity. Qed.
Lemma N_fixed_coverb : ltac2:(tb__ "0|0|
S0S38S9SbcS5dSabSa1R1A1A3SaA3Fc;").
Proof. intros. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma N_fixed_small : ltac2:(tb__ "0|0|
S0SdfS5dSaeSa1R1A1A3Fc;").
Proof.
  intros c. unfold N_fixed, N_rt. cbn [removelast]. unfold spec_small.
  repeat apply Forall_cons; try apply Forall_nil; (split; [lia|]); (split; [lia|]); (split; [lia|]); unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia.
Qed.

Lemma rt_civ : ltac2:(tb__ "0|5|
S4eS0S15S7S4bQ40M0A1M1A1SbfS37S3cZ0R4A2S3eR4ZbA2A2VAInv;R6R4R3R2A4S38G1S16R5P97A2S4aG0S55S4fR7A1A1A2A3S38G1S16R6P98A2S4aG0S51S4fR8A1A1A2A3S38G1S16R7P99A2S4aG0S54S4fR9A1A1A2A3S38G1S16R8P9aA2S4aG0S53S4fRaA1A1A2A3S38G1S16R9P9bA2S4aG0S50S4fRbA1A1A2A3S38G1S16RaP9cA2S4aG0S52S4fRcA1A1A2A3SdfS5dS5dS5S5S5S13S0A2M2S0A2M3S7S5S5S0S6A2S13A2A1M4A2OLk;R1G3G4G3OLp;R2G2S0G2OLp0;R2S13S0SdbR12SdcVsegs;S19R12A1A2S4cG0S1bR12R2A2A2R5A4Llo;Lbase;X5x1Lhi;Lp0;X5x1Lcs;Lp;X5x1Lk;Sa1RcA1A3F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Ftp;Frho;Fc;FA;").
Proof.
  intros A c rho tp md Hc HA E151 E152 E153 E154 E155 E156.
  pose proof HA as (HG & HR & HF & HRest & HM).
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & TG).
  unfold N_fixed, N_rt. cbn [removelast]. unfold vT, vCTX, vTOP, vBOT, vFSB, vDTLS, vHINT.
  repeat apply Forall_cons; try apply Forall_nil; lazy beta iota zeta; cbn [eval]; rewrite ?E151, ?E152, ?E155, ?E156, ?u64_lit by lia.
  all: unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?E151, ?E152, ?E153, ?E154, ?E155, ?E156; civ_any2 HR.
Qed.

Definition idxs_sm : list nat := ltac2:(tb__ "0|1|
SbS6S4S6U0S4S6U20S4S6U21S4S6U1S4S6U2S8S6A1M0A3A3A3A3A3SbS6Se2U3U1cA2S4S6U1fS4S6U22G0A3A3A3A3").
Definition facts_E (c : Z) : ltac2:(tb__ "0|0|
S7S18A1") := ltac2:(tb__ "0|0|
SbS18SbS18S61Vc;A1S70Vhi;Vc;A2A3SbS18S4S18S28S1aPcA1S17Sc5Vc;A1A1A2S8S18A1A3S71Vhi;A1A3A3").
Definition hexp : sv := SAlu ALU_ADD vH (SLit 1).
Definition R_sm (c : Z) : list sobj := ltac2:(tb__ "0|1|
SbS14S66Vc;Sb5A2S4S14S79Vc;Z1A2S4S14S7cVc;S74S44S42S42Sc5Vc;A1Z8M0A2G0A2A1A1A2S8S14A1A3A3A3").
Definition kept_sm (c : Z) : list sobj := ltac2:(tb__ "0|4|
S4S14S72S4S14S7bVc;S4S5S5S0S6A2M0S13A2M1S3G0S13S3S0S6Z18U8M2A4S1aPaA1A4S8G1A1M3A3A2S4S14S7aVc;S4G1S3G0S13S3S0S6S3fSc5Vc;A1Z8A2G2A4S64Vc;A1A4G3A3A2S4S14S9aS4S14S9bS8S14A1A3A3A3A3A3").
Definition st2s (c : Z) : sstate := ltac2:(tb__ "0|0|
S1cS8fS8dVc;A2S6dVc;A1Sc0S1eSeS13A1SbS14Sa7Vc;A1Sb4Vc;A1A3Sa6Vc;A1S63ScA9").
Definition st3 (c : Z) : sstate := ltac2:(tb__ "0|0|
S1cS8fS8dVc;A2S6dVc;A1Sc0S1eSeS13A1Sa7Vc;A1Sa6Vc;A1S63ScA9").
Definition st4 (c : Z) : sstate := ltac2:(tb__ "0|4|
S1cS8fS8dVc;A2S6dVc;A1Sc0S1eSeS13A1SbS14Sa7Vc;A1S4S14SddS64Vc;A1Z0M0Z1M1S4S5S5S0S6A2M2S13A2M3S3G2S13S3S0S6G0U1A4S17G1A1A4S8G3A1A3A4S8S14A1A3A3Sa6Vc;A1S63ScA9").
Definition st5 (c : Z) : sstate := ltac2:(tb__ "0|1|
SebSb9Vc;A1M0SeaS1dG0A1S4S6U0S4S6U1S4S6U2S4S6U5S4S6U3S4S6U4S8S6A1A3A3A3A3A3A3A2A2").
Definition st6 (c : Z) : sstate := ltac2:(tb__ "0|1|
S1cS8fS8dVc;A2Sc2Sc4S59A1S4S5S6S13A2M0S3S6S13UaS68Vc;A1A4S8G0A1A3A2Sc0S1eSeS13A1S1dSbaVc;A1A1Sa6Vc;A1S63ScA9").
Definition X6 (c : Z) : axst := ltac2:(tb__ "0|1|
S88SafVc;A1S4S5S13S13A2M0S3S13S13S68Vc;A1S17Sc5Vc;A1A1A4S8G0A1A3S9cA3").
Definition s_fin (c : Z) : wsub := ltac2:(tb__ "0|0|
Se3Sc1SafVc;A1S85S99S8dVc;A2A1A3").

Lemma zero_cells_in : ltac2:(tb__ "0|1|
S6S6Se4R1R2A2SbbS5S5S0S6A2M0S13A2S3G0S13S3S0S6S45Z8S40R2A1A2U8A4S17Z0A1A4S74R3A1A3F_;Fm;Fk;").
Proof.
  induction k as [|k IH]; intros m Hm; [lia|]. cbn [zero_cells].
  destruct (Nat.eq_dec m k) as [->|Hne]; [left; reflexivity | right; apply IH; lia].
Qed.
Lemma nth_enc8_zero : ltac2:(tb__ "0|5|
S15S6Se4R1U8M0A2S38S4bQ8M1A1M2Se1G2R2S2aG0S1bR3S17Z0M3A1A2A2S4aG1G3A2M4A4G4A3F_;Fj;Frho;").
Proof. intros rho j Hj. do 8 (destruct j as [|j]; [reflexivity|]). lia. Qed.

Definition img_zone_okb (k : carve_spec) : bool := ltac2:(tb__ "0|7|
S5S5S5S13S0A2M0S0A2M1S7S5S5S0S6A2S13A2A1M2A2S9Lk;Vk;G1G2G1S9Lp;R2G0S0G0S9Lp0;R2S13S0S13S9Ls;R2S0S0S9Lz;R1ScbS0Sf0Sf1SefSeeA2R1A2La;R2S3fR4R2A2A3S1SaLp1;M3G3X0x3Lz;S1SaLi;Sd4S13S13SaLb;La;M4Lop;M5G5Sd5G4Lop;M6G6S9S2S13SaLa;Lw;Lsgn;S1S13S0SaLk0;Li;Ll0;X13x8Llo;Ls;X5x1Lhi;Lp0;X5x1Ll;Lp;X5x1").
Lemma N_fixed_img_zone : ltac2:(tb__ "0|0|
S0S38S9SbcS5dSb6Sa1R1A1A3SaA3Fc;").
Proof. intros. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma N_fixed_zone : ltac2:(tb__ "0|1|
S0S4eS15S0S15S5dS0S37S3cZ0R7A2S3eR7ZbA2A2SceS4fR7A1A1Sa0R8R9R7R6R5A5SbbS5dR5Sa1RaA1A3S37S3cSfS0S0Sa9R7R6A2M0A3R5A2S3eR5S10S0S0G0A3A2A2SedS4fRbA1R6A2F_;F_;F_;F_;F_;Fa;Fk;Frho;Fi;Frho0;FA;Fc;").
Proof.
  intros c A rho0 i rho k a Hc HG HR Hk Ha.
  pose proof HR as (R1 & R2 & R3 & R4 & R5 & R6 & _).
  pose proof (geom_numsS _ HG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & _). pose proof (topG_range (aa_geom A)) as TG.
  pose proof (proj1 (forallb_forall _ _) (N_fixed_img_zone c) k Hk) as IZ.
  unfold N_fixed, N_rt in Hk. cbn [removelast In] in Hk. unfold vT, vCTX, vFSB, vDTLS in Hk. unfold rt_zone.
  repeat (destruct Hk as [E|Hk];
    [subst k; cbn [spec_range fst snd eval] in Ha; rewrite ?R1, ?R2, ?R5, ?R6, ?u64_lit in Ha by lia;
     first [ left; split; [unfold IMG_HI; lia|]; unfold img_zone_okb in IZ;
             eapply (forall_rangeZ_ok (fun a0 => cells_footb (rtc_cells_img RTC_A G0) a0)); [exact IZ | lia]
           | right; lia ]
    |]).
  destruct Hk.
Qed.

End SM.
