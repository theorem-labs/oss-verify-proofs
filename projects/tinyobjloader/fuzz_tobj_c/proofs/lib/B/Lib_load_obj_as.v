(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "pair"; "true"; "bool"; "nil"; "prod"; "Some"; "app"; "option"; "length"; "list"; "andb"; "negb"; "snd"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "sv"; "SPUle"; "SVar"; "sobj"; "SAlu"; "sprop_eqb"; "ss_facts"; "ss_objs"; "cell"; "sprop_below"; "ss_next"; "mkCell"; "sv_eqb"; "swf"; "DUnknown"; "SMd"; "SPBranch"; "SPEq"; "SPUlt"; "mkObj"; "mkSS"; "ob_base"; "ob_lo"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_regs"; "ss_resv"; "sstate"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "apply_axforms"; "AXSplit"; "AXMerge"; "AXRebase"; "AXUnbase"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "la_state"; "leafA"; "ax_X"; "ax_base"; "axwf"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_as"; "pST"; "oidx"; "T_s1f"; "pSL"; "spA"; "E_s1"; "E_s2"; "E_si"; "s1A"; "K_s"; "R_s1"; "R_s2"; "s_s1"; "s_s2"; "T_s1f0"; "T_s1n0"; "T_s2n0"; "T_s2y0"; "pSI"; "sel_front"; "vSL"; "B_s1f"; "B_s1n"; "B_s2n"; "B_s2y"; "K_sB"; "T_s1n"; "T_s2n"; "T_s2y"; "cutsS"; "exitsS"; "pEr"; "sB_facts"; "xf_si0"; "xfb_s1"; "xfb_s2"; "H_ecertS_ok"; "O_midS"; "keep_ecertS_ok"; "ra_si"; "xf_s1"; "xf_si"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "nd_below"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "ndA1"; "RL"; "VLA"; "z0"; "ndX0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "vLEN"; "NP"; "optL"; "O_Dlo"; "vBUF"; "vDp"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "combine"; "filter"; "find"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "txt"; "X_latch"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_as.NT"; "Pre_nt"; "P_found"; "P_nf"; "Posts_nt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_as.SI"; "Pre_si"; "P_none"; "P_num"; "Posts_si"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "spm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efnode"; "V_below"; "ejcertAF"; "@Corelib.Lists.ListDef"; "map"; "seq"; "nth"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_tidy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_postA"; "call_checkA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA"; "pinA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "V_B"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_avn"; "PhisV"; "cps_arm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_disp"; "E_nt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop.LOLAddr"; "c_si";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA"; "hideN"; "hide_set"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require HideA.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAFb OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.TobjJAH OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.HideA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_scan_int.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_hv0 Lib_load_obj_bud Lib_load_obj_exits Lib_load_obj_loopE Lib_load_obj_armkit Lib_load_obj_armkit2 Lib_load_obj_avn Lib_load_obj_aus.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr HVAddr.
Module NT. Include OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.Lib_next_token. End NT.
Module SI. Include Lib_scan_int. End SI.
Import NT.NextTokenAddr SI.ScanIntAddr.

Definition oidx (b lo : sv) (T : axst) : nat := ltac2:(tb__ "0|3|
S9S6S1S16A2M0A1S1Lx;S7fG0G0ScS1fS28SeS1S16R1A3M1A1Vb;A2S1fS29G1A1Vlo;A2A2Lp;S7dS1S16S90U0SaS16S1aS38VT;A1A1M2A2A2G2A4A3G0G0S1Lp;R1S1S16R2Ls;Li;X6x1Lp;U3e7X9x2").
Definition spA : sv := SVar 10.
Definition s1A : sv := SAlu ALU_ADD spA (SLit (-640)).

Definition sel_front (sel : list nat) (n : nat) : axform := ltac2:(tb__ "0|0|
S36S8S1Vsel;S7eS1S1SdS7bS1Sa5R1A1Vsel;A3A1Li;S90U0Vn;A2A3A3A1").

Definition xf_s1 : list axform := ltac2:(tb__ "0|2|
S0S30S33U3A1S0S30S32U6S11N10A1A2S0S30S32U4M0S11N70A1A2S0S30S35G0N78A2S0S30S32U2M1S11N120A1A2S0S30S35G1N128A2S5S30A1A3A3A3A3A3A3").
Definition E_s1 : axst := Eval vm_compute in optL (apply_axforms E_nt xf_s1).
Definition s_s1 : wsub := ltac2:(tb__ "0|0|
S99PaS38S44A1S38S82A1A3").
Definition R_s1 : list sobj := Eval vm_compute in optR (entails_frA E_s1 NT.Pre_nt s_s1).
Definition T_s1n0 : axst := Eval vm_compute in ax_add_facts (ss_facts (ax_S E_s1)) (import_postA s_s1 NT.Pre_nt NT.P_nf E_s1 R_s1).
Definition T_s1f0 : axst := Eval vm_compute in ax_add_facts (ss_facts (ax_S E_s1)) (import_postA s_s1 NT.Pre_nt NT.P_found E_s1 R_s1).

Definition xfb_s1 (T : axst) : list axform := ltac2:(tb__ "0|2|
S0S30S34U3A1S0S30S34U4A1S0S30S32U1M0S11Z8A1A2S5S30A1M1A3A3A3SbS30A1S77S31VT;R1A2A1S37SaS16S1aS38R1A1A1A2S1S8S30R3S0S30S52S0S1S40S43S11N128A1R2A3S0S1S40S43S11N120A1R2A3S0S1S40S43S11N78A1R2A3S0S1S40S43S11N70A1R2A3S0S1S40S47S7aR2A3S0S1S40S47S11N10A1R2A3S5S1A1A3A3A3A3A3A3R1A2S0S30S33U0A1S0S30S33G0A1S0S30S33U2A1G1A3A3A3A3A3Tn;TT1;Tpre;").
Definition B_s1n : axst := Eval vm_compute in optL (apply_axforms T_s1n0 (xfb_s1 T_s1n0)).
Definition B_s1f : axst := Eval vm_compute in optL (apply_axforms T_s1f0 (xfb_s1 T_s1f0)).
Definition T_s1n : axst := Eval vm_compute in ax_tidy B_s1n.
Definition T_s1f : axst := Eval vm_compute in ax_tidy B_s1f.
Definition pST : sv := SVar 641. Definition pSL : sv := SVar 642. Definition pSI : sv := SVar 643. Definition vSL : positive := 642%positive.

Lemma as_checks1 : ltac2:(tb__ "0|5|
S10SfS9S37A1M0S31S9fS67A2S7S37S44A2A3S10SfS9SbS16A1M1A1S96S44S82S4bA3S7G1S49A2A3S10SfS4S95S44S82S4bS49S8fS3aS37S39S85A4A5S3A3S10SfS4S9bS76S1dS38S44A1M2A1M3A2S3A3S10SfS4S6cG3S70A2S3A3S10SfS4S7cS12S1cG3A1S19G2A1M4A3S3A3S10SfS37S8bG4S94S4bS82S84S44S49A5A2S4eA3S10SfS37S8bG4S94S4bS82S83S44S49A5A2S4dA3S10SfG0S31S4eS61S4eA1A2S7S37S55A2A3S10SfS37S93S55A1S59A3S10SfG0S31S4dS61S4dA1A2S7S37S54A2A3S10SfS37S93S54A1S41A3SfS4S8dG3S98A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition K_s (t : Z) : axst := ltac2:(tb__ "0|1|
S8bS0S12S14S80S3fA1S11Z800000000000A1A2S0S12S14S17S6dS3fS11Vt;A1M0A3S75A2S5S12A1A3A3S97S41S53G0A3A2").

Definition pEr : sv := SAlu ALU_ADD pPOS pLNL.
Definition sB_facts : list sprop := ltac2:(tb__ "0|2|
S0S12S14S80S3fA1S11Z800000000000A1A2S0S12S14S11Z4A1M0S42A2S0S12S14S17S6dS3fG0A3M1S5eA2S0S12S14G1S75A2S0S12S14S17S6dS3fS42A3S75A2S5S12A1A3A3A3A3A3").
Definition K_sB : axst := ax_add_facts sB_facts T_s1f.

Lemma as_checks_split : ltac2:(tb__ "0|7|
S10SfS4Sa1S6aS3L_;S38S41A1M0A2S3A3S10SfS4S7cS69S69S20S38S97S41S53S11R1A1M1A3A1M2A1Lt;S0S69Z1M3S0S69Z2S0S69Z3S5S69A1A3A3A3M4A3S3A3S10SfS4S7cS12S1cS1dG0A1A1S5fA3S3A3S10SfS4S7cS69S69S7cS12S1cS1dG2A1A1S0S12S14S80S3fA1S11Z800000000000A1A2S0S12S14S17S6dS3fG1A3S75A2S5S12A1A3A3A3Lt;G4A3S3A3S10SfS4S7bS12S18S14S11G3A1S42A2A1S19G0A1M5A3S3A3S10SfS4S7bS12S18S24S17S6dS3fS42A3S51A2A1G5A3S3A3S10SfS4S7bS12S18S14S51S5eA2A1G5A3S3A3S10SfS4S7bS12S18S14S51S75A2A1G5A3S3A3S10SfS4S7bS12S18S14S3fS11Z10000000000A1M6A2A1G5A3S3A3SfS4S7bS12S18S14S42G6A2A1G5A3S3A3A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma K_s_eq : ltac2:(tb__ "0|2|
S69SfS37S48R1A1S9aS97S41S53S11R1A1M0A3M1S8S12S0S12S14S80S3fA1S11Z800000000000A1A2S0S12S14S17S6dS3fG0A3S75A2S5S12A1A3A3S19S38G1A1A1A3A2A3Ft;").
Proof. intros t. reflexivity. Qed.
Lemma K_sB_eq : ltac2:(tb__ "0|0|
SfS37S58S9aS41S8S12S5fS19S38S41A1A1A3A2A3").
Proof. reflexivity. Qed.

Definition ra_si : Z := 0x8e1e0.
Definition O_midS : sobj := ltac2:(tb__ "0|3|
S26S43S11N128A1M0S11N88A1S0S1bS1eG0Z8M1S80S3fA1M2A3S0S1bS1eS11N94A1Z4S11Z0A1A3S0S1bS1eS11N90A1G1G2A3S5S1bA1A3A3A3S21A5").
Definition E_si : axst := ltac2:(tb__ "0|3|
S38S41A1S2fS3eS27Sa0Sa2S2dR1A1S0S6S1S13A2M0S2S1S13U1M1S11S66A1A4S0G0S2S1S13UaS8aZ90A1A4S0G0S2S1S13UbS22S6fS11Z1A1S17S6dS42S80S3fA1A3A3A4S0G0S2S1S13UcS8aZ94A1A4S0G0S2S1S13U5S15P284A1A4S0G0S2S1S13U6S15P285A1A4S0G0S2S1S13U7S15P286A1A4S0G0S2S1S13UdS15P287A1A4S0G0S2S1S13UeS15P288A1A4S0G0S2S1S13UfS15P289A1A4S0G0S2S1S13U10S15P28aA1A4S0G0S2S1S13U11S15P28bA1A4S5G0A1A3A3A3A3A3A3A3A3A3A3A3A3A2S2bR1A1S2aR1A1S2eR1A1S0S16S64S0S16S91S16G1S1aR1A1M2S78A4S0S16S78S92S16U3G2A3A3A3A3S0S12S14S17S6dS3fS42A3S75A2S19R1A1A3P28cS2cR1A1A9S3bS41A1S3cS41A1A3TS;").

Definition xf_si0 : list axform := ltac2:(tb__ "0|4|
S0S30S32U2M0S11N10A1A2S0S30S32U0M1S11N90M2A1A2S0S30S32G1S11N94M3A1A2S0S30S35U1G3A2S0S30S35G0G2A2S5S30A1A3A3A3A3A3").
Definition xf_si (E : axst) : list axform := ltac2:(tb__ "0|1|
S77S31VE;S60A2A1S37S8S30S60S0S30S52S0S1S40S47S11N10A1R1A3S0S1S40S8aZ90A1S11Z0A1M0R1A3S0S1S40S79G0R1A3S0S1S40S8aZ94A1G0R1A3S5S1A1A3A3A3A3SaS16S1aS38R1A1A1A2A2S5S30A1A3A3TT1;").
Definition E_s2 : axst := Eval vm_compute in optL (apply_axforms E_si (xf_si E_si)).

Definition s_s2 : wsub := ltac2:(tb__ "0|1|
S0S6S6aS13A2M0S2S6aS13PfS79A4S0G0S2S6aS13P10S3fA4S0G0S2S6aS13P11S17S6dS3fS42A3A4S0G0S2S6aS13P13S8aZ98A1A4S99PaS38S45A1S38S86A1A3A3A3A3A3").
Definition R_s2 : list sobj := Eval vm_compute in optR (entails_frA E_s2 SI.Pre_si s_s2).
Definition T_s2n0 : axst := Eval vm_compute in ax_add_facts (ss_facts (ax_S E_s2)) (import_postA s_s2 SI.Pre_si SI.P_none E_s2 R_s2).
Definition T_s2y0 : axst := Eval vm_compute in ax_add_facts (ss_facts (ax_S E_s2)) (import_postA s_s2 SI.Pre_si SI.P_num E_s2 R_s2).

Definition xfb_s2 (T : axst) : list axform := ltac2:(tb__ "0|3|
S0S30S34U1M0A1S0S30S34U3A1S5S30A1M1A3A3SbS30A1S77S31VT;R1A2A1S37SaS16S1aS38R1A1A1A2S1S8S30R3S0S30S52S0S1S40S43S11N128A1R2A3S0S1S40S43S11N94A1R2A3S0S1S40S43S11N90A1R2A3S0S1S40S47S7aR2A3S0S1S40S47S11N10A1R2A3S5S1A1A3A3A3A3A3R1A2S0S30S33U0A1M2S0S30G2S0S30S33G0A1G1A3A3A3A3A3Tn;TT1;Tpre;").
Definition B_s2n : axst := Eval vm_compute in optL (apply_axforms T_s2n0 (xfb_s2 T_s2n0)).
Definition B_s2y : axst := Eval vm_compute in optL (apply_axforms T_s2y0 (xfb_s2 T_s2y0)).
Definition T_s2n : axst := Eval vm_compute in ax_tidy B_s2n.
Definition T_s2y : axst := Eval vm_compute in ax_tidy B_s2y.

Lemma as_checks2 : ltac2:(tb__ "0|5|
S10SfS4S20S38S46A1A1S3A3S10SfS4S3dS46A1S3A3S10SfS9S37A1M0S31S46S68S46A1A2S7S37S45A2A3S10SfS9SbS16A1M1A1S96S45S86S4cA3S7G1S4aA2A3S10SfS4S95S45S86S4cS4aS8fS3aS37S39S89A4A5S3A3S10SfS4S9bS76S1dS38S45A1M2A1M3A2S3A3S10SfS4S6cG3S70A2S3A3S10SfS4S7cS12S1cG3A1S19G2A1M4A3S3A3S10SfS37S8bG4S94S4cS86S87S45S4aA5A2S4fA3S10SfS37S8bG4S94S4cS86S88S45S4aA5A2S50A3S10SfG0S31S4fS62S4fA1A2S7S37S56A2A3S10SfS37S93S56A1S5aA3S10SfG0S31S50S62S50A1A2S7S37S57A2A3S10SfS37S93S57A1S5bA3SfS4S8dG3S98A2S3A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition cutsS : list efnode := ltac2:(tb__ "0|7|
S0S6S6S6S37S6bA2M0S1A2M1S6S69S13A2M2A2M3S2G1G2S2G0S1S2S37S6bS59S70A4U1M4A4S2S69S13S71S72ZaS73A2A4M5A4S0G3S2G1G2S2G0S1S2S37S6bS48Z1A1S70A4G4A4G5A4S0G3S2G1G2S2G0S1S2S37S6bS48Z2A1S70A4G4A4G5A4S0G3S2G1G2S2G0S1S2S37S6bS48Z3A1S70A4G4A4G5A4S0G3S2G1G2S2G0S1S2S37S6bS58S70A4G4A4G5A4S0G3S2G1G2S2G0S1S2S37S6bS5aS70A4G4A4S2S69S13S71S72Z5S73A2A4M6A4S0G3S2G1G2S2G0S1S2S37S6bS5bS70A4G4A4G6A4S5G3A1A3A3A3A3A3A3A3").
Definition exitsS : list efnode := ltac2:(tb__ "0|5|
S0S6S6S6S37S6bA2M0S1A2M1S6S69S13A2M2A2M3S2G1G2S2G0S1S2S37S6bS46S70A4U1M4A4S2S69S13S71S72Z7S73A2A4A4S0G3S2G1G2S2G0S1S2S37S6bS81S74A4G4A4S2S69S13S71S72Z1S73A2A4A4S5G3A1A3A3").

Definition keep_ecertS_ok : list sprop := ltac2:(tb__ "0|3|
S0S12S25S15P1ccA1S15P1d3A1M0A2S0S12S14S15P1eaA1S15P1e0A1M1A2S0S12S14G0S15PeA1M2A2S0S12S23S6eS11N1800A1S15P13A1A3S0S12S14G2S11Z4000000A1A2S0S12S14S17S6dG1S15P1e1A1A3G2A2S0S12S14S15PdA1S11Z800000000000A1A2S5S12A1A3A3A3A3A3A3A3").
Definition H_ecertS_ok : list sprop := ltac2:(tb__ "0|0|
Sa4S65S8S8cS5cS5dA3A2").
Lemma ecertS_ok : ltac2:(tb__ "0|1|
SfS4S8eS9cS76S9dUbb8S9eS76S8fS8cS8cSa3S63A1M0S5cA4S8fS8cS8cG0S5dA4A8S3A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
