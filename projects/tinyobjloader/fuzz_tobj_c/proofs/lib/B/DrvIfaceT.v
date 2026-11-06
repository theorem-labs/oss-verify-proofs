(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nil"; "nat"; "prod"; "app"; "bool"; "snd"; "andb"; "fst"; "length"; "list"; "option"; "true"; "None"; "false"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "sobj"; "cell"; "sprop"; "SPUle"; "mkCell"; "mkObj"; "DUnknown"; "SVar"; "DImage"; "rw"; "sv_eqb"; "SPAlign"; "DList"; "FcsrFrm0"; "SAlu"; "SPEq"; "mkSS"; "ob_base"; "ob_lo"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "add"; "mul"; "pow"; "sub"; "opp"; "land"; "div"; "eqb"; "ltb"; "modulo"; "of_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf"; "add"; "O_cflag"; "O_file0"; "O_realv"; "O_sbuf0"; "O_ssp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT"; "sp0"; "vB"; "vCap"; "vA1"; "DEEP"; "vClen"; "vL3"; "vLen"; "vPlen"; "vA0"; "vL1"; "S_T"; "clen_of"; "payload"; "vL0"; "vTID"; "vTOPv"; "vTP"; "ATOPHI"; "IMGHI"; "K_T"; "O_a1p"; "O_afl1"; "O_arg1"; "O_buf"; "O_deep"; "O_errno0"; "O_ferr0"; "O_glxT"; "O_hdr2"; "O_mainfr"; "O_rds"; "O_realfw"; "O_realrd"; "O_stage2"; "O_stderrp"; "O_tri0"; "PreF"; "V_T"; "X_T"; "arg1_facts"; "bd_T"; "exit_statics"; "facts_T"; "flags_of"; "fps_statics"; "fregs_T"; "hdr_word"; "objs_T"; "regs_T"; "spM"; "top_facts"; "tv_T"; "vFlg"; "vGL1"; "vGL2"; "vH"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Lists.ListDef"; "nth"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT.TAddr"; "TP"; "RD_STAGE"; "TR_INIT"; "free_stub"; "main_entry"; "tr_entry"; "tr_ra"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "axwf"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface"; "cz"; "FERR"; "O_afl2b"; "O_atx0"; "O_cov"; "O_dso"; "O_dtf"; "O_fin"; "O_fina"; "O_nlkx"; "O_ofl"; "O_regf"; "O_tid"; "O_uerr"; "O_uout"; "O_xlk"; "Pre_exit"; "exit_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "BIc"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget"; "MAX_INPUT"; "NCALLS"; "CK0"; "CK_DIV"; "CV"; "CV0"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "A_globals"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.HandoffMain"; "RA_MAIN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st"; "O_cfsl"; "O_realmc"; "O_realsn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "X_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface"; "O_aglob"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ANone"; "NDA"; "@Stdlib.Bool.Bool"; "Is_true"; "@Stdlib.Lists.List"; "combine"; "find"; "@stdpp.base"; "filter"; "@stdpp.decidable"; "Is_true_dec"; "@stdpp.list_basics.list"; "list_filter"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Budget Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.HandoffMain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nb.Icpt_memchr_st OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module TAddr.
  Definition main_entry : Z := 0x8c524.
  Definition tr_entry : Z := 0x8c7f4.
  Definition tr_ra : Z := 0x8c698.
  Definition loop_head : Z := 0x8c8ac.
  Definition RD_STAGE : Z := 0x610710.
  Definition fz_stub : Z := 0x8c9c4.
  Definition malloc_stub : Z := 0x5e1f4.
  Definition free_stub : Z := 0x5e1f0.
  Definition memcpy_stub : Z := 0x5c9dc.
  Definition read_stub : Z := 0x4d2cc.
  Definition EMPTY : Z := 0x620720.
  Definition TR_INIT : Z := 0x620710.
  Definition TP : Z := 0x621278.
  Definition HSE : Z := 0x10007fff8000.
End TAddr.
Import TAddr.

Definition sp0 : sv := SVar 1.
Definition spM : sv := add sp0 (SLit (-128)).
Definition spT : sv := add sp0 (SLit (-208)).
Definition vA0 := SVar 4.  Definition vL0 := SVar 5.
Definition vA1 := SVar 8.  Definition vL1 := SVar 9.
Definition vL3 := SVar 10.
Definition vSSP := SVar 15. Definition vTID := SVar 16. Definition vTP := SVar 24.
Definition vTOPv := SVar 30.
Definition ATOPHI : Z := 140737479966720.
Definition IMGHI : Z := 0x643000.
Definition vB := SVar 40. Definition vCap := SVar 41. Definition vLen := SVar 42. Definition vClen := SVar 43.
Definition vPlen := SVar 44. Definition vH := SVar 45. Definition vFlg := SVar 46.
Definition vGL1 := SVar 47. Definition vGL2 := SVar 48.

Definition top_facts : list sprop := ltac2:(tb__ "0|2|
S0S15S16S21Sa1S1aP1A1S11N800000A1A3M0S1aP1eA1M1A2S0S15S16G1G0A2S0S15S16S11Z7fff7f800000A1G1A2S0S15S16G1S11Z7fffff800000A1A2S2S15A1A3A3A3A3").
Definition payload : sv := ltac2:(tb__ "0|0|
S34S34S3bS11Z6A1A2S3fA2").
Definition DEEP : Z := 65408.

Definition O_deep : sobj := ltac2:(tb__ "0|0|
S18S3aS11S2dS29S3eZ80A2A1A1S11N80A1S2S14A1S19A5").

Definition O_mainfr : sobj := ltac2:(tb__ "0|3|
S18S3aS11N80A1S11N30A1S0S14S17S11N78A1Z8M0S11Z0A1M1A3S0S14S17S11N70A1G0G1A3S0S14S17S11N68A1G0G1A3S0S14S17S11N60A1G0G1A3S0S14S17S11N58A1G0S34S34S3aS11Z10A1M2A2G2A2A3S0S14S17S11N50A1G0S11S7eA1A3S0S14S17S11N48A1G0S11Z2A1A3S0S14S17S11N40A1G0S34S3aS11G0A1A2A3S0S14S17S11N38A1G0S11Sa4A1A3S2S14A1A3A3A3A3A3A3A3A3A3S19A5").
Definition O_stage2 : sobj := ltac2:(tb__ "0|3|
S18S3aS11N30A1M0S11Z0A1M1S0S14S17G0Z8M2S34S3aS11G2A1A2A3S0S14S17S11N28A1G2G1A3S0S14S17S11N20A1G2G1A3S0S14S17S11N18A1G2G1A3S0S14S17S11N10A1G2G1A3S0S14S17S11N8A1G2G1A3S2S14A1A3A3A3A3A3A3S19A5").
Definition O_hdr2 : sobj := ltac2:(tb__ "0|2|
S18S3aS11Z0A1M0S11Z10A1S0S14S17G0Z8M1S11Z2A1A3S0S14S17S11G1A1G1S43A3S2S14A1A3A3S19A5").
Definition O_a1p : sobj := ltac2:(tb__ "0|1|
S18S3aS11Z10A1M0S11Z18A1S0S14S17G0Z8S3dA3S2S14A1A3S19A5").

Definition O_str0 : sobj := ltac2:(tb__ "0|0|
S18S43S11Z0A1S34S48S11Z1A1A2S2S14A1S1fP2A1A5").
Definition O_arg1 : sobj := ltac2:(tb__ "0|0|
S18S3dS11Z0A1S40S2S14A1S1fP3A1A5").
Definition X_str0 : (sv * sv) := ltac2:(tb__ "0|0|
S1S12S12S43S34S48S11Z1A1A2A4").
Definition X_arg1 : (sv * sv) := ltac2:(tb__ "0|0|
S1S12S12S3dS40A4").

Definition O_errno : sobj := ltac2:(tb__ "0|0|
S18S11Z0A1S11S2cS7aZa4A2A1S11S2cS7aZa0A2A1S2S14A1S19A5").

Definition O_errno0 : sobj := ltac2:(tb__ "0|1|
S18S11Z0A1S11S2cS7aZa4A2A1M0G0S2S14A1S19A5").
Definition O_tri0 : sobj := ltac2:(tb__ "0|0|
S18S11Z0A1S11S7cA1S11S29S7cZ14A2A1S2S14A1S1bA5").
Definition O_tri1 : sobj := ltac2:(tb__ "0|2|
S18S11Z0A1S11S7cA1M0S11S29S7cZ14A2A1S0S14S17G0Z1M1S11G1A1A3S2S14A1A3S1bA5").
Definition O_buf : sobj := ltac2:(tb__ "0|1|
S18S3bS11Z0A1M0S3cS0S14S17G0Z4S72A3S2S14A1A3S19A5").

Definition O_stderrp : sobj := ltac2:(tb__ "0|0|
S18S11Z0A1S11Ze47c0A1S11Ze47c8A1S2S14A1S1bA5").

Definition O_ferr0 : sobj := ltac2:(tb__ "0|0|
S18S11Z0A1S11S86A1S11S29S86Ze8A2A1S2S14A1S1bA5").
Definition O_realrd : sobj := ltac2:(tb__ "0|1|
S18S11Z0A1S11Ze6648A1M0S11Ze6650A1S0S14S17G0Z8S11Ze0304A1A3S2S14A1A3S1bA5").
Definition O_realfw : sobj := ltac2:(tb__ "0|0|
S18S11Z0A1S11Ze6650A1S11Ze6658A1S2S14A1S1bA5").

Definition O_afl1 : sobj := ltac2:(tb__ "0|0|
S18S11Z0A1S11Zeb8b8A1S11Zeb8e4A1S0S14S17S11Zeb8d0A1Z4S11Z1A1A3S2S14A1A3S19A5").

Definition O_glxT : sobj := ltac2:(tb__ "0|2|
S18S11Z0A1M0S11Zeb930A1S11Zeb980A1S0S14S85Zeb938Z8M1S11Z60A1A3S0S14S85Zeb940G1S70A3S0S14S85Zeb948G1S71A3S0S14S85Zeb970G1G0A3S2S14A1A3A3A3A3S19A5").
Definition exit_statics : list sobj := ltac2:(tb__ "0|0|
S0S13S92S0S13S93S0S13S8cS0S13S8fS0S13S88S0S13S94S0S13S8eS0S13S90S0S13S8bS0S13S8aS0S13S8dS0S13S50S0S13S87S0S13S56S0S13Sa9S0S13S89S2S13A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition fps_statics : list sobj := ltac2:(tb__ "0|0|
S0S13Sa6S0S13Sa7S0S13Sa5S2S13A1A3A3A3").

Definition O_rds : sobj := ltac2:(tb__ "0|0|
S18S11Z0A1S11S7bA1S11S29S7bZ10000A2A1S2S14A1S19A5").
Definition X_rds : (sv * sv) := ltac2:(tb__ "0|0|
S1S12S12S11S7bA1S11Z10000A1A4").
Definition objs_T : list sobj := ltac2:(tb__ "0|1|
S5S13S0S13S53S0S13S58S0S13S5cS0S13S57S0S13S4fS0S13S51S0S13S54S0S13S91S0S13S5eS0S13S52S0S13S36S0S13S38S0S13S35S0S13S37S0S13S5bS0S13S5aS0S13S39S0S13S5dS0S13S55S2S13A1M0A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S5S13S67S5S13S64S5S13S0S13S59G0A3Sa2A3A3A3A3").

Definition X_T : list (sv * sv) := ltac2:(tb__ "0|1|
S5S4S12S12A2M0S0G0S1S12S12S11Z14d80A1S11Z40A1A4S0G0S1S12S12S34S3aS11S2dS29S3eZ80A2A1A1A2S11S3eA1A4S0G0S1S12S12S3bS3cA4S2G0A1A3A3A3Sa8A3").
Definition X_Tg : list (sv * sv) := X_T ++ X_main.

Definition arg1_facts : list sprop := ltac2:(tb__ "0|2|
S0S15S16S11Z7fff80000020A1S3dA2S0S15S16S34S3aS11Z20A1A2S3dA2S0S15S16S3dS11S2bZ2M0Z2fA2A1M1A2S0S15S16S34S3dS40A2G1A2S0S15S16S11Z1A1S44A2S0S15S16S44S11ZfffA1A2S0S15S16S34S44S11Z8A1A2S40A2S0S15S16S40S11S2bG0Z16A2A1A2S2S15A1A3A3A3A3A3A3A3A3").
Definition facts_T : list sprop := ltac2:(tb__ "0|9|
S5S15S0S15S1eP1Z4M0A2S0S15S16S11Z7fff80000000A1S3aA2S0S15S16S3aS11S2cS2bZ2M1Z2fA2Ze0A2A1A2S0S15S22S4bS11S7aA1A2S0S15S1eP28M2G0A2S0S15S1eG2Z3A2S0S15S16S11Z1000A1S3bA2S0S15S16S34S3bS3cA2M3S11S4cA1M4A2S0S15S16S3bG4A2S0S15S16S11S4dA1S3bA2S0S15S16G3S4aA2S0S15S16S3bS4aA2S0S15S16S11Z10000A1S3cA2S0S15S16S3cS11S2bG1Z1aA2A1M5A2S0S15S16S41S3cA2S0S15S16S34S34S3fS42A2S11Z6A1M6A2M7S41A2S0S15S16S41G7A2S0S15S16S34S3fG6A2M8S41A2S0S15S16G8S3cA2S0S15S16S42S41A2S0S15S16S3fS11Z7fffA1A2S0S15S16S42G5A2S0S15S16S11Z1A1S49A2S0S15S16S49S11Z3fffffA1A2S2S15A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S5S15S6dS62A3A3").

Definition regs_T : list sv := ltac2:(tb__ "0|2|
S0S12S11Z0A1M0S0S12S11S80A1S0S12S6cS0S12S11Z10800A1S0S12S4bS0S12S1aP3dA1S0S12S1aP3eA1S0S12S1aP3fA1S0S12S34S3bS11Z2A1A2M1S0S12S3bS0S12G1S0S12S3fS0S12S47S0S12S42S0S12S1aP36A1S0S12S1aP37A1S0S12S1aP38A1S0S12S1aP39A1S0S12S3fS0S12S47S0S12S42S0S12S6fS0S12S11S7bA1S0S12G0S0S12G0S0S12G0S0S12G0S0S12G0S0S12S1aP3aA1S0S12S1aP3bA1S0S12S1aP40A1S0S12S1aP41A1S2S12A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Definition fregs_T : list sv := repeat (SLit 0) 32.

Definition S_T : axst := ltac2:(tb__ "0|0|
S84S23S7fS6bS68S20SeS12A1S6aS65SabSfA9S61S11Sa3A1A3").

Lemma S_T_wf : ltac2:(tb__ "0|0|
S77S76S6S83S45A1SdA3S76S6S26S81S45A1A1SdA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition hdr_word (F : list byte) : Z := ltac2:(tb__ "0|3|
S29S29S29S73Q8M0S78S74G0A1M1U0VF;S75G0Z0A2M2A4A2S2aZ100S73G0S78G1U1VF;G2A4A2A2A2S2aZ10000S73G0S78G1U2VF;G2A4A2A2A2S2aZ1000000S73G0S78G1U3VF;G2A4A2A2A2").
Definition clen_of (F : list byte) : Z := ltac2:(tb__ "0|3|
S29S73Q8M0S78S74G0A1M1U0VF;S75G0Z0A2M2A4A2S2aZ100S2eS73G0S78G1U1VF;G2A4A2Z7fA2A2A2").
Definition flags_of (F : list byte) : Z := bv_unsigned (nth 1 F (Z_to_bv 8 0)).
Definition calls_of (F : list byte) : Z := ltac2:(tb__ "0|3|
S6S27L_;S30S46VF;A1Z0M0A2Z1M1S29S2eS73Q8M2S78S74G2A1U2VF;S75G2G0A2A4A2Z3A2G1A2X6x2").
Definition P0f_T (F : list byte) (rho : valuation) : Prop := ltac2:(tb__ "0|5|
S77S76S27S73Q40M0S1cVrho;P18A2A2S7aA3S77S76S27S73G0S1cVrho;P2aA2A2S33SaS74Q8A1VF;A2A1M1A3S77S76S27S73G0S1cVrho;P2bA2A2S46VF;A1M2A3S77S76S27S73G0S1cVrho;P2cA2A2S2cS2cG1Z6A2G2A2A3S77S76S27S32S73G0S1cVrho;P2dA2A2S2bZ2M3Z20A2A2S69VF;A1A3S76S27S73G0S1cVrho;P2eA2A2S6S27L_;S31S66VF;A1M4Z80A2G4S2cS29G4S2bG3Z40A2A2Z100A2X6x2A3A2A2A2A2A2").

Definition V_T : Z := ltac2:(tb__ "0|0|
S29S2bZ2Z1aA2S2aS9cS29S2aS9fS9bA2Sa0A2A2A2").
Definition K_T : Z := ltac2:(tb__ "0|0|
S29Z3S2aS9cS29S2fS9bS9eA2S9dA2A2A2").
Definition bd_T : list bitem := ltac2:(tb__ "0|2|
S0S97S98Z1M0Z0M1S60A3S0S97S98G1G0S2aS99S4eA2A3S2S97A1A3A3").

Definition tv_T : list (sv * sv) := ltac2:(tb__ "0|1|
S0S4S12S12A2M0S1S12S12S3bS3cA4S2G0A1A3").
Definition nd_T : ndesc := ltac2:(tb__ "0|0|
SadS6eS2S4S4S12S27A2S12A2A1S63SacA4").

Definition PreF : axst := Pre_free AE_A [] UStopLe.
Definition PostF : axst := L_free AE_A [] UStopLe.
Definition s_ex (C : axst) (n c : Z) : wsub := ltac2:(tb__ "0|0|
S9aP1S81VC;A1S81S95Vn;Vc;A2A1A3").
Definition N_ex : list (Z * Z * list (Z * nat * Z)) := ltac2:(tb__ "0|e|
S0S4S4S27S27A2M0SbS4S4S27S3A2M1S27A2M2A1M3A2M4S1G0G3S1S27S27Z7fffc570Z7fffc758A4S2G2A1M5A4S0G4S1G0G3S1S27S27Z80015238Z80015540A4G5A4S0G4S1G0G3S1S27S27Zed91cM6Zed91dA4S0G2S1G1S27S1S27S3G6U1M7A4Z1M8A4G5A3A4S0G4S1G0G3S1S27S27Zeed98M9Zeed9aA4S0G2S1G1S27S1S27S3G9G7A4G8A4S0G2S1G1S27S1S27S3Zeed99G7A4G8A4G5A3A3A4S0G4S1G0G3S1S27S27Z17fc60MaZ17fc68A4S0G2S1G1S27S1S27S3GaU8MbA4ZffffffffffffffffA4G5A3A4S0G4S1G0G3S1S27S27Ze6778McZe6788A4S0G2S1G1S27S1S27S3GcGbA4Zdac00A4S0G2S1G1S27S1S27S3Ze6780GbA4Zdb004A4G5A3A3A4S0G4S1G0G3S1S27S27Zeb90dMdZeb90eA4S0G2S1G1S27S1S27S3GdG7A4G8A4G5A3A4S2G4A1A3A3A3A3A3A3A3").

Definition dropX (r : sv * sv) (A : axst) : axst := ltac2:(tb__ "0|2|
SaaVA;Sb1S4S12S12A2M0SbG0A1Sb3G0A1G0SaeS10S8S1dS9S12S12Vr;A3S9S12S12R1A3A2S1dS7S12S12Vr;A3S7S12S12R1A3A2A2A1M1A1Lr';G0Sb2G1A1Lx;S82VA;A1A6A2").

Definition locate (objs : list sobj) (b lo : sv) : nat := ltac2:(tb__ "0|3|
ScS4S3S13A2M0A1S3Lx;Sb0G0G0S8S1dS24S7S3S13R1A3M1A1Vb;A2S1dS25G1A1Vlo;A2A2Lio;SafS3S13S79U0M2SaS13Vobjs;A2A2Vobjs;A4A3G0G0S3Lp;R1S3S13R2Ls;Li;X4x1Lp;G2Xcx2").

Definition CUTS_X : list Z := ltac2:(tb__ "0|0|
S0S27S7dS0S27S96S0S27Z8c718S2S27A1A3A3A3").
Definition FUEL_X : nat := 80%nat.

Definition O_deepM : sobj := ltac2:(tb__ "0|0|
S18S3aS11S2dS29S3eZ80A2A1A1S11Nd0A1S2S14A1S19A5").
Definition O_deepS : sobj := ltac2:(tb__ "0|0|
S18S3aS11S2dS29S3eZ80A2A1A1S11N80A1S2S14A1S19A5").

Definition s_fb (C : axst) : wsub := ltac2:(tb__ "0|1|
S0S4S28S12A2M0S1S28S12PfS11S2dS3eA1A1A4S0G0S1S28S12PdS3cA4S9aP1S81VC;A1S81S5fA1A3A3A3").
