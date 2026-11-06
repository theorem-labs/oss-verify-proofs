(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "true"; "bool"; "cons"; "nil"; "prod"; "Some"; "option"; "pair"; "list"; "nat"; "andb"; "None"; "app"; "false"; "length"; "negb"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "SLit"; "SPUle"; "SVar"; "sobj"; "ss_pc"; "ss_next"; "sprop_eqb"; "ss_facts"; "sstate"; "reg_sv"; "ss_objs"; "SPEq"; "sprop_below"; "ss_lenient"; "DUnknown"; "cell"; "mkObj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "axst"; "mkLeafA"; "sym_runA"; "ax_X"; "ax_base"; "la_state"; "mkAX"; "entailsA"; "la_reason"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvM_states"; "s_R0"; "C_m65"; "s_m65"; "CUTS_M"; "PreM"; "R_m65"; "runwf"; "nd_M"; "vFD"; "L_R0"; "E_fw"; "E_m65"; "E_m65r"; "E_oom"; "E_op"; "R1"; "R2"; "T_op"; "vBn"; "T_m65null"; "T_m65ok"; "T_op3"; "T_opF"; "C_fw"; "C_m65S"; "E_copen"; "E_ex2"; "L_R0h"; "R3"; "R_fw"; "bd_M0"; "err_facts"; "fd3_facts"; "nd_M1"; "nd_R1"; "r0_hints"; "r0_perm"; "s_fw"; "tv_R1"; "FW2"; "O_winR"; "T_fw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "stop_reason"; "RsFuel"; "instr_at"; "set_objs"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "nth_error"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR"; "bd_R0"; "R_head"; "CAP0"; "S_R0"; "nd_R0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_below"; "ANone"; "NDA"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "nd_tv"; "ndesc"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT"; "vL1"; "vA1"; "vL3"; "vTOPv"; "ATOPHI"; "DEEP"; "IMGHI"; "K_T"; "O_arg1"; "O_deep"; "V_T"; "sp0"; "vTP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf"; "add"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "add"; "mul"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite"; "sp0_factsb"; "drv_xrb"; "robjs_checkD"; "xrs_checkD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "call_checkA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "BIc"; "KU"; "bd_below"; "bd_subst"; "bud_le"; "bud_pay"; "@Corelib.Lists.ListDef"; "map"; "nth"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface"; "exit_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceM.MAddr"; "copen_pc"; "oom1_pc"; "openat_pc"; "usage_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceM"; "S_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT.TAddr"; "malloc_stub"; "TP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "UStopLe"; "V_TOP"; "L_malloc_null"; "L_malloc_ok"; "V_RES"; "ulink";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvErrno"; "errR"; "errR_okb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface"; "Posts_fw"; "Pre_fw"; "fw_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "select"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "pos_add_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "select_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysOpen"; "AT_FDCWD_word"; "O_RD_LARGEFILE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.DrvGlueA"; "set_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysA"; "A_after_fresh"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundW SymSoundM SymSoundR SymComplete SymFrame SymObj SymEntail SymCFG SymSummary SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv ObjUnbase ObjXform TobjJV SysOpen.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Budget Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import BudA TobjJA TobjJAM SysA DrvGlueA DrvGlueB AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceT DrvIfaceR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvJ DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require DrvIfaceM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fm.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e3.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e9.DrvFwIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvJ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fq.DrvSite OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.DrvIfaceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fm.DrvErrno.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr TAddr MAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition CUTS_M : list Z := ltac2:(tb__ "0|0|
S4S12S9fS4S12Sa2S4S12S67S4S12Sa0S4S12S9dS4S12S9eS4S12S9cS4S12Z4d13cS5S12A1A3A3A3A3A3A3A3A3").
Definition runM (fuel : nat) (A : axst) : list leafA := ltac2:(tb__ "0|1|
S8SaS28A1M0A1G0Lx;S2bS5cVfuel;S35VA;S2A5G0R1Ll;S5S28A1X8x2").
Definition nthA (d : axst) (l : list leafA) (i : nat) : axst := ltac2:(tb__ "0|0|
S2eS99S28Vi;Vl;S2aVd;S60A2A4A1").
Definition leaf_info (l : list leafA) : ltac2:(tb__ "0|0|
SaS6S5fS12A2A1") := ltac2:(tb__ "0|0|
S98S28S6S5fS12A2S28S9S5fS12S31R1A1S1aS27S2eR1A1A1A1A4LL;Vl;A4").

Definition bd_M0 : list bitem := ltac2:(tb__ "0|2|
S4S91S92Z1M0Z0M1S85S86S80S84Z2Z1bA2A2Z10000A2A3S4S91S92G1G0S87S93S86S7dZ15A2A2A3S5S91A1A3A3").
Definition nd_M : ndesc := ltac2:(tb__ "0|0|
S6eS5S6S14S14A2A1S5S6S6S14S12A2S14A2A1S50S6dA4").
Definition nd_M1 : ndesc := ltac2:(tb__ "0|0|
S6eS5S6S14S14A2A1S5S6S6S14S12A2S14A2A1S66S6dA4").

Definition LV_M0 : list leafA := Eval vm_compute in runM 200 S_M.
Definition E_op : axst := Eval vm_compute in nthA S_M LV_M0 0.

Definition T_op : axst := Eval vm_compute in A_after_fresh E_op.
Definition vFD : positive := Eval vm_compute in ss_next (ax_S E_op).
Definition fd3_facts : list sprop := ltac2:(tb__ "0|0|
S4S15S21S18S3aA1S16Z3A1A2S5S15A1A3").
Definition T_op3 : axst := Eval vm_compute in ax_add_facts fd3_facts T_op.
Definition LV_M1 : list leafA := Eval vm_compute in runM 200 T_op3.
Definition E_m65 : axst := Eval vm_compute in nthA S_M LV_M1 0.

Definition err_facts : list sprop := ltac2:(tb__ "0|2|
S4S15S17S16S85S84Z2Z40A2M0ZfffA2A1S18S3aA1M1A2S4S15S17G1S16S85G0Z1A2A1A2S5S15A1A3A3").
Definition T_opF : axst := Eval vm_compute in ax_add_facts err_facts T_op.
Definition LV_M1F : list leafA := Eval vm_compute in runM 200 T_opF.
Definition E_copen : axst := Eval vm_compute in nthA S_M LV_M1F 0.

Definition PreM : axst := Pre_malloc AE_A [] UStopLe.

Definition E_m65r : axst := Eval vm_compute in errR E_m65.
Definition C_m65S : sstate := Eval vm_compute in match split_obj_at (ax_S E_m65r) 0 (SLit (-128)) with Some S' => S' | None => ax_S E_m65r end.
Definition C_m65 : axst := ltac2:(tb__ "0|0|
S2fS4aS2cS3eA1S2dS3eA1A3").
Lemma M_errR : ltac2:(tb__ "0|0|
S1S0S3SafS3dA1S2A3S0S29SaeS3dA1S3eA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Definition s_m65 : wsub := Eval vm_compute in (15%positive, SLit (- DEEP)) :: infer_sub 1 (ax_S C_m65) (ax_S PreM).

Definition R_m65 : list sobj := Eval vm_compute in match entails_frA C_m65 PreM s_m65 with Some R => R | None => [] end.
Definition T_m65ok : axst := Eval vm_compute in T_afterA PreM C_m65 s_m65 R_m65 (L_malloc_ok AE_A [] UStopLe).
Definition T_m65null : axst := Eval vm_compute in T_afterA PreM C_m65 s_m65 R_m65 (L_malloc_null AE_A [] UStopLe).
Definition LV_M2 : list leafA := Eval vm_compute in runM 100 T_m65ok.
Definition L_R0 : axst := Eval vm_compute in nthA S_M LV_M2 0.
Definition LV_M2n : list leafA := Eval vm_compute in runM 100 T_m65null.

Definition O_winR : sobj := ltac2:(tb__ "0|0|
S26S83S81S16N80A1A2S16S88S7bA1A1S16Z0A1S5S25A1S24A5").
Definition vBn : positive := Eval vm_compute in match nth 10 (ss_regs (ax_S T_m65ok)) (SLit 0) with SVar v => v | _ => 1%positive end.
Definition tv_R1 : list (sv * sv) := ltac2:(tb__ "0|1|
S4S6S14S14A2M0S9S14S14S18S44A1S16Z10000A1A4S5G0A1A3").
Definition nd_R1 : ndesc := ltac2:(tb__ "0|0|
S6eS58S5S6S6S14S12A2S14A2A1S66S6dA4").

Definition r0_hints : list sprop := ltac2:(tb__ "0|3|
S4S15S17S18S44A1M0S16S7aA1M1A2S4S15S17S83G0S16S68A1A2M2G1A2S4S15S17S16Z1000A1G0A2S4S15S17S16S7cA1G0A2S4S15S17G2S79A2S4S15S17G0S79A2S4S15S17S16Z1A1S76A2S4S15S17S76S16ZfffA1A2S5S15A1A3A3A3A3A3A3A3A3").
Definition R1 : sstate := Eval vm_compute in set_obj_at (ax_S L_R0) 0 O_deep.

Definition r0_perm : list nat := Eval vm_compute in
  map (fun o => locate (ss_objs R1) (ob_base o) (ob_lo o)) (map (fun o => match o with mkObj b lo hi cs d => mkObj (match b with SVar 40%positive => SVar vBn | _ => b end) lo hi cs d end) objs_R0).
Definition R2 : sstate := Eval vm_compute in set_objs R1 (select (ss_objs R1) r0_perm).
Definition R3 : sstate := Eval vm_compute in add_facts r0_hints R2.
Definition L_R0h : axst := ltac2:(tb__ "0|0|
S2fS4eS2cS3bA1S2dS3bA1A3").
Definition s_R0 : wsub := Eval vm_compute in infer_sub 1 (ax_S L_R0h) (ax_S S_R0).

Definition E_oom : axst := Eval vm_compute in nthA S_M LV_M2n 0.
Definition LV_M3 : list leafA := Eval vm_compute in runM 50 E_oom.
Definition E_fw : axst := Eval vm_compute in nthA S_M LV_M3 0.

Definition N_fw : list lcarve := ltac2:(tb__ "0|8|
S4S6S6S12S12A2M0SaS6S6S12SbA2M1S12A2M2A1M3A2M4S9G0G3S9S12S12Zf20d8M5Zf20daA4S4G2S9G1S12S9S12SbG5U1M6A4Z1M7A4S4G2S9G1S12S9S12SbZf20d9G6A4G7A4S5G2A1A3A3A4S5G4A1A3").
Definition FW1 : sstate := Eval vm_compute in match split_obj_at (ax_S E_fw) 0 (SLit (- D_FW)) with Some x => x | None => ax_S E_fw end.
Definition FW2 : sstate := Eval vm_compute in
  mkSS (ss_pc FW1) (setregs (ss_regs FW1) [(4%nat, SLit TP)]) (ss_fregs FW1) (ss_fcsr FW1) (ss_resv FW1) (ss_objs FW1 ++ map lc_obj N_fw) (ss_facts FW1) (ss_next FW1) (ss_lenient FW1).
Definition C_fw : axst := ltac2:(tb__ "0|0|
S2fS59S2cS3cA1S2dS3cA1A3").
Definition s_fw : wsub := Eval vm_compute in infer_sub 1 (ax_S C_fw) (ax_S (Pre_fw 0x14d77 19)).

Definition R_fw : list sobj := Eval vm_compute in match entails_frA C_fw (Pre_fw 0x14d77 19) s_fw with Some R => R | None => [] end.
Definition T_fw : axst := Eval vm_compute in T_afterA (Pre_fw 0x14d77 19) C_fw s_fw R_fw P_fw.
Definition LV_M4 : list leafA := Eval vm_compute in runM 50 T_fw.
Definition E_ex2 : axst := Eval vm_compute in nthA S_M LV_M4 0.

Lemma M_runs : ltac2:(tb__ "0|6|
S1S0S8SaS28A1M0A1M1S2bS5cUc8M2S35Sa1S2A5S7G0S4S28S2aS40S5eA2S5S28A1M3A3A2A3S1S0S12S1aS27S40A1A1S9fA3S1S0G1S2bS5cG2S35S47S2A5S7G0S4S28S2aS3dS5eA2G3A3A2A3S1S0S12S1aS27S3dA1A1Sa2A3S1S0G1S2bS5cG2S35S48S2A5S7G0S4S28S2aS4bS5eA2G3A3A2A3S1S0S12S1aS27S4bA1A1S9dA3S1S0G1S2bS5cU64M4S35S46S2A5S7G0S4S28S2aS3bS5eA2G3A3A2A3S1S0S12S1aS27S3bA1A1S67A3S1S0G1S2bS5cG4S35S45S2A5S7G0S4S28S2aS3fS5eA2G3A3A2A3S1S0S12S1aS27S3fA1A1S9eA3S1S0G1S2bS5cU32M5S35S3fS2A5S7G0S4S28S2aS3cS5eA2G3A3A2A3S1S0S12S1aS27S3cA1A1Sb2A3S1S0G1S2bS5cG5S35S5bS2A5S7G0S4S28S2aS4cS5eA2G3A3A2A3S0S12S1aS27S4cA1A1S9cA3A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition runwf (A : axst) (nd : ndesc) : bool := ltac2:(tb__ "0|2|
ScScS74S6bS1bS27VA;A1M0A1M1A2S11S23G0A1A1A2S6cG1Vnd;A2A2").
Lemma runwf_sound : ltac2:(tb__ "0|2|
S29S73S0S3S38R2R1A2S2A3S1S0S3S74S6bS1bS27R3A1M0A1M1A2S2A3S1S0S3S23G0A1SfA3S0S3S6cG1R2A2S2A3A2A2F_;Fnd;FA;").
Proof.
  intros A nd H. unfold runwf in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  split; [exact H1|]. split; [destruct (ss_lenient (ax_S A)); [discriminate | reflexivity] | exact H3].
Qed.
Lemma M_wf : ltac2:(tb__ "0|0|
S1S0S3S38Sa1S39A2S2A3S1S0S3S38S47S39A2S2A3S1S0S3S38S48S39A2S2A3S1S0S3S38S46S54A2S2A3S1S0S3S38S45S53A2S2A3S0S3S38S3fS53A2S2A3A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma M_open : ltac2:(tb__ "0|6|
S1S0S29SbdS40A1S43A3S1S0S29Sa4S52S43A2S47A3S1S0S29Sa4S51S43A2S48A3S1S0S13S3aS1bS27S40A1M0A1A3S1S0S13S1bS27S43A1A1S75S3aA1M1A3S1S0S8S9aA1S61S5cS1aG0A1A2S7S9aS9bA2A3S1S0S14S1fG0Z11A2S16Z38A1A3S1S0S14S1fG0ZaA2S16Sb9A1A3S1S0S14S1fG0ZcA2S16SbaA1A3S1S0S14S1fG0ZbA2S77A3S1S0S8S19A1S65S19S20G0A1U4A3S7S19S7eA2A3S1S0S3S74S6bS3aA2S2A3S1S0S3S6cS3aS39A2S2A3S1S0S3S6cG1S39A2S2A3S1S0S3S64S15S22G1A1M2S52A3S2A3S1S0S3S64S15G2S51A3S2A3S1S0S3S63S15S1cS17S76S16Z1ffffA1A2A1S1dG0A1M3A3S2A3S1S0S3S63S15S1cS17S83S77S78A2S16S84Z2M4Z2fA2A1M5A2A1G3A3S2A3S1S0S3S63S15S1cS17S77G5A2A1G3A3S2A3S1S0S3S63S15S1cS17S83S76S16Z8A1A2S78A2A1G3A3S2A3S0S3S63S15S1cS17S78S16S84G4Z16A2A1A2A1G3A3S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma M_malloc : ltac2:(tb__ "0|d|
S1S0S8S1eA1Sb6S27S3eA1U0S16N80A1A3S7S1eS4aA2A3S1S0S8SaS19A1M0A1S8eS33S36S34A3S7G0S37A2A3S1S0S3S8dS33S36S34S37S4S29SaaSa7S5SadA1M1Sa8A3M2S4S29SabSa7G1Sa8A3M3S5S29A1M4A3M5A3A5S2A3S1S0S3S8dS33S36S34S37S4S29G2G4A3A5S2A3S1S0S3S8dS33S36S34S37G5A5S2A3S1S0S3Sa6S6bS34A2S2A3S1S0S3S74S6bS1bS27S33A1M6A1M7A2S2A3S1S0S3S6cG7S39A2S2A3S1S0S3S94G7S66A2S2A3S1S0S14S5dS34PcA2S16Z10000A1M8A3S1S0S14S5dS90S34S36G3S33A4SacA2S18Sb7G7UaA2M9A1A3S1S0S13G9S44A3S1S0S3S97S1dG6A1MaG8S93S50S66A5S2A3S1S0S3S89GaA1S2A3S1S0S3S8bGaS5S6S14S14A2A1MbSdSbA1McS37A4S2A3S1S0S3S8cGaGbGcS20G6A1S8aS2cS33A1A6S2A3S1S0S29Sa5S36S33S34S37G2A5S45A3S0S29Sa5S36S33S34S37G3A5S46A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma M_r0 : ltac2:(tb__ "0|f|
S1S0S8S19A1S65S19S20S27S3bA1M0A1U0M1A3S7S19S5aA2A3S1S0S1eSbcG0G1S7fA3S41A3S1S0S3Sb3G0S41A2S2A3S1S0S3S89S1dG0A1M2A1S2A3S1S0S3Sb8S10S19S20S41A1M3A2S56A2S2A3S1S0S1eS62S41Sb5G3S56A2A2S42A3S1S0S1eSb4S55S42A2S4eA3S1S0S3S64S15S22S1bS42A1M4A1SeS15S55S1dS42A1M5A3A3S2A3S1S0S13G4S1bG0A1A3S1S0SaS15A1G5G2A3S1S0S3S63S15S1cS17S16Z1000A1S18S44A1A2A1G2A3S2A3S1S0S3S63S15S1cS21S82S16Sa3A1A2A1S1dS27S4dA1M6A1M7A3S2A3S1S0S3S89G7A1S2A3S1S0S3S30S4dS69S32A3S2A3S1S0S14S5dS32P18M8A2S18G8A1A3S1S0S14S5dS32P9M9A2S18G9A1A3S1S0S14S5dS32P1MaA2S18GaA1A3S1S0S14S5dS32PbMbA2S18GbA1A3S1S0S14S5dS32Sa9A2S18Sa9A1A3S1S0S14S5dS32PaMcA2S18GcA1A3S1S0S3S74S6bS1bG6A1MdA2S2A3S1S0S3S6cGdS54A2S2A3S1S0S3SbbS32S58S72S6aA1A3S2A3S1S0S3S71S32S5S6S6S14S12A2S14A2A1MeGeA3S2A3S1S0S3S96G7S95S32S66A2S66A3S2A3S0S3S6fS70S32S6dA2S6dA2S2A3A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Lemma M_fw : ltac2:(tb__ "0|2|
S1S0S8SaS19A1M0A1S8eS49Sb1Z14d77Z13A2M1S57A3S7G0S4fA2A3S0S3S8fS49G1S57S4fS98S28S29S2eSb0A4A5S2A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
