(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "app"; "prod"; "pair"; "list"; "bool"; "option"; "Some"; "None"; "true"; "false"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sprop"; "sobj"; "SPUle"; "SVar"; "SPAlign"; "rm"; "DUnknown"; "FcsrFrm0"; "SPBranch"; "SPEq"; "SPNot"; "cell"; "mkObj"; "mkSS"; "rl"; "swf"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Sh"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "mul"; "div"; "sub"; "of_nat"; "opp"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "FdEntry"; "Model"; "m_fds"; "m_fs"; "FdChannel"; "VmState"; "event"; "with_fds"; "FdDir"; "FdFile"; "fd_insert"; "fd_lookup"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT"; "vB"; "vA1"; "sp0"; "vL3"; "DEEP"; "vL1"; "vTID"; "vTOPv"; "vTP"; "ATOPHI"; "IMGHI"; "K_T"; "O_a1p"; "O_arg1"; "O_deep"; "O_errno0"; "O_ferr0"; "O_hdr2"; "O_mainfr"; "O_rds"; "O_realfw"; "O_realrd"; "O_stage2"; "O_stderrp"; "O_tri0"; "V_T"; "X_rds"; "arg1_facts"; "exit_statics"; "fps_statics"; "fregs_T"; "spM"; "top_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceR"; "Uv"; "CAP0"; "S_R0"; "argsX_facts"; "std_fds"; "vAL"; "KcG"; "O_buf0"; "R_head"; "SHR"; "SHR2"; "SHRZ"; "SHRZ2"; "SLK1"; "TOPV"; "X_R0"; "ZARG"; "bd_R0"; "facts_R0"; "objs_R0"; "open_entry"; "regs_R0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf"; "add"; "O_cflag"; "O_file0"; "O_realv"; "O_sbuf0"; "O_ssp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "bitem"; "BIc"; "KU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "with_vm"; "Kc_ok"; "@LinuxProcessSemantics.LinuxProcessSem.Fs"; "Fs"; "path_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT.TAddr"; "TP"; "RD_STAGE"; "@Corelib.Init.Nat"; "add"; "@Corelib.Lists.ListDef"; "firstn"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi"; "dot_path"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "A_globals"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface"; "O_tid"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa"; "SH0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "X_lits"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axwf"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "aceil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ANone"; "NDA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require RegGlobIface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require na.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require DrvIfaceT DrvTLXa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.HandoffMain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Drv_printf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.RegGlobIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.na.DrvExitIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvIfaceT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.DrvTLXa OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import PFAddr TAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition R_head : Z := 0x8c5f0.
Definition CAP0 : Z := 65536.

Definition O_buf0 : sobj := ltac2:(tb__ "0|0|
S1bS3cSeZ0A1SeS5eA1S1S1aA1S15A5").

Definition objs_R0 : list sobj := ltac2:(tb__ "0|1|
S2S10S0S10S4aS0S10S4eS0S10S52S0S10S4dS0S10S48S0S10S49S0S10S4bS0S10S88S0S10S54S0S10S64S0S10S75S0S10S77S0S10S74S0S10S76S0S10S51S0S10S50S0S10S78S0S10S53S0S10S4cS1S10A1M0A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S2S10S59S2S10S58S2S10S0S10S4fG0A3S86A3A3A3A3").

Definition X_R0 : list (sv * sv) := ltac2:(tb__ "0|1|
S2S3SdSdA2M0S0G0S4SdSdSeZ14d80A1SeZ40A1A4S0G0S4SdSdS73S3eSeS2dS26S40Z80A2A1A1A2SeS40A1A4S0G0S4SdSdS3cSeS5eA1A4S0G0S56S1G0A1A3A3A3A3S8aA3").

Definition vAL : sv := SVar 11.
Definition argsX_facts : list sprop := ltac2:(tb__ "0|2|
S0SfS11S73S3dS3fA2S73S3eS62A2M0A2S0SfS11G0SeS28Z2M1Z2fA2A1A2S0SfS11S62SeS28G1Z17A2A1A2S1SfA1A3A3A3").
Definition arg1_factsM : list sprop := ltac2:(tb__ "0|2|
S2SfS0SfS11SeZ7fff80000020A1S3dA2S0SfS11S73S3eSeZ20A1A2S3dA2S0SfS11S3dSeS28Z2M0Z2fA2A1M1A2S0SfS11S73S3dS3fA2G1A2S0SfS11S41SeZ1ffffA1A2S0SfS11S73S41SeZ8A1A2S3fA2S0SfS11S3fSeS28G0Z16A2A1A2S1SfA1A3A3A3A3A3A3A3S60A3").

Definition CST_drv2 : list (Z * Z) := ltac2:(tb__ "0|1|
S0S3S23S23A2M0S4S23S23Z16080Z40A4S0G0S4S23S23Z1ee40Z80A4S1G0A1A3A3").

Definition facts_R0 : list sprop := ltac2:(tb__ "0|4|
S2SfS0SfS13P1Z4M0A2S0SfS11SeZ7fff80000000A1S3eA2S0SfS11S3eSeS2bS28Z2Z2fA2Ze0A2A1A2S0SfS18S44SeS80A1A2S0SfS13P28M1G0A2S0SfS13G1Z3A2S0SfS11SeZ1000A1S3cA2S0SfS11S73S3cSeS5eA1A2M2SeS45A1M3A2S0SfS11S3cG3A2S0SfS11SeS46A1S3cA2S0SfS11G2S43A2S0SfS11S3cS43A2S0SfS19S17S85S3cSeZ0A1A3A1S0SfS11SeZ1A1S42A2S0SfS11S42SeZ3fffffA1A2S1SfA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S2SfS5cS2SfS57S60A3A3A3").

Definition regs_R0 : list sv := ltac2:(tb__ "0|1|
S0SdSeZ0A1M0S0SdS12P3cA1S0SdS5bS0SdSeZ10800A1S0SdS44S0SdS12P3dA1S0SdS12P3eA1S0SdS12P3fA1S0SdSeZ2A1S0SdS3cS0SdS12P32A1S0SdS12P33A1S0SdS12P34A1S0SdS12P35A1S0SdS12P36A1S0SdS12P37A1S0SdS12P38A1S0SdS12P39A1S0SdS3dS0SdG0S0SdSeZ3A1S0SdSeS5eA1S0SdSeS81A1S0SdS3cS0SdG0S0SdG0S0SdG0S0SdG0S0SdS12P3aA1S0SdS12P3bA1S0SdS12P40A1S0SdS12P41A1S1SdA1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Definition S_R0 : axst := ltac2:(tb__ "0|0|
S8dS1cS65S72S5aS16S9SdA1S70S6fS8eSbA9S6cSeS87A1A3").

Lemma S_R0_wf : ltac2:(tb__ "0|0|
S1fS20S6S8cS5fA1SaA3S20S6S1eS8bS5fA1A1SaA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Definition bd_R0 : list bitem := ltac2:(tb__ "0|3|
S0S79S7aZ1M0Z0M1S2bS26S55S28Z2M2Z1bA2A2S29G2Z10000A2A2A3S0S79S7aG1G0S29S7bS26S47Z14A2A2A3S1S79A1A3A3").
Definition nd_R0 : ndesc := ltac2:(tb__ "0|1|
S91S0S3SdSdA2M0S4SdSdS3cSeS5eA1A4S1G0A1A3S1S3S3SdS23A2SdA2A1S6eS90A4").

Definition SHRZ (z : Z) : Prop := ltac2:(tb__ "0|0|
S21S1fS25S24Z21440A1Vz;A2S27Vz;S24Z214c0A1A2A2S21S1fS25S24Z16080A1Vz;A2S27Vz;S24Z16100A1A2A2S1fS25S24Z1a780A1Vz;A2S27Vz;S24Z1a800A1A2A2A2A2").

Definition SHR (r : valuation) : Prop := ltac2:(tb__ "0|2|
S1fS89Vr;A1S23S68R1A1S20S7S2fQ8M0A1M1A1S14Vr;S2eQ40R2A2A2S8G1S2eG0Z0A2A2A3F_;Fz;A2").
Definition Uv (r : valuation) (v : positive) : Z := bv_unsigned (rw r v).

Definition ZARG (r : valuation) : Prop := ltac2:(tb__ "0|5|
S1fS25Z7fff80000000S5dVr;P1A2M0A2S1fS25S26G0S5dVr;PbA2A2M1S28Z2Z2fA2A2S23S1fS25S29S2aS24G0A1Z8M2A2G2A2R1A2S27R1S26S29S2aS24S2bG1Z1A2A1G2A2G2A2G2A2A2A2S20S7S2fQ8M3A1M4A1S14Vr;S2eQ40R2A2A2S8G4S2eG3Z0A2A2A3F_;Fz;A2A2").

Lemma ZARG_pcl : ltac2:(tb__ "0|2|
S23S23S23S25Z7fff80000000R3A2S25S26R4R3A2S28Z2Z2fA2M0A2S1fS25S29S2aS24R5A1Z8M1A2G1A2R3A2S27R3S26S29S2aS24S2bS26R5R4A2Z1A2A1G1A2G1A2G1A2A2A2S22S23S23S1fS25Z0R1A2S1fS1fS25S8fR1A2S27R1G0A2A2S20S23R5S24R1A1A3A2A2Lx;A2F_;F_;F_;Fz;Fal;Fsp;").
Proof.
  intros sp al z Hsp Hal Hz. unfold Sh, SHADOW_OFF in *.
  pose proof (Z.div_mod (sp / 8 + 2147450880) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (sp / 8 + 2147450880) 8 ltac:(lia)).
  pose proof (Z.div_mod sp 8 ltac:(lia)). pose proof (Z.mod_pos_bound sp 8 ltac:(lia)).
  assert (U : (sp + al - 1) / 8 <= 2 ^ 44 - 1).
  { replace (2 ^ 44 - 1) with ((2 ^ 47 - 1) / 8) by reflexivity. apply Z.div_le_mono; lia. }
  assert (U2 : ((sp + al - 1) / 8 + 2147450880) / 8 <= (2 ^ 44 - 1 + 2147450880) / 8) by (apply Z.div_le_mono; lia).
  change ((2 ^ 44 - 1 + 2147450880) / 8) with (2 ^ 41 + 268431359) in U2.
  exists (8 * (z - 2147450880)). unfold TobjJV.aceil. split; [lia|]. split; [lia|].
  rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

Definition SHRZ2 (z : Z) : Prop := ltac2:(tb__ "0|0|
S21S1fS25S24Z16080A1Vz;A2S27Vz;S24Z160c0A1A2A2S1fS25S24Z1ee40A1Vz;A2S27Vz;S24Z1eec0A1A2A2A2").
Definition SHR2 (r : valuation) : Prop := ltac2:(tb__ "0|2|
S23S69R1A1S20S7S2fQ8M0A1M1A1S14Vr;S2eQ40R2A2A2S8G1S2eG0Z0A2A2A3F_;Fz;").

Definition TOPV (r : valuation) : Prop := ltac2:(tb__ "0|0|
S20S23S26S5dVr;P1eA2Z800000A2S5dVr;P1A2A3").

Definition SLK1 (r : valuation) : Prop := ltac2:(tb__ "0|0|
S25S26S5dVr;P9A2Z11A2S5dVr;PaA2A2").
Definition P0Z (argv1 : list byte) (r : valuation) : Prop := ltac2:(tb__ "0|3|
S1fS20S23S5dVr;P18A2S80A3S1fS66Vr;A1S1fS20S5S2fQ8M0A1M1A1S83G1S82ScG1Vargv1;A2M2U1A2S1dVr;P3A2A3S2G1Vargv1;S0G1S2eG0Z0A2S1G1A1A3A3A3S1fS20S23S5dVr;P9A2S2cG2A1A3S1fS1fS6dVr;A1S67Vr;A1A2S1fS6bVr;A1S6aVr;A1A2A2A2A2A2A2").

Definition std_fds : list (word * FdEntry) := ltac2:(tb__ "0|6|
S0S3S2fQ40M0A1M1S30A2M2S4G1S30S2eG0Z0A2M3S34G3A1A4S0G2S4G1S30S2eG0Z1A2M4S34G4A1A4S0G2S4G1S30S2eG0Z2A2M5S34G5A1A4S1G2A1A3A3A3").
Definition open_entry (p : list byte) : FdEntry := ltac2:(tb__ "0|0|
S6S30L_;S7fVp;S84A2S38S39Vp;S2eQ40Z0A2A2X6x2").
Definition FD3 (p : list byte) : list (word * FdEntry) := ltac2:(tb__ "0|0|
S3aS61S2eQ40Z3A2S71Vp;A1A3").

Definition KcG (T0 : list event) (MDX : Model -> Prop) (fds : list (word * FdEntry)) (evs : list event) : KcA := ltac2:(tb__ "0|1|
S5S36A1M0S31S1fS20G0R2S2S36VT0;Vevs;A3A3S1fS20S5S3S2fQ40A1S30A2A1S32R1A1Vfds;A3VMDX;R1A1A2A2Lmd;Ltr;").

Lemma alloc_fd_std : alloc_fd std_fds = Z_to_bv 64 3.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma lookup3_std : ltac2:(tb__ "0|0|
S20S7S30A1S3bS61S2eQ40Z3A2A2S9S30A1A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma m_fds_with_vm : ltac2:(tb__ "0|0|
S35S31S20S5S3S2fQ40A1S30A2A1S32S7cR2R1A2A1S32R1A1A3Fmd;Fv;").
Proof. intros v md. destruct md; reflexivity. Qed.
Lemma m_fs_with_vm : ltac2:(tb__ "0|0|
S35S31S20S7eS33S7cR2R1A2A1S33R1A1A3Fmd;Fv;").
Proof. intros v md. destruct md; reflexivity. Qed.
Lemma m_fds_with_fds : ltac2:(tb__ "0|1|
S5S3S2fQ40A1S30A2A1M0S31S20G0S32S37R2R1A2A1R2A3Fmd;Ff;").
Proof. intros f md. destruct md; reflexivity. Qed.
Lemma m_fs_with_fds : ltac2:(tb__ "0|0|
S5S3S2fQ40A1S30A2A1S31S20S7eS33S37R2R1A2A1S33R1A1A3Fmd;Ff;").
Proof. intros f md. destruct md; reflexivity. Qed.
Lemma KcG_ok : ltac2:(tb__ "0|1|
S5S36A1M0S31OFx;S5S3S2fQ40A1S30A2A1G0S31S35R5R2A1R6S7cR2R3A2A1F_;Fv;Fmd;S7dS63R5R4R3R2A4A1F_;Fevs;Ffds;FMDX;FT0;").
Proof.
  intros T0 MDX fds evs HMDXvm tr md v (H1 & H2 & H3). split; [exact H1|]. split; [rewrite m_fds_with_vm; exact H2 | apply HMDXvm; exact H3].
Qed.

