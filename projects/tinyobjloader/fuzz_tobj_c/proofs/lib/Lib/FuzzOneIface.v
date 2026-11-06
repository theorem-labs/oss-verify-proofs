(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "prod"; "list"; "pair"; "None"; "bool"; "false"; "nat"; "fst"; "snd"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sv"; "SVar"; "sprop"; "SPUle"; "sobj"; "sstate"; "DUnknown"; "cell"; "mkObj"; "FcsrFrm0"; "SAlu"; "SPBranch"; "mkSS"; "rw"; "valuation"; "SPAlign"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "post_regs"; "pre_fregs"; "pre_regs"; "@Stdlib.ZArith.BinInt.Z"; "opp"; "pow"; "add"; "le"; "@Corelib.Lists.ListDef"; "map"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FuzzOneIface.Iface"; "P0_fz"; "O_D_fz"; "O_F_fz"; "O_pay"; "Posts_fuzz"; "Pre_fuzz"; "base_facts_fz"; "spm"; "L_fuzz"; "NPOST_FZ"; "PD_fuzz"; "fcallee_saved"; "post_fregs_fz"; "@Corelib.Init.Logic"; "and"; "ex"; "eq"; "or"; "@Corelib.Init.Nat"; "add"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_GE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "jpost"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.FuzzOneIface"; "FZ_P"; "FZ_U"; "V_FZD"; "fuzz_one_sum_ex_stmt"; "fuzz_one_sum_stmt"; "fz_frame"; "FZC"; "FZ_DEPTH"; "fz_entry"; "fz_rets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "JG_pre"; "JLG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "C_P"; "C_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P.Init"; "segsP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Init"; "segsU"; "@Stdlib.PArith.BinPos.Pos"; "of_nat"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "list_set"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "V_TOP"; "ok_sideK"; "vm_insensitive"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws Contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymFrame SymSummary ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Record fuzz_consts := FZC {
  fz_entry : Z;
  fz_frame : Z;
  fz_rets : list Z
}.
Definition FZ_P : fuzz_consts := FZC 0x1a948 400 [0x1a9d0].
Definition FZ_U : fuzz_consts := ltac2:(tb__ "0|0|
S46Z190d4Z170S0SbZ19130S0SbZ19148S1SbA1A3A3A3").

Definition FZ_DEPTH : Z := 16384.

Definition V_FZD : positive := 15%positive.

Section Iface.
Variable segs : list Segment.
Variable C : mconsts.
Variable fz : fuzz_consts.

Definition spm : sv := ltac2:(tb__ "0|0|
S17S3bSePaA1ScS21S45Vfz;A1A1A1A3").

Definition base_facts_fz : list sprop := ltac2:(tb__ "0|7|
S0SfS1cPaM0Z4A2S0SfS18S3cScS21S47A1A1SeS42A1M1A3S0SfS18S3cG1ScS21S22Z2M2Z28A2A1A1A3S0SfS10SeS56A1M3S17S3bS2eG1A3A2S0SfS10G3SeG0A1M4A2S0SfS10G4ScS22G2Z2fA2A1M5A2S0SfS10SePdA1ScS22G2Z1aA2A1A2S0SfS10SePcA1M6G5A2S0SfS10ScZ1000A1G6A2S0SfS10ScZ7fff7f800000A1G3A2S0SfS10G3ScZ7fffff800000A1A2S1SfA1A3A3A3A3A3A3A3A3A3A3A3").

Definition O_F_fz : sobj := ltac2:(tb__ "0|0|
S15SePaA1ScS21S45Vfz;A1A1A1ScZ0A1S1S14A1S13A5").
Definition O_D_fz : sobj := ltac2:(tb__ "0|0|
S15S2eSeS42A1ScZ0A1S1S14A1S13A5").
Definition O_pay : sobj := ltac2:(tb__ "0|0|
S15SePcA1ScZ0A1SePdA1S1S14A1S13A5").

Definition Pre_fuzz : sstate := ltac2:(tb__ "0|0|
S19S48Vfz;A1S20S1fS16S5SdA1S0S11S29S0S11S28S0S11S2aS1S11A1A3A3A3S2dS1dS7A9").

Definition fcallee_saved (r : nat) : bool :=
  match r with 8 | 9 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 => true | _ => false end%nat.
Definition post_fregs_fz : list sv := ltac2:(tb__ "0|0|
S25S8SdS8S6SdL_;S32R1A1SeS50S38U3cR1A2A1A1SeS50S38U8cR1A2A1A1X6x2Lr;S26U0U20A2A4").
Definition NPOST_FZ : positive := 172%positive.
Definition L_fuzz (ret : Z) : sstate := ltac2:(tb__ "0|0|
S19Vret;S55SdS1eS1dA1UaScZ0A1A4S33S16S5SdA1S0S11S29S0S11S28S0S11S2aS1S11A1A3A3A3S2dS30S7A9").

Definition payload_cov (FBc : list (Z * Z)) (rho1 : valuation) : Prop := ltac2:(tb__ "0|3|
S37S36SbS51Q40M0S1aVrho1;PdA2A2M1Z0A3S35SbSbS35SbSbS34S59S2SbSbA2S4SbSbR2R1A4VFBc;A3S34S24R2S51G0S1aVrho1;PcA2A2M2A2S24S23G2G1A2S23R2R1A2A2A2A2Ln;A2Lb;A2A2").
Definition P0_fz (FBc : list (Z * Z)) : valuation -> Prop := payload_cov FBc.

Definition PD_fuzz : list (sstate * list (sv * sv)) := ltac2:(tb__ "0|2|
S25SbS2S12S3S2SdSdA2M0A1M1A2SbS4S12G1S2fR1A1S1G0A1A4Lr;S49Vfz;A1A4").

Definition Posts_fuzz (Kc : list event -> Model -> Prop) (FBc : list (Z * Z)) : list (sstate * jpost) := ltac2:(tb__ "0|2|
S25S2S12S3S2SdSdA2A1M0A2M1S2S12S3fA2G1S4S12S3fS9S12G0R1A3S4bVsegs;VC;VKc;S27VFBc;A1VFBc;SaS12G0R1A3A6A4Ld;S31A4").

Definition fuzz_one_sum_stmt : Prop := ltac2:(tb__ "0|0|
S54OF_;S3S3aA1S39OF_;F_;S3S2SbSbA2A1S1bS57Vsegs;R4R3A3S53Vsegs;R5S3dVsegs;S4aVsegs;VC;R4S27R3A1R3S1S2SdSdA2A1A6S2cR2A4S3eVsegs;S1dR2S2bR4R3A2A4A4F_;Frho1;FFBc;FKc;Fok;").

Definition fuzz_one_sum_ex_stmt : Prop := ltac2:(tb__ "0|0|
S3S3aA1S39OF_;F_;S3S2SbSbA2A1S1bS58R3A1S52Vsegs;S3dVsegs;S4aVsegs;VC;R4S27R3A1R3S1S2SdSdA2A1A6S2cR2A4S3eVsegs;S1dR2S2bR4R3A2A4A3F_;Frho1;FFBc;FKc;").

Lemma Pre_fuzz_next : ss_next Pre_fuzz = NF. Proof using . reflexivity. Qed.
End Iface.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.P Require Init.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Init.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition fuzz_one_sum_stmt_P : Prop := ltac2:(tb__ "0|0|
S44S4eS4cS40A3").
Definition fuzz_one_sum_ex_stmt_P : Prop := ltac2:(tb__ "0|0|
S43S4eS4cS40A3").
Definition fuzz_one_sum_stmt_U : Prop := ltac2:(tb__ "0|0|
S44S4fS4dS41A3").
Definition fuzz_one_sum_ex_stmt_U : Prop := ltac2:(tb__ "0|0|
S43S4fS4dS41A3").
