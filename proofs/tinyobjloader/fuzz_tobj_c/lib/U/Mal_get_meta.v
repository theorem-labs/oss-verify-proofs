(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nat"; "nil"; "pair"; "app"; "list"; "true"; "false"; "None"; "Some"; "option"; "prod"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "SAlu"; "sv"; "SPBranch"; "cell"; "mkCell"; "sobj"; "mkObj"; "DUnknown"; "SMd"; "SExt"; "SPNot"; "FcsrFrm0"; "SPUle"; "mkSS"; "valuation"; "DRom"; "SLBytes"; "SPAlign"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta.States"; "v"; "gm_idx"; "gm_scsize"; "gm_variant"; "gm_maplen"; "gm_sc"; "NFM"; "gm_bit"; "gm_facts"; "gm_facts_map"; "gm_facts_sized"; "gm_mem_sv"; "gm_objs"; "MASK_PAGE"; "Post_get_meta"; "gm_facts_common"; "gm_facts_direct"; "gm_facts_nomap"; "gm_last"; "gm_post_regs"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "BC_EQ"; "BC_GEU"; "M_MUL"; "ALU_AND"; "BC_LTU"; "ALU_SRL"; "ALU_SUB"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "segsU"; "segsU"; "pre_fregs"; "pre_regs"; "setregs"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "sym_run"; "RsSymJump"; "mkLeaf"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.Mal_get_meta"; "GM_P"; "GM_U"; "Posts_get_meta"; "Pre_get_meta"; "gm_variant"; "GM_FUEL"; "L_SIZECLASSES"; "NFM"; "gm_ctx"; "gm_entry"; "gm_ret"; "gm_sctab"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple"; "world"; "@OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "LQ"; "SP"; "ok_frame"].
#[local] Ltac2 tb__ s := OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG ExampleMemcpy.
From OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images Require Import Ubsan.
From OssFuzzTheorems.tinyobjloader.fuzz_tobj_c.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Record gm_consts := GMC { gm_entry : Z; gm_ret : Z; gm_ctx : Z; gm_sctab : Z }.
Definition GM_P : gm_consts := GMC 0x2073c 0x20848 0x5a3d0 0x108ec.
Definition GM_U : gm_consts := GMC (0x1fffc + 0x740) (0x20108 + 0x740) 0x5a3d0 0x108ec.

Definition L_SIZECLASSES : positive := 1%positive.

Section States.
Variable c : gm_consts.

Definition v (n : positive) : sv := SVar n.

Definition NFM : positive := 200%positive.
Definition MASK_PAGE : Z := 18446744073709547520.

Definition gm_mem_sv : sv := ltac2:(tb__ "0|0|
SeS3cS20PcA1SeS35S20P83A1ScZ4A1A3A3").

Definition gm_objs : list sobj := ltac2:(tb__ "0|b|
S0S13S14S20PcA1ScN4A1M0ScZ0A1M1S0S11S12G0Z1M2G1A3S0S11S12ScN3A1G2S20P82A1A3S0S11S12ScN2A1Z2S20P83A1A3S2S11A1M3A3A3A3S15A5S0S13S14S2bScN10A1M4ScN8A1S0S11S12G4Z8M5S20P84A1M6A3G3A3S15A5S0S13S14G6ScZ10A1M7ScZ28A1S0S11S12G7G5SeS34S2bG4A3A3S0S11S12ScZ18A1Z4M8S20P85A1A3S0S11S12ScZ1cA1G8S20P86A1A3S0S11S12ScZ20A1G5S20P87A1A3G3A3A3A3A3S15A5S0S13S14SeS39G6ScS2dA1A3G1ScG5A1M9S0S11S12G1G5S20P88A1A3G3A3MaS15A5S0S13S14ScS4eVc;A1A1G1G9GaS15A5S0S13S14ScS51Vc;A1A1G1ScZ60A1G3S1dS4cA1A5S2S13A1A3A3A3A3A3A3").

Definition gm_idx : sv := SAlu ALU_AND (v 130) (SLit 31).
Definition gm_last : sv := SAlu ALU_AND (v 135) (SLit 31).
Definition gm_sc : sv := ltac2:(tb__ "0|0|
SeS3bSeS35S20P87A1ScZ34A1A3ScZ3aA1A3").
Definition gm_maplen : sv := SAlu ALU_SRL (v 135) (SLit 12).
Definition gm_bit : sv := SAluW ALU_SLL (SLit 1) gm_idx.
Definition gm_scsize : sv := ltac2:(tb__ "0|0|
S17S7Q10S1eS4cSeS35S25ScZ1A1A3Z2A3A3").

Definition gm_facts_common : list sprop := ltac2:(tb__ "0|2|
S0SdS1fPcZ4A2S0SdS1aS20P82A1ScZffA1A2S0SdS1aS20P83A1ScZffffA1A2S0SdS10S37S32S21A3S0SdS10S36SeS39S17S6Q20M0S20P85A1A3S27A3ScZ0A1M1A3S0SdS10S36SeS39S17S6G0S20P86A1A3S27A3G1A3S2SdA1A3A3A3A3A3A3").

Definition gm_facts_sized : list sprop := ltac2:(tb__ "0|1|
S0SdS18S10S3aScZ2fA1S25A3A1S0SdS10S37S20P83A1M0S16S38S22S21A3A3S0SdS18S10S37G0S16S38SeS34S21ScZ1A1A3S22A3A3A1S2SdA1A3A3A3").

Definition gm_facts_direct : list sprop := ltac2:(tb__ "0|0|
S0SdS10S3aScZ2fA1S25A3S0SdS10S36S25ScZ3fA1A3S2SdA1A3A3").

Definition gm_facts_nomap : list sprop := ltac2:(tb__ "0|0|
S0SdS10S36S24ScZ0A1A3S2SdA1A3").
Definition gm_facts_map : list sprop := ltac2:(tb__ "0|0|
S0SdS18S10S36S24ScZ0A1A3A1S0SdS10S37SeS34SeS35S24ScZ8A1A3ScN1A1A3S20P83A1A3S2SdA1A3A3").

Inductive gm_variant := GM_A0 | GM_A1 | GM_B.

Definition gm_facts (x : gm_variant) : list sprop := ltac2:(tb__ "0|0|
S4SdS2fS23S5SdA1Lx;Vx;S4SdS2aS31A3S4SdS2aS29A3S4SdS30S29A3X23x3A3").

Definition Pre_get_meta (x : gm_variant) : sstate := ltac2:(tb__ "0|0|
S1bS4fVc;A1S40S3fS19S8SfA1S2cS28Vx;A1S26S7A9").

Definition gm_post_regs (x : gm_variant) : list sv := ltac2:(tb__ "0|a|
S41S40S4SbS1SfA2M0S0G0S3S1SfUaS20P84A1A4S0G0S3S1SfUbS20P83A1A4S2G0A1M1A3A3S4G0S23S5G0A1Lx;M2Vx;S0G0S3S1SfUcM3ScZ0A1A4G1A3S0G0S3S1SfG3SeS34SeS35S24ScZ8A1A3ScN1A1A3A4G1A3M4G4X23x3G2Vx;S0G0S3S1SfUdM5S16S38SeS34S21ScZ1A1A3S22A3A4S0G0S3S1SfUeM6S22A4S0G0S3S1SfUfM7S16S38S22S21A3A4G1A3A3A3M8G8S0G0S3S1SfG5ScZ3fA1M9A4S0G0S3S1SfG6G9A4S0G0S3S1SfG7ScZ2fA1A4G1A3A3A3X23x3A3A3A2").

Definition Post_get_meta (x : gm_variant) : sstate := ltac2:(tb__ "0|0|
S1bS50Vc;A1S33Vx;A1S3fS19S8SfA1S2cS28Vx;A1S26S7A9").

Definition Posts_get_meta (x : gm_variant) : list leaf := ltac2:(tb__ "0|0|
S0S42S45S2eVx;A1S44A2S2S42A1A3").

End States.

Definition GM_FUEL : nat := 300%nat.

Lemma run_get_meta_P : ltac2:(tb__ "0|1|
S4aS52SaS5S42A1M0A1S43S3dS4bS2S53A1S49S46R1A2S6A5S9G0S48S46R1A2A2A3Fx;").
Proof. intros [| |]; vm_compute; reflexivity. Qed.

Theorem get_meta_sum_P : ltac2:(tb__ "0|0|
S4aS57OF_;S5S55A1S54OF_;F_;S1cS5aS3dR3R2A3S56S3dR4S59S3dR3S49S46R5A2R2A4S58S3dR3S4dR2S48S46R5A2A5A4F_;Frho;FK;Fok;Fx;").
Proof.
  intros x ok K rho Hok. apply triple1_triple.
  apply (sym_run_sound_strict segsU GM_FUEL [] (Pre_get_meta GM_P x) (Posts_get_meta GM_P x) ok K rho eq_refl (run_get_meta_P x) Hok).
Qed.

Lemma run_get_meta_U : ltac2:(tb__ "0|1|
S4aS52SaS5S42A1M0A1S43S3eS4bS2S53A1S49S47R1A2S6A5S9G0S48S47R1A2A2A3Fx;").
Proof. intros [| |]; vm_compute; reflexivity. Qed.

Theorem get_meta_sum_U : ltac2:(tb__ "0|0|
S4aS57OF_;S5S55A1S54OF_;F_;S1cS5aS3eR3R2A3S56S3eR4S59S3eR3S49S47R5A2R2A4S58S3eR3S4dR2S48S47R5A2A5A4F_;Frho;FK;Fok;Fx;").
Proof.
  intros x ok K rho Hok. apply triple1_triple.
  apply (sym_run_sound_strict segsU GM_FUEL [] (Pre_get_meta GM_U x) (Posts_get_meta GM_U x) ok K rho eq_refl (run_get_meta_U x) Hok).
Qed.
