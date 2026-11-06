(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "nat"; "pair"; "bool"; "false"; "list"; "prod"; "true"; "app"; "length"; "None"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sprop"; "sv"; "SVar"; "cell"; "sstate"; "mkCell"; "rl"; "SPBranch"; "sobj"; "valuation"; "SAlu"; "SPNot"; "SPUle"; "FcsrFrm0"; "mkObj"; "mkSS"; "DUnknown"; "SExt"; "SLBytes"; "ss_lenient"; "DList"; "SPAlign"; "ext_low"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "vnode"; "mkVN"; "check_cfg"; "check_ecfg"; "@Stdlib.ZArith.BinInt.Z"; "add"; "land"; "modulo"; "pow"; "le"; "lt"; "mul"; "of_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyRS"; "Eb"; "LS"; "FUELRS"; "E3c"; "Posts_rsB"; "Posts_rsS"; "Pre_rsB"; "Pre_rsS"; "cutpcs_rsB"; "cutpcs_rsS"; "cuts_rsB"; "cuts_rsS"; "exits_rsB"; "exits_rsS"; "vcuts_rsB"; "vcuts_rsS"; "vexits_rsB"; "vexits_rsS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "NPOST"; "cut_regs"; "post_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyRS.States"; "Eb"; "nm3"; "P_rs"; "F_rs"; "Fbig"; "Fsmall"; "LS"; "O_src"; "P_rsA_c"; "P_rsA_t"; "P_rsB_c"; "P_rsB_t"; "P_rsZ"; "hcells_c"; "rs_cut"; "C_58r"; "C_a4r"; "C_rs"; "O_dst"; "Pre_rsB"; "RSLEN"; "hcells_t"; "B120r"; "B121r"; "E3c"; "F_z"; "J120r"; "O_dst0"; "Pre_rsS"; "hcells_z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsSymJump"; "mkLeaf"; "@Corelib.Init.Peano"; "le"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "bytes_le_to_Z"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_AND"; "BC_LTU"; "BC_NE"; "ALU_ADD"; "BC_GEU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "LQ"; "SP"; "ok_frame"; "@Corelib.Lists.ListDef"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.HdrPack"; "byte_of"; "pack4_word"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SysRead"; "hdr_val"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@Stdlib.Lists.List"; "existsb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymSoundW.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CellTile SysRead.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import HdrPack.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section States.
Variable base : Z.
Variable rs : Z.

Definition LS : positive := 5%positive.
Definition RSLEN : Z := 65536.

Definition F_rs : list sprop := ltac2:(tb__ "0|1|
S0SdS22PcZ2A2S0SdS19ScZ4A1SfPeA1M0A2S0SdS19G0ScS63A1A2S1SdA1A3A3A3").
Definition O_src : sobj := ltac2:(tb__ "0|0|
S1bScZ0A1ScVrs;A1ScS2bVrs;S63A2A1S1S10A1S21S55A1A5").
Definition O_dst0 : sobj := ltac2:(tb__ "0|0|
S1bSfPcA1ScZ0A1SfPeA1S1S10A1S1dA5").

Definition Eb (t : Z) : sv := ltac2:(tb__ "0|0|
S1eS5Q8S1fS55ScVt;A1Z1A3A3").
Definition E3c : sv := ltac2:(tb__ "0|0|
S1eS8Q20S1fS55ScZ3A1Z4A3A3").
Definition hcells_t : list cell := ltac2:(tb__ "0|4|
S0S10S12ScZ3M0A1Z1M1S4fG0A1A3S0S10S12ScZ2M2A1G1S4fG2A1A3S0S10S12ScG1A1G1S4fG1A1A3S0S10S12ScZ0M3A1G1S4fG3A1A3S1S10A1A3A3A3A3").
Definition hcells_c : list cell := ltac2:(tb__ "0|3|
S0S10S12ScZ3A1Z1M0S67A3S0S10S12ScZ2M1A1G0S4fG1A1A3S0S10S12ScG0A1G0S4fG0A1A3S0S10S12ScZ0M2A1G0S4fG2A1A3S1S10A1A3A3A3A3").
Definition hcells_z : list cell := ltac2:(tb__ "0|3|
S0S10S12ScZ2M0A1Z1M1S4fG0A1A3S0S10S12ScG1A1G1S4fG1A1A3S0S10S12ScZ0M2A1G1S4fG2A1A3S1S10A1A3A3A3").
Definition O_dst (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S1bSfPcA1ScZ0A1SfPeA1Vcs;S1dA5").

Definition nm3 : sv := SAlu ALU_ADD (SVar 14) (SLit (-3)).
Definition Fsmall : sprop := SPBranch BC_LTU nm3 (SLit 32).
Definition Fbig : sprop := ltac2:(tb__ "0|0|
S18S14S76S50ScZ20A1A3A1").
Definition Pre_rs (fsz : sprop) : sstate := ltac2:(tb__ "0|1|
S1cVbase;S4aS4eS0S7S2SeA2M0S3S2SeUbScVrs;A1A4S1G0A1A3A2S49S1aSbSeA1S0S15S6aS0S15S56S1S15A1A3A3S0SdVfsz;S52A3S48S5A9").
Definition Pre_rsS : sstate := Pre_rs Fsmall.
Definition Pre_rsB : sstate := Pre_rs Fbig.

Definition J120r : sprop := ltac2:(tb__ "0|0|
S19S17S78SfP78A1SfP79A1A3SfPeA1A2").
Definition B120r : sprop := SPUle (SVar 120) (SLit two62).
Definition B121r : sprop := SPUle (SVar 121) (SLit two62).
Definition rs_cut (pc : Z) (cs : Z) (extra : list (nat * sv)) (facts : list sprop) : sstate := ltac2:(tb__ "0|3|
S1cVpc;S4aS4cS48A1S9S7S2SeA2M0S0G0S3S2SeUaSfPcA1M1A4S0G0S3S2SeUbS17S78ScS2bVrs;Vcs;A2A1SfP78A1M2A3A4S0G0S3S2SeUcSfP79A1A4S0G0S3S2SeUdS17S78G1G2A3A4S1G0A1A3A3A3A3Vextra;A3A2S49S1aSbSeA1S0S15S61S5cA1S0S15S56S1S15A1A3A3S9SdVfacts;S9SdS0SdS19ScZ4A1G2A2S0SdS69S0SdS65S0SdS66S0SdS53S1SdA1A3A3A3A3A3S52A3A3P87S5A9").
Definition C_rs : sstate := ltac2:(tb__ "0|2|
S5dS2bVbase;Z1acA2ZfS0S7S2SeA2M0S3S2SeUfScZ12A1M1A4S1G0A1A3S0SdS14S76G1SfP79A1A3S1SdA1A3A4").
Definition C_58r : sstate := ltac2:(tb__ "0|0|
S5dS2bVbase;Z60A2Z0S1S7S2SeA2A1S0SdS14S76SfP79A1ScZ10A1A3S1SdA1A3A4").
Definition C_a4r : sstate := ltac2:(tb__ "0|1|
S5dS2bVbase;Z2acA2Z0S1S7S2SeA2A1S0SdS19ScZ10A1SfP79A1M0A2S0SdS14S76G0ScZ20A1A3S1SdA1A3A3A4").

Definition P_rs (pc : Z) (cs : list cell) (fs : list sprop) : sstate := ltac2:(tb__ "0|1|
S1cVpc;S4aS4dS48A1S0S7S2SeA2M0S3S2SeUaSfPcA1A4S1G0A1A3A2S49S1aSbSeA1S0S15S61Vcs;A1S0S15S56S1S15A1A3A3S9SdVfs;S52A3S4bS5A9").
Definition F_z : list sprop := ltac2:(tb__ "0|1|
S0SdS18S14S77S17S75S50ScZ1A1A3ScZ0A1M0A3A1S0SdS18S14S77S17S75S50ScZ2A1A3G0A3A1S0SdS18S14S77S17S75S50ScZ4A1A3G0A3A1S0SdS18S14S77S17S75S50ScZ8A1A3G0A3A1S0SdS18S14S79S50ScZ10A1A3A1S1SdA1A3A3A3A3A3").
Definition P_rsA_t : sstate := ltac2:(tb__ "0|0|
S51S2bVbase;Z3d0A2S64S0SdS54S1SdA1A3A3").
Definition P_rsB_t : sstate := ltac2:(tb__ "0|0|
S51S2bVbase;Z400A2S64S0SdS54S1SdA1A3A3").
Definition P_rsZ   : sstate := ltac2:(tb__ "0|0|
S51S2bVbase;Z3d0A2S6cS9SdS68S0SdS54S1SdA1A3A3A3").
Definition P_rsA_c : sstate := ltac2:(tb__ "0|0|
S51S2bVbase;Z3d0A2S5cS0SdS53S1SdA1A3A3").
Definition P_rsB_c : sstate := ltac2:(tb__ "0|0|
S51S2bVbase;Z400A2S5cS0SdS53S1SdA1A3A3").
Definition Posts_rsS : list leaf := ltac2:(tb__ "0|0|
S0S6dS6fS58S6eA2S0S6dS6fS5aS6eA2S0S6dS6fS5bS6eA2S1S6dA1A3A3A3").
Definition Posts_rsB : list leaf := ltac2:(tb__ "0|0|
S0S6dS6fS57S6eA2S0S6dS6fS59S6eA2S1S6dA1A3A3").

Definition cuts_rsS : list sstate := [Pre_rsS].
Definition exits_rsS : list sstate := ltac2:(tb__ "0|0|
S0S11S58S0S11S5aS0S11S5bS1S11A1A3A3A3").
Definition cutpcs_rsS : list Z := [].
Definition cuts_rsB : list sstate := ltac2:(tb__ "0|0|
S0S11S62S0S11S60S0S11S5eS0S11S5fS1S11A1A3A3A3A3").
Definition exits_rsB : list sstate := ltac2:(tb__ "0|0|
S0S11S57S0S11S59S1S11A1A3A3").
Definition cutpcs_rsB : list Z := ltac2:(tb__ "0|0|
S0S26S2bVbase;Z1acA2S0S26S2bVbase;Z60A2S0S26S2bVbase;Z2acA2S1S26A1A3A3A3").

Definition vcuts_rsS : list vnode := ltac2:(tb__ "0|0|
S0S27S28S6bZaScZ0A1A3S1S27A1A3").
Definition vexits_rsS : list vnode := ltac2:(tb__ "0|2|
S0S27S28S58Z0M0ScG0A1M1A3S0S27S28S5aG0G1A3S0S27S28S5bG0G1A3S1S27A1A3A3A3").
Definition vcuts_rsB : list vnode := ltac2:(tb__ "0|2|
S0S27S28S62ZaScZ0A1M0A3S0S27S28S60Z7SfP79A1A3S0S27S28S5eZ6M1G0A3S0S27S28S5fG1G0A3S1S27A1A3A3A3A3").
Definition vexits_rsB : list vnode := ltac2:(tb__ "0|2|
S0S27S28S57Z0M0ScG0A1M1A3S0S27S28S59G0G1A3S1S27A1A3A3").
End States.

Definition FUELRS : nat := 400%nat.

Section Generic.
Variable segs : list Segment.
Variables base rs : Z.
Hypothesis check_rsS : ltac2:(tb__ "0|0|
S24S4S29Vsegs;S38S3fS48S41Vbase;Vrs;A2S43Vbase;Vrs;A2A6S8A3").
Hypothesis echeck_rsS : ltac2:(tb__ "0|0|
S24S4S2aVsegs;S38S3fS48S45Vbase;Vrs;A2S47Vbase;Vrs;A2A6S8A3").
Hypothesis check_rsB : ltac2:(tb__ "0|0|
S24S4S29Vsegs;S38S3eVbase;A1S48S40Vbase;Vrs;A2S42Vbase;Vrs;A2A6S8A3").
Hypothesis echeck_rsB : ltac2:(tb__ "0|0|
S24S4S2aVsegs;S38S3eVbase;A1S48S44Vbase;Vrs;A2S46Vbase;Vrs;A2A6S8A3").

Lemma cuts_rsS_strict : ltac2:(tb__ "0|0|
S24S4S84S11S20S41Vbase;Vrs;A2A3S5A3"). Proof using . reflexivity. Qed.
Lemma cuts_rsB_strict : ltac2:(tb__ "0|0|
S24S4S84S11S20S40Vbase;Vrs;A2A3S5A3"). Proof using . reflexivity. Qed.

Theorem memcpy_rsS_sum : ltac2:(tb__ "0|0|
S83OF_;S6S74A1S73OF_;F_;S16S7cVsegs;R3R2A3S82Vsegs;R4S7bVsegs;R3S3dVbase;Vrs;A2R2A4S7aVsegs;R3S48R2S3bVbase;Vrs;A2A5A4F_;Frho;FK;Fok;").
Proof using check_rsS.
  intros ok K rho Hok.
  apply (cfg_sound segs FUELRS cutpcs_rsS NF (cuts_rsS base rs) (exits_rsS base rs)
           (fun rho' => agree_below NF rho rho') ok K (LQ segs K NF rho (Posts_rsS base rs)) Hok).
  - rewrite cuts_rsS_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_rsS.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[<-|[<-|[]]]]; (apply exit_post; [cbn; tauto | exact HagE]).
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Theorem memcpy_rsS_sum_ex : ltac2:(tb__ "0|0|
S6S74A1S73OF_;F_;S16S81Vsegs;S7bVsegs;R2S3dVbase;Vrs;A2R1A4S7aVsegs;R2S48R1S3bVbase;Vrs;A2A5A3Frho;FK;").
Proof using echeck_rsS.
  intros K rho.
  change (Pre_rsS base rs) with (vn_state (mkVN (Pre_rsS base rs) 10 (SLit 0))).
  apply (cfg_complete_auto segs FUELRS cutpcs_rsS NF (vcuts_rsS base rs) (vexits_rsS base rs)
           (fun rho' => agree_below NF rho rho') K (LQ segs K NF rho (Posts_rsS base rs))).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_rsS.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[<-|[<-|[]]]]; (apply eexit_post; [cbn; tauto | exact HgE]).
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Theorem memcpy_rsB_sum : ltac2:(tb__ "0|0|
S83OF_;S6S74A1S73OF_;F_;S16S7cVsegs;R3R2A3S82Vsegs;R4S7bVsegs;R3S3cVbase;Vrs;A2R2A4S7aVsegs;R3S48R2S3aVbase;Vrs;A2A5A4F_;Frho;FK;Fok;").
Proof using check_rsB.
  intros ok K rho Hok.
  apply (cfg_sound segs FUELRS (cutpcs_rsB base) NF (cuts_rsB base rs) (exits_rsB base rs)
           (fun rho' => agree_below NF rho rho') ok K (LQ segs K NF rho (Posts_rsB base rs)) Hok).
  - rewrite cuts_rsB_strict. intros; discriminate.
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact check_rsB.
  - intros E rhoE HinE HagE.
    destruct HinE as [<-|[<-|[]]]; (apply exit_post; [cbn; tauto | exact HagE]).
  - left; reflexivity.
  - apply agree_below_refl.
Qed.

Theorem memcpy_rsB_sum_ex : ltac2:(tb__ "0|0|
S6S74A1S73OF_;F_;S16S81Vsegs;S7bVsegs;R2S3cVbase;Vrs;A2R1A4S7aVsegs;R2S48R1S3aVbase;Vrs;A2A5A3Frho;FK;").
Proof using echeck_rsB.
  intros K rho.
  change (Pre_rsB base rs) with (vn_state (mkVN (Pre_rsB base rs) 10 (SLit 0))).
  apply (cfg_complete_auto segs FUELRS (cutpcs_rsB base) NF (vcuts_rsB base rs) (vexits_rsB base rs)
           (fun rho' => agree_below NF rho rho') K (LQ segs K NF rho (Posts_rsB base rs))).
  - intros r1 r2 H1 H2. eapply agree_below_trans; eauto.
  - exact echeck_rsB.
  - intros E rhoE HinE HgE.
    destruct HinE as [<-|[<-|[]]]; (apply eexit_post; [cbn; tauto | exact HgE]).
  - left; reflexivity.
  - apply agree_below_refl.
Qed.
End Generic.

Section Hdr.

Lemma ext_low32_mod' : ltac2:(tb__ "0|2|
S33Q40M0A1S24S26S2dS34G0S23S8Q20R1A3A2S2eZ2Z20A2M1A2S2dS34G0R1A2G1A2A3Fv;").
Proof using .
  intros v. unfold ext_low. rewrite sext64_32_mod by lia.
  rewrite bv_extract_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  apply Z.mod_mod. lia.
Qed.

Lemma bytes_le_to_Z_single : ltac2:(tb__ "0|2|
S33Q8M0A1M1S24S26S72S0G1R1S1G1A1A3A1S34G0R1A2A3Fb;").
Proof using . intros b. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l. apply Z.lor_0_r. Qed.

Lemma bytes_le_to_Z_cons : ltac2:(tb__ "0|2|
S33Q8M0A1M1S6G1A1S24S26S72S0G1R2R1A3A1S2bS34G0R2A2S31S72R1A1S2eZ2Z8A2A2A2A3Fr;Fb;").
Proof using .
  intros b r. change (b :: r) with ([b] ++ r). rewrite bytes_le_to_Z_app, bytes_le_to_Z_single. cbn [length Z.of_nat]. reflexivity.
Qed.

Lemma bytes_le_to_Z_cons_mod : ltac2:(tb__ "0|2|
S33Q8M0A1M1S6G1A1S24S26S2dS72S0G1R2R1A3A1S2eZ2Z8A2A2S34G0R2A2A3Fr;Fb;").
Proof using .
  intros b r. rewrite bytes_le_to_Z_cons. pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with (2 ^ 8) in Hb.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma byte_of_Eb : ltac2:(tb__ "0|2|
S16S2S71R1SaS33Q8M0A1M1S13R2S37A2A2A2S71R2U4A2S24S26S7eR4S36S32R3A1A1A2S34G0S7dG1R3S13R4S37A2S35G0Z0A2A4A2A3F_;F_;Ft;Frho;").
Proof using .
  intros rho t Ht H4. unfold byte_of, Eb. cbn [eval].
  change 8%N with (8 * N.of_nat 1)%N. rewrite (ext_low_false_unsigned 1) by lia. change (8 * Z.of_nat 1) with 8.
  rewrite Z.mod_mod by lia.
  unfold sublist. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small (Z.of_nat t)) by lia.
  rewrite Nat2Z.id. change (Z.to_nat 1) with 1%nat.
  destruct (skipn t (rl rho LS)) as [|b r] eqn:E.
  - exfalso. apply (f_equal (@length _)) in E. rewrite length_skipn in E. cbn in E. lia.
  - cbn [firstn]. unfold le_bytes_to_word. rewrite bytes_le_to_Z_single.
    pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
    rewrite Z.mod_small by lia.
    replace b with (nth t (rl rho LS) (Z_to_bv 8 0)); [reflexivity|].
    rewrite <- (Nat.add_0_r t), <- nth_skipn, E. reflexivity.
Qed.

Lemma byte_of_E3c : ltac2:(tb__ "0|2|
S16S70U4SaS33Q8M0A1M1S13R1S37A2A2A2S24S26S7eR2S39A2S34G0S7dG1U3S13R2S37A2S35G0Z0A2A4A2A3F_;Frho;").
Proof using .
  intros rho Hl. unfold byte_of, E3c. cbn [eval].
  rewrite <- (mod_pow2_mono' _ 8 32) by lia. rewrite ext_low32_mod'. rewrite (mod_pow2_mono' _ 8 32) by lia.
  unfold sublist. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small 3) by lia.
  change (Z.to_nat 3) with 3%nat. change (Z.to_nat 4) with 4%nat.
  destruct (skipn 3 (rl rho LS)) as [|b r] eqn:E.
  - exfalso. apply (f_equal (@length _)) in E. rewrite length_skipn in E. cbn in E. lia.
  - unfold le_bytes_to_word. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    pose proof (bytes_le_to_Z_bound (firstn 4 (b :: r))) as B.
    assert (L4 : (length (firstn 4 (b :: r)) <= 4)%nat) by (rewrite length_firstn; lia).
    assert (B' : bytes_le_to_Z (firstn 4 (b :: r)) < 2 ^ 32).
    { eapply Z.lt_le_trans; [apply B|]. apply Z.pow_le_mono_r; lia. }
    rewrite (Z.mod_small _ (2 ^ 64)) by lia. cbn [firstn]. rewrite bytes_le_to_Z_cons_mod.
    replace b with (nth 3 (rl rho LS) (Z_to_bv 8 0)); [reflexivity|].
    change 3%nat with (3 + 0)%nat at 1. rewrite <- nth_skipn, E. reflexivity.
Qed.

Lemma pack4_hdr : ltac2:(tb__ "0|3|
S16SeS70U4SaS33Q8M0A1M1S13R2S37A2A2A2S24S26S7eR3R2A2S34G0S7dG1U3S13R3S37A2S35G0Z0M2A2A4A2A3S24S33Q40A1S7fR4S0SeS36G2A1S0SeS36Z1A1S0SeS36Z2A1S0SeR3S1SeA1A3A3A3A3A2S80S13R4S37A2A1A3F_;F_;Fe3;Frho;").
Proof using .
  intros rho e3 Hl H3. unfold pack4_word, hdr_val. f_equal. cbn [pack4_Z].
  change (Eb 0) with (Eb (Z.of_nat 0)). change (Eb 1) with (Eb (Z.of_nat 1)). change (Eb 2) with (Eb (Z.of_nat 2)).
  rewrite (byte_of_Eb rho 0) by lia. rewrite (byte_of_Eb rho 1) by lia. rewrite (byte_of_Eb rho 2) by lia. rewrite H3.
  destruct (rl rho LS) as [|b0 [|b1 [|b2 [|b3 r]]]]; cbn [length] in Hl; try lia.
  cbn [firstn nth]. rewrite !bytes_le_to_Z_cons. change (firstn 0 r) with (@nil byte). change (bytes_le_to_Z []) with 0. lia.
Qed.

Corollary pack4_hdr_t : ltac2:(tb__ "0|0|
S16S70U4SaS33Q8A1S13R1S37A2A2A2S24S33Q40A1S7fR2S0SeS36Z0A1S0SeS36Z1A1S0SeS36Z2A1S0SeS36Z3A1S1SeA1A3A3A3A3A2S80S13R2S37A2A1A3F_;Frho;").
Proof using . intros rho Hl. apply pack4_hdr; [exact Hl|]. change (Eb 3) with (Eb (Z.of_nat 3)). apply (byte_of_Eb rho 3); lia. Qed.
Corollary pack4_hdr_c : ltac2:(tb__ "0|0|
S16S70U4SaS33Q8A1S13R1S37A2A2A2S24S33Q40A1S7fR2S0SeS36Z0A1S0SeS36Z1A1S0SeS36Z2A1S0SeS39S1SeA1A3A3A3A3A2S80S13R2S37A2A1A3F_;Frho;").
Proof using . intros rho Hl. apply pack4_hdr; [exact Hl|]. apply byte_of_E3c. exact Hl. Qed.

Lemma rsZ_absurd_Z : ltac2:(tb__ "0|1|
S26S25S2fZ0M0R1A2S30R1Z10A2A2S24S26S2cR2Z1A2G0A3S24S26S2cR3Z2A2G0A3S24S26S2cR4Z4A2G0A3S24S26S2cR5Z8A2G0A3S24S26R6G0A3F_;F_;F_;F_;F_;Fm;").
Proof using .
  intros m Hm H1 H2 H4 H8.
  assert (C : m = 0 \/ m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5 \/ m = 6 \/ m = 7 \/ m = 8 \/ m = 9 \/ m = 10 \/ m = 11 \/ m = 12 \/ m = 13 \/ m = 14 \/ m = 15) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]]; cbn in *; try reflexivity; discriminate.
Qed.
End Hdr.
