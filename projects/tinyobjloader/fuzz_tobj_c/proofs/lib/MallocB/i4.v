(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From Stdlib Require NArith PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require IfaceEx Inv.
From Stdlib Require FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Prelude Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.

(* [comment removed for export] *)
Module SegQC_states.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "nil"; "prod"; "nat"; "app"; "bool"; "false"; "pair"; "None"; "true"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "SLit"; "sobj"; "sv"; "sprop"; "cell"; "SAlu"; "SVar"; "mkCell"; "SPUlt"; "DUnknown"; "FcsrFrm0"; "mkObj"; "mkSS"; "SMd"; "SPAlign"; "SPBranch"; "SPNot"; "SPUle"; "ss_lenient"; "ss_next"; "swf"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "add"; "vMX"; "vPK"; "NPRE"; "O_sb"; "runA"; "vCS"; "vST"; "DEPTH_Q"; "NXQ"; "chk1p"; "post_ru"; "vSB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states"; "PreQC"; "F_QC"; "O_ent"; "O_slotC"; "O_stC"; "QCFULL"; "QCINIT"; "QCRET"; "ent_base"; "run_QC"; "ALLOCG"; "PostQC"; "QCENT"; "cptr_of"; "regsC"; "slotC_base"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "ALU_SLL"; "ALU_SRL"; "BC_EQ"; "M_MUL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "pre_fregs"; "pre_regs"; "setregs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "leafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "A_globals"; "mkA"; "stack_win"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA SysCallA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Open Scope Z_scope.

Definition QCENT : Z := 0x3eb68.
Definition QCRET : Z := 0x3ec08.
Definition QCFULL : Z := 0x3ecf8.
Definition QCINIT : Z := 0x3ec50.
Definition ALLOCG : Z := 0xeaa58.

Definition ent_base : sv := ltac2:(tb__ "0|0|
S24S11PcA1S18S45S11PeA1SbZ50A1A3A2").
Definition O_ent (k : sv) : sobj := ltac2:(tb__ "0|3|
S16S39SbZ0A1M0SbZ10A1S0SfS12G0Z4M1Vk;A3S0SfS12SbG1A1G1S25A3S0SfS12SbZ8M2A1G2S2aA3S1SfA1A3A3A3S14A5").
Definition slotC_base : sv := ltac2:(tb__ "0|0|
S24S39S10S42S26SbZ2A1A3A2").
Definition O_slotC (cells : list cell) : sobj := ltac2:(tb__ "0|0|
S16S40SbZ10A1SbZ14A1Vcells;S14A5").
Definition O_stC (v : sv) : sobj := ltac2:(tb__ "0|3|
S4fS11PcA1Za10M0Za18S0S2S2S20S3A2M1SdA2M2S7G1SdS7S20S3G0U8A4Vv;A4S1G2A1A3A4").

Definition cptr_of : sv := ltac2:(tb__ "0|0|
S10S43S10S41S10S41S11P21A1S10S42S11PeA1SbZ20A1A3A3S30A3SbZ4A1A3").

Definition F_QC : list sprop := ltac2:(tb__ "0|2|
S4SeS4eS2cA1S0SeS19PcZ4A2S0SeS13SbZ0A1M0S11PeA1M1A2S0SeS13G1SbZ20A1A2S0SeS1bS1aS44S25G0A3A1S0SeS13S26S25A2S0SeS1cS25SbZ100A1A2S1SeA1A3A3A3A3A3A3A3").
Definition regsC : list sv := ltac2:(tb__ "0|1|
S48S47S0S2S3SdA2M0S7S3SdUbSbS3bA1A4S1G0A1A3A2").
Definition PreQC : axst := ltac2:(tb__ "0|0|
S4cS17S3dS3fS46S15S8SdA1S4ScS0ScS4dS0ScS33S26A1S0ScS34S1SfA1A1S0ScS35S2bA1S0ScS28S1ScA1A3A3A3A3A3S4bA3S32S27S6A9S1S2SdSdA2A1A2").
Definition PostQC : axst := ltac2:(tb__ "0|0|
S4cS17S38S48S47S2fA2S46S15S8SdA1S4ScS0ScS4dS0ScS33S24S26SbZ1A1A2A1S0ScS34S0SfS12SbZ10A1Z4S3eA3S1SfA1A3A1S0ScS35S24S2bS10S41SbZ0A1S2aA3A2A1S0ScS28S1ScA1A3A3A3A3A3S4bA3S32S2dS6A9S1S2SdSdA2A1A2").

Definition run_QC : list leafA := ltac2:(tb__ "0|0|
S29U258S0S20S36S0S20S37S1S20A1A3A3S31A3").
Lemma run_QC_eq : ltac2:(tb__ "0|0|
S22SaS4aA1S29U258S0S20S36S0S20S37S1S20A1A3A3S31A3S3aA3"). Proof. unfold run_QC. reflexivity. Qed.
Lemma preQC_nx : ltac2:(tb__ "0|1|
S23S22S21S1eS49S31A1M0A1S27A3S22S5S1dG0A1S6A3A2"). Proof. split; reflexivity. Qed.
Lemma chk_QC : ltac2:(tb__ "0|0|
S22S5S2eS38S3aS3cA3S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma preQC_wf : axwf PreQC = true. Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma preQC_swf : ltac2:(tb__ "0|0|
S22S5S1fS49S31A1A1S9A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End SegQC_states.

(* [comment removed for export] *)
Module InvInitP.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger"; "sepZ"; "@Corelib.Init.Datatypes"; "pair"; "cons"; "nil"; "prod"; "false"; "list"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "modulo"; "lt"; "sub"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvInitP.A0"; "A_0"; "G_0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvInitP"; "grantZ"; "pairwiseZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "FS_total"; "kPtrArrayReserve"; "PG"; "SHADOW_BAND_HI"; "IMG_HI"; "IMG_LO"; "SHADOW_BAND_LO"; "dyn_in"; "dyn_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "FBSZ"; "NBSZ"; "G0"; "@Corelib.Lists.ListDef"; "repeat"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "page_round_up_Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.IfaceEx"; "classes_fresh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_Kf"; "aa_Km"; "aa_V"; "aa_frames"; "aa_geom"; "ag_tp"; "class_state"; "cs_empty"; "large_live"; "mkAA"; "mkAG"; "qbatch"; "sec_chunk"; "small_live"; "topG"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface IfaceEx SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require PrimCredit Inv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.IfaceEx OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.PrimCredit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition grantZ (top a len : Z) : Prop := ltac2:(tb__ "0|1|
S1S2S0SdVa;S17A2Z0A3S1SbZ1000Va;A2S1SbScVa;Vlen;A2M0Vtop;A2S1S3SbG0S1aA2SbS19Va;A2A2S3SbG0S1bA2SbS18Va;A2A2A2A2A2A2").
Lemma grantZ_dyn_ok : ltac2:(tb__ "0|0|
S0S0S0S13R3R2R1A3SeZ0R2A2S1dR5R4R3A3F_;F_;Flen;Fa;Ftop;").
Proof. intros top a len (H1 & H2 & H3 & H4 & H5) Hl. split; [exact H1|]. repeat split; assumption. Qed.
Lemma grantZ_dyn_in : ltac2:(tb__ "0|0|
S0S0S0S0S13R4R3R2A3S1SeZ0R2A2SbR2R3A2A2S1cR6R5R3A3F_;F_;Flen';Flen;Fa;Ftop;").
Proof.
  intros top a len len' (H1 & H2 & H3 & H4 & H5) Hl. unfold dyn_in. split; [exact H2|]. split; [lia|]. split; [lia|].
  split; [destruct H4; [left|right]; lia | destruct H5; [left|right]; lia].
Qed.

Fixpoint pairwiseZ (l : list (Z * Z)) : Prop :=
  match l with [] => True | e :: r => Forall (sepZ e) r /\ pairwiseZ r end.

Section A0.

Variables P0 SB T C D F PAB N0 S0 STOP SP0 TOP f0 PC0 : Z.
Variable hints : list Z.

Definition G_0 : ageom := ltac2:(tb__ "0|0|
S2eVSB;VT;VC;VF;VPAB;VSTOP;SfVSTOP;Z800000A2VSP0;Z621278VD;VN0;VS0;VTOP;Ad").
Definition A_0 : AA := ltac2:(tb__ "0|4|
S2dS12S21S2aS2bU20A3S9S7S30A1VPC0;S7S8S0S0A2M0A1M1S7S2fA1M2G2S20VN0;VS0;Vf0;A3Vhints;S21SaG0A1G1UbA3S9Z0M3G3G3Af").

Hypothesis HTOP : 140735332483072 <= TOP <= 140737479966720.
Hypothesis HP0 : ltac2:(tb__ "0|0|
S1S2S0SdVP0;S17A2Z0A3S1SbS18VP0;A2SbScVP0;Z2000011000A2VTOP;A2A2A2").
Hypothesis HSB : ltac2:(tb__ "0|1|
S2S0VSB;SfScVP0;Z10000M0A2SdVP0;G0A2A2A3").
Hypothesis HgT : grantZ TOP T 4096.
Hypothesis HgC : grantZ TOP C 65536.
Hypothesis HgD : grantZ TOP D 4096.
Hypothesis HgF : ltac2:(tb__ "0|0|
S13VTOP;VF;S15A3").
Hypothesis HgPAB : ltac2:(tb__ "0|0|
S13VTOP;VPAB;S16A3").
Hypothesis HgN : ltac2:(tb__ "0|0|
S13VTOP;VN0;S1fA3").
Hypothesis HgS : ltac2:(tb__ "0|0|
S13VTOP;VS0;S1eA3").

Hypothesis HSEP : ltac2:(tb__ "0|2|
S14S6S8S0S0A2M0S5S0S0VS0;S1eA4S6G0S5S0S0VN0;S1fA4S6G0S5S0S0VF;S15A4S6G0S5S0S0VD;Z1000M1A4S6G0S5S0S0VC;Z10000A4S6G0S5S0S0VT;G1A4S6G0S5S0S0VPAB;S16A4S6G0S5S0S0VP0;Z2000011000A4S7G0A1A3A3A3A3A3A3A3A3A1").
Hypothesis HSTK : ltac2:(tb__ "0|0|
S1SbZ0SfVSTOP;Z800000A2A2SbVSTOP;S10Z2Z2fA2A2A2").

Hypothesis HSTKHB : ltac2:(tb__ "0|0|
SbVSTOP;S22ScVTOP;Z7fff60A2A1A2").

Lemma topG_0 : topG G_0 = TOP.
Proof. unfold topG, G_0. cbn [ag_top]. apply top_clamp_id. exact HTOP. Qed.

Lemma SB_range : ltac2:(tb__ "0|0|
S1S1SeVP0;VSB;A2SbVSB;ScVP0;Z10000A2A2A2S2S0SdVSB;S10Z2Z10A2A2Z0A3A2").
Proof.
  rewrite HSB. pose proof (Z.mod_pos_bound P0 65536 ltac:(lia)) as M. split; [lia|].
  change (2 ^ 16) with 65536. rewrite (Z.div_mod P0 65536) at 1 by lia.
  replace (65536 * (P0 / 65536) + P0 mod 65536 + 65536 - P0 mod 65536) with ((P0 / 65536 + 1) * 65536) by lia. apply Z.mod_mul. lia.
Qed.

Lemma seps : ltac2:(tb__ "0|9|
S1S4S5S0S0VP0;Z2000011000A4M0S5S0S0VT;Z1000M1A4M2A2S1S4G0S5S0S0VC;Z10000A4M3A2S1S4G0S5S0S0VD;G1A4M4A2S1S4G0S5S0S0VF;S15A4M5A2S1S4G0S5S0S0VPAB;S16A4M6A2S1S4G0S5S0S0VN0;S1fA4M7A2S1S4G0S5S0S0VS0;S1eA4M8A2S1S4G2G3A2S1S4G2G4A2S1S4G2G5A2S1S4G2G6A2S1S4G2G7A2S1S4G2G8A2S1S4G3G4A2S1S4G3G5A2S1S4G3G6A2S1S4G3G7A2S1S4G3G8A2S1S4G4G5A2S1S4G4G6A2S1S4G4G7A2S1S4G4G8A2S1S4G5G6A2S1S4G5G7A2S1S4G5G8A2S1S4G6G7A2S1S4G6G8A2S4G7G8A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  pose proof HSEP as H. cbn [pairwiseZ] in H.
  repeat match type of H with
         | Forall _ _ /\ _ => let F := fresh "F" in destruct H as [F H]
         end.
  repeat match goal with
         | F : Forall _ (_ :: _) |- _ => let X := fresh "X" in let F' := fresh "F" in inversion F as [|? ? X F']; subst; clear F
         | F : Forall _ [] |- _ => clear F
         end.
  assert (SYM : forall r1 r2, sepZ r1 r2 -> sepZ r2 r1) by (intros r1 r2 [E|E]; [right | left]; exact E).
  repeat split; first [assumption | apply SYM; assumption].
Qed.

Ltac sepz H := clear - H; unfold sepZ in H |- *; cbn [fst snd] in H |- *; unfold FS_total, kPtrArrayReserve, NBSZ, FBSZ in *; lia.

Theorem geom_ok_0 : geom_ok G_0.
Proof.
  pose proof seps as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & S28).
  pose proof SB_range as (SBr & SBm). destruct HP0 as (HPa & HPb & HPc). destruct HSTK as (K1 & K2).
  unfold geom_ok. rewrite topG_0. unfold G_0. cbn [ag_fsb ag_tp ag_thread ag_ctx ag_dtls ag_spacebeg ag_stack_bottom ag_stack_top ag_pab ag_top].
  assert (KS : kSpaceSize = 0x2000000000) by reflexivity.
  assert (HSE : HIGH_SHADOW_END <= SHADOW_BAND_HI) by (unfold SHADOW_BAND_HI; lia).
  split; [apply grantZ_dyn_ok; [exact HgF | reflexivity]|].
  split; [reflexivity|].
  split; [apply grantZ_dyn_ok; [exact HgT | lia]|].
  split; [apply (grantZ_dyn_in TOP C 65536); [exact HgC | lia]|].
  split; [apply (grantZ_dyn_in TOP D 4096); [exact HgD | lia]|].
  split; [exact SBm|]. split; [clear - HPb HSE SBr; lia|]. split; [clear - HPc SBr KS; lia|].
  split; [sepz S10|].
  split; [sepz S15|].
  split; [sepz S19|].
  split; [clear - S4 SBr KS; unfold sepZ in S4; cbn [fst snd] in S4; unfold FS_total in *; lia|].
  split; [sepz S8|]. split; [sepz S9|]. split; [clear - S14; unfold sepZ in S14; cbn [fst snd] in S14; lia|].
  split; [clear - K1 K2; lia|]. split; [exact (conj K2 HSTKHB)|].
  split; [exact (proj1 HgPAB) | exact HTOP].
Qed.

Theorem inv3_0 : inv3 A_0.
Proof.
  pose proof seps as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & S28).
  pose proof SB_range as (SBr & SBm).
  assert (KS : kSpaceSize = 0x2000000000) by reflexivity.
  unfold inv3. cbn [A_0 aa_geom aa_live aa_sec aa_cls aa_depot aa_q_thread aa_q_global aa_cache_inited].
  split.
  {
    unfold sep_geom3, G_0. cbn [ag_thread ag_spacebeg ag_ctx ag_dtls ag_pab ag_fsb].
    split; [clear - S1 SBr KS; unfold sepZ in S1; cbn [fst snd] in S1; lia|].
    split; [clear - S2 SBr KS; unfold sepZ in S2; cbn [fst snd] in S2; lia|].
    split; [clear - S3 SBr KS; unfold sepZ in S3; cbn [fst snd] in S3; lia|].
    split; [clear - S5 SBr KS; unfold sepZ in S5; cbn [fst snd] in S5; unfold kPtrArrayReserve in *; lia|].
    split; [sepz S11|]. split; [sepz S23|]. split; [sepz S16 | sepz S20]. }
  split; [intros b n []|]. split; [intros i ch Hi; destruct i; discriminate Hi|].
  split.
  { intros z Hq. exfalso. unfold q_foot in Hq. cbn [aa_q_thread aa_q_global A_0 app] in Hq. inversion Hq. }
  split.
  { intros bn Hbn. rewrite topG_0. unfold dblocks, G0 in Hbn. cbn [dNB dFB map app] in Hbn.
    unfold G_0. cbn [ag_thread ag_spacebeg ag_ctx ag_dtls ag_pab ag_fsb].
    destruct Hbn as [<-|[<-|[]]]; cbn [fst snd].
    - split; [apply (grantZ_dyn_in TOP N0 NBSZ); [exact HgN | unfold NBSZ; lia]|].
      split; [sepz S12|]. split; [sepz S17|]. split; [sepz S21|]. split; [sepz S24|].
      split; [clear - S6 SBr KS; unfold sepZ in *; cbn [fst snd] in *; unfold NBSZ in *; lia|]. split; [sepz S26|]. intros ch [].
    - split; [apply (grantZ_dyn_in TOP S0 FBSZ); [exact HgS | unfold FBSZ; lia]|].
      split; [sepz S13|]. split; [sepz S18|]. split; [sepz S22|]. split; [sepz S25|].
      split; [clear - S7 SBr KS; unfold sepZ in *; cbn [fst snd] in *; unfold FBSZ in *; lia|]. split; [sepz S27|]. intros ch []. }
  split; [cbn; constructor|].
  split; [unfold large_live, qlarge, qall; cbn; lia|].
  split; [unfold small_live, PRIM_LIVE_MAX; cbn; lia|].
  intros H. exfalso. apply H. reflexivity.
Qed.

Lemma A0_pure : ltac2:(tb__ "0|4|
S1S2S0S29S28S11A1M0A1Z621278A3S1S2S0S32G0A1VTOP;A3S1S2SaS8S0S0A2M1A1S27S11A1S7G1A1A3S1S1S1SbZ0M2S26S11A1M3A2SbG3Z10000A2A2S1S2S0S25S11A1G2A3S2S0S24S11A1G2A3A2A2S1S23S11A1S1S2S0S2cS11A1G2A3S2S0S31S11A1G2A3A2A2A2A2A2A2").
Proof.
  split; [reflexivity|]. split; [exact topG_0|]. split; [reflexivity|]. split; [cbn; lia|].
  split; [|split; reflexivity].
  intros c Hc. unfold class_fresh. cbn [A_0 aa_cls]. apply nth_repeat.
Qed.
End A0.
End InvInitP.

(* [comment removed for export] *)
Module InvIA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "cell_ok"; "c_addr"; "acell"; "view"; "c_w"; "@Corelib.Init.Logic"; "eq"; "not"; "and"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "of_nat"; "@Corelib.Init.Datatypes"; "list"; "prod"; "option"; "bool"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.InvIA.WithSegs"; "agree_nz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_geom"; "aa_sec"; "qbatch"; "aa_cls"; "ageom"; "aa_live"; "class_state"; "sec_chunk"; "aa_cache_inited"; "aa_ptr_committed"; "aa_q_global"; "aa_q_thread"; "DG"; "ag_thread"; "qb_addr"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "ia_zone"; "qhdr_repr"; "IA_BEG"; "alloc_magic_ok"; "batch_repr"; "class_repr"; "depot_wf"; "live_block_repr"; "q_item_ok"; "qlinks"; "set_inited"; "geom_ok"; "ia_inv"; "live_sep"; "quarantine_repr"; "secondary_repr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "dyn_in"; "IMG_LO"; "Sh"; "max_count"; "rz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "valuation"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "qall"; "@Corelib.Lists.ListDef"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf"; "DFP"; "depot_mem"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymFrame SymEntail Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Iface SegQ_defs SegD_wf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Inv.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_wf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.Ledger OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Local Ltac lia := first [Stdlib.micromega.Lia.lia | unfold IMG_HI, IMG_LO, IA_BEG, IA_END, SHADOW_OFF, PG in *; Stdlib.micromega.Lia.lia].

Section WithSegs.
Variable segs : list Segment.
Let AInvA := AInvA segs.

Definition agree_nz (m m' : bview) : Prop := ltac2:(tb__ "0|0|
S0S8S25R1A1A1S7S11S3dQ8A1A1Vm';R2A1Vm;R2A1A3F_;Fz;").

Lemma nz_below : ltac2:(tb__ "0|0|
S0SdR1S27A2S8S25R2A1A1F_;Fz;").
Proof. intros z Hz. unfold ia_zone, IA_BEG, IA_END in *. lia. Qed.
Lemma nz_above : ltac2:(tb__ "0|0|
S0SbS35R1A2S8S25R2A1A1F_;Fz;").
Proof. intros z Hz. unfold ia_zone, IA_BEG, IA_END, IMG_HI in *. lia. Qed.
Lemma nz_band : ltac2:(tb__ "0|0|
S0SaSdR1S37A2SbS35R1A2A2S8S25R2A1A1F_;Fz;").
Proof. intros z Hz. unfold ia_zone, IA_BEG, IA_END, IMG_LO, IMG_HI in *. lia. Qed.
Lemma nz_dyn : ltac2:(tb__ "0|0|
S0S0S0S0S36R4R3R2A3S9SbR4R2A2SdR2ScR4R3A2A2A2S8S25R3A1A1F_;F_;Fz;Flen;Fa;Ftop;").
Proof. intros top a len z (_ & _ & _ & HB & _) Hz. apply nz_band. lia. Qed.

Lemma nz_depot : ltac2:(tb__ "0|0|
S21S1S0S42R3R2A2S41R4R2A2S8S25R3A1A1F_;F_;Fz;Fm;FG;").
Proof.
  intros G m z HD Hz. destruct Hz as [Hs|[(b & Hb & Hzb)|(b & Hb & Hzb)]].
  - unfold dfp_static, DEPOT, MAP1, MAP1N, STORE, NFBLK in Hs. unfold ia_zone, IA_BEG, IA_END. lia.
  - destruct (dm_nb _ _ HD b Hb) as (_ & H1 & _). apply nz_above. lia.
  - destruct (dm_fbases _ _ HD b Hb) as (_ & H1 & _). apply nz_above. lia.
Qed.
Lemma depot_wf_nz : ltac2:(tb__ "0|0|
S1S1S14S13R3R2A2S2bR4R2A2S2bR4R3A2F_;F_;FA;Fm';Fm;").
Proof.
  intros m m' A AH HD. unfold depot_wf in *. eapply depot_mem_frame; [|exact HD]. intros a Ha. apply AH. eapply nz_depot; [exact HD | exact Ha].
Qed.

Lemma rz_bound : ltac2:(tb__ "0|1|
S0S9SbZ10S3aR1A1M0A2SbG0Z800A2A2Fn;").
Proof.
  intros n. unfold rz, rz_log.
  repeat (destruct (n <=? _); [rewrite Z.shiftl_mul_pow2 by lia; cbn; lia|]). rewrite Z.shiftl_mul_pow2 by lia. cbn. lia.
Qed.

Lemma max_count_le : ltac2:(tb__ "0|0|
S0SbS39R1A1Z10A2Fc;").
Proof. intros c. unfold max_count, MaxCachedHint, kMaxNumCachedHint. pose proof (Z.le_min_l 8 (Z.max 1 (kMaxBytesCached / Size c))). lia. Qed.

Lemma cell_ok_agree_above : ltac2:(tb__ "0|0|
S1S1S4S13R3R2A2SbS35S3R2A1A2S2R5R3A2S2R5R4A2F_;F_;F_;Fc;Fm';Fm;").
Proof. intros m m' c AH Hc. apply cell_ok_agree. intros k Hk. apply AH. apply nz_above. lia. Qed.
Lemma cell_ok_agree_below : ltac2:(tb__ "0|0|
S1S1S4S13R3R2A2SbScS3R2A1SeS6R2A1A1A2S27A2S2R5R3A2S2R5R4A2F_;F_;F_;Fc;Fm';Fm;").
Proof. intros m m' c AL H2. apply cell_ok_agree. intros k Hk. apply AL. apply nz_below. lia. Qed.
Lemma cell_ok_agree_dyn : ltac2:(tb__ "0|0|
S1S1S4S0S0S0S13R6R5A2S36R4R3R2A3SbR4S3R6A1A2SbScS3R7A1SeS6R7A1A1A2ScR5R4A2A2S2RaR8A2S2RaR9A2F_;F_;F_;F_;F_;Flen;Fa;Ftop;Fc;Fm';Fm;").
Proof. intros m m' c top a len AH HD H1 H2. apply cell_ok_agree. intros k Hk. apply AH. eapply nz_dyn; [exact HD | lia]. Qed.

Lemma alloc_magic_ok_nz : ltac2:(tb__ "0|0|
S1S1S0S0S13R4R3A2SbScS35Z800A2R3A2S28R6R4R3A3S28R6R5R4A3F_;F_;F_;Fn;Fb;Fm';Fm;").
Proof.
  intros m m' b n AH Hb [H|[H1 H2]]; [left; exact H|right]. pose proof (rz_bound n) as RZ.
  split; (eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | assumption]).
Qed.

Lemma Sh_above : ltac2:(tb__ "0|0|
S0SbZ0R1A2SbS35S38R2A1A2F_;Fa;").
Proof. intros a Ha. unfold Sh, SHADOW_OFF, IMG_HI. pose proof (Z.div_pos a 8 Ha ltac:(lia)). lia. Qed.

Lemma live_block_repr_nz : ltac2:(tb__ "0|0|
S1S1S14S32R1A1S13R4R3A2S2cR5R3A2S2cR5R4A2F_;F_;F_;FA;Fm';Fm;").
Proof.
  intros m m' A Hsep AH Hlive b n Hin.
  destruct (Hlive b n Hin) as (L1 & L2 & L3 & L4 & L5 & L6). destruct (Hsep b n Hin) as (S1 & S2 & S3 & _).
  pose proof (rz_bound n) as RZ.
  split; [rewrite AH by (apply nz_above; lia); exact L1|].
  split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact L2]|].
  split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact L3]|].
  split.
  - destruct L4 as [L4a L4b]. pose proof (Sh_above b ltac:(lia)) as SB. split.
    + intros g Hg. rewrite AH by (apply nz_above; lia). exact (L4a g Hg).
    + intros Hn. rewrite AH by (apply nz_above; pose proof (Z.div_pos n 8); lia). exact (L4b Hn).
  - split; [eapply alloc_magic_ok_nz; [exact AH | lia | exact L5]|].
    destruct L6 as (t & Ht & Hm4). exists t. split; [rewrite AH by (apply nz_above; lia); exact Ht | exact Hm4].
Qed.

Lemma class_repr_nz : ltac2:(tb__ "0|0|
S1S1S19S14S14S0S1bS30R5A1S9SbZ1R3A2SbR3Z1eA2A2S7S12S1dR5A1S1dR6A1A3S7SfS10S0S0A2A1S1aR6A1S1aR7A1A3S7SfS17A1S3eR7A1S3eR8A1A3S13RcRbA2S2aRdRbRaR8R7A5S2aRdRcRaR9R8A5F_;F_;F_;F_;F_;F_;F_;Fcs;Fc;FA';FA;FG;Fm';Fm;").
Proof.
  intros m m' G A A' c cs HG Hc Hci Hlv Hq AH P4.
  pose proof (geom_nums G HG) as (_ & _ & _ & T1 & T2 & _ & _ & _ & _ & _ & S1 & S2 & S0 & TG).
  pose proof HG as (_ & _ & (_ & TD) & _).
  unfold HIGH_SHADOW_END in S1. rewrite kSpaceSize_val in S2.
  assert (CA : forall c, IMG_HI <= c_addr c -> cell_ok m c -> cell_ok m' c).
  { intros c0 Hc0. apply cell_ok_agree_above; [exact AH | exact Hc0]. }
  assert (CT : forall c, ag_thread G <= c_addr c -> c_addr c + Z.of_nat (c_w c) <= ag_thread G + 0x1000 -> cell_ok m c -> cell_ok m' c).
  { intros c0 H1 H2. eapply cell_ok_agree_dyn; [exact AH | exact TD | exact H1 | exact H2]. }
  unfold class_repr in P4 |- *. rewrite Hci.
  set (ri := region_info (ag_spacebeg G) c) in *. set (fa := free_array (ag_spacebeg G) c) in *.
  assert (RI : IMG_HI <= ri) by (unfold ri, region_info; rewrite kSpaceSize_val; unfold kRegionInfoStride, IMG_HI; lia).
  assert (FA : IMG_HI <= fa) by (unfold fa, free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize, IMG_HI; lia).
  unfold live_ids. rewrite Hlv, Hq.
  destruct P4 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & PRI & N1 & N2 & N3 & N4 & N5 & N6 & C9 & PR & N7 & PU & PS & PE & ND & LV & CI & CN & TI10 & CV10 & MC10 & FC10).
  set (rb := region_beg (ag_spacebeg G) c) in *.
  assert (RB : IMG_HI <= rb) by (unfold rb, region_beg, kRegionSize, IMG_HI; lia).
  split; [apply CA; [cbn [c_addr]; unfold RI_mutex; lia | exact C1]|].
  split; [apply CA; [cbn [c_addr]; unfold RI_num_freed; lia | exact C2]|].
  split; [apply CA; [cbn [c_addr]; unfold RI_mapped_free_array; lia | exact C3]|].
  split; [apply CA; [cbn [c_addr]; unfold RI_allocated_user; lia | exact C4]|].
  split; [apply CA; [cbn [c_addr]; unfold RI_allocated_meta; lia | exact C5]|].
  split; [apply CA; [cbn [c_addr]; unfold RI_mapped_user; lia | exact C6]|].
  split; [apply CA; [cbn [c_addr]; unfold RI_mapped_meta; lia | exact C7]|].
  split; [apply CA; [cbn [c_addr]; unfold RI_exhausted; lia | exact C8]|].
  split; [eapply present_agree; [|exact PRI]; intros z Hz; apply AH; apply nz_above; lia|].
  split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|]. split; [exact N5|]. split; [exact N6|].
  split; [intros i x Hi; apply CA; [cbn [c_addr]; lia | exact (C9 i x Hi)]|].
  split; [eapply present_agree; [|exact PR]; intros z Hz; apply AH; apply nz_above; lia|].
  split; [exact N7|].
  split; [eapply present_but_agree; [|exact PU]; intros z Hz _; apply AH; apply nz_above; lia|].
  split; [eapply present_agree; [|exact PS]; intros z Hz; apply AH; apply nz_above; pose proof (Sh_above rb ltac:(lia)); lia|].
  split; [eapply present_agree; [|exact PE]; intros z Hz; apply AH; eapply nz_dyn; [exact TD | lia]|].
  split; [exact ND|]. split; [exact LV|].
  split.
  - intros Hx. destruct (CI Hx) as (D1 & D2 & D3 & D4 & D5).
    split; [apply CT; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact D1]|].
    split; [apply CT; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact D2]|].
    split; [apply CT; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact D3]|]. split; [|exact D5].
    intros i x Hi. assert (Li : (i < length (cs_cache cs))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    pose proof (max_count_le c) as MC.
    apply CT; [cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact (D4 i x Hi)].
  - split; [|exact (conj TI10 (conj CV10 (conj MC10 FC10)))].
    intros Hx. destruct (CN Hx) as [D1 D2]. split; [exact D1|]. eapply filled_agree; [|exact D2]. intros z Hz. apply AH. eapply nz_dyn; [exact TD | lia].
Qed.

Lemma secondary_repr_nz : ltac2:(tb__ "0|1|
S1S1S14S14S7S19S15R1A1S15R2A1A3S7SfS1cA1S16R2A1S16R3A1A3S7S0S1eR3A1S1eR4A1A3S7SfS10S0S0A2A1S1aR4A1S1aR5A1A3S13R8R7A2S34R9R7A2M0G0F_;F_;F_;F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' Eg Es Ep El AH (S1 & SP & S2 & S3 & S4 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold secondary_repr. rewrite Eg, Es, Ep, El.
  pose proof (dyn_ok_big _ _ _ S4 ltac:(unfold kPtrArrayReserve; lia)) as PB.
  split.
  { intros i ch Hi. destruct (S1 i ch Hi) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    pose proof (dyn_in_big _ _ _ D10 ltac:(unfold PG in *; lia)) as CB.
    assert (Li : (i < length (aa_sec A))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact D1]|].
    split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact D2]|].
    split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact D3]|].
    split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact D4]|].
    split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact D5]|].
    split; [exact D6|]. split; [exact D7|]. split; [exact D8|]. split; [exact D9|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|].
    split; [eapply present_but_agree; [|exact D13]; intros z Hz _; apply AH; apply nz_above; lia|].
    eapply present_agree; [|exact D14]. intros z Hz. apply AH. apply nz_above. pose proof (Sh_above (sc_map_beg ch) ltac:(lia)). lia. }
  split; [eapply present_agree; [|exact SP]; intros z Hz; apply AH; apply nz_above; unfold kPtrArrayReserve in *; lia|].
  split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
  unfold SEC_INST in *.
  split; [eapply cell_ok_agree_below; [exact AH | cbn [c_addr c_w Z.of_nat]; unfold IA_BEG; lia | exact I1]|].
  split; [eapply cell_ok_agree_below; [exact AH | cbn [c_addr c_w Z.of_nat]; unfold IA_BEG; lia | exact I2]|].
  split; [eapply cell_ok_agree_below; [exact AH | cbn [c_addr c_w Z.of_nat]; unfold IA_BEG; lia | exact I3]|].
  split; [eapply cell_ok_agree_below; [exact AH | cbn [c_addr c_w Z.of_nat]; unfold IA_BEG; lia | exact I4]|].
  split; [eapply cell_ok_agree_below; [exact AH | cbn [c_addr c_w Z.of_nat]; unfold IA_BEG; lia | exact I5]|].
  split; [eapply cell_ok_agree_below; [exact AH | cbn [c_addr c_w Z.of_nat]; unfold IA_BEG; lia | exact I6]|].
  split; [eapply present_agree; [|exact I7]; intros z Hz; apply AH; apply nz_below; unfold IA_BEG; lia|].
  split; [eapply cell_ok_agree_below; [exact AH | cbn [c_addr c_w Z.of_nat]; unfold IA_BEG; lia | exact I8]|].
  eapply present_agree; [|exact I9]; intros z Hz; apply AH; apply nz_below; unfold IA_BEG; lia.
Qed.

Lemma q_item_ok_nz : ltac2:(tb__ "0|0|
S1S1S14S14S10S0S0A2S7S19S15R2A1S15R3A1A3S7SfS1bA1S18R3A1S18R4A1A3S7SfS1cA1S16R4A1S16R5A1A3S13R8R7A2S2dR9R7R5A3S2dR9R7R6A3F_;F_;F_;F_;F_;Fit;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' it Eg Ec Es AH HQ. unfold q_item_ok in HQ |- *. cbn zeta in HQ |- *. rewrite Eg, Ec, Es.
  destruct HQ as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  split; [exact Q1|]. split; [exact Q2|].
  split; [rewrite AH by (apply nz_above; lia); exact Q3|].
  split; [eapply present_agree; [|exact Q4]; intros z Hz; apply AH; apply nz_above; lia|].
  split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact Q5]|].
  split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact Q6]|].
  split; [eapply present_agree; [|exact Q7]; intros z Hz; apply AH; apply nz_above; lia|].
  split; [eapply alloc_magic_ok_nz; [exact AH | lia | exact Q8]|].
  split; [exact Q9|]. split; [exact Q10|].
  pose proof (Sh_above (fst it) ltac:(lia)).
  eapply present_agree; [|exact Q11]. intros z Hz. apply AH. apply nz_above. lia.
Qed.

Lemma batch_repr_nz : ltac2:(tb__ "0|0|
S1S1S14S14S17S7S19S15R2A1S15R3A1A3S7SfS1bA1S18R3A1S18R4A1A3S7SfS1cA1S16R4A1S16R5A1A3S13R8R7A2S29R9R7R5A3S29R9R7R6A3F_;F_;F_;F_;F_;Fb;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' b Eg Ec Es AH (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
  unfold batch_repr. rewrite Eg, Ec.
  split; [exact B0|].
  split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact B1]|].
  split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact B2]|].
  split; [exact B3|]. split; [exact B4|].
  split; [eapply present_agree; [|exact B5]; intros z Hz; apply AH; apply nz_above; lia|].
  split; [|exact B7].
  intros i it Hi. destruct (B6 i it Hi) as [I1 I2].
  split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact I1]|].
  eapply (q_item_ok_nz m m' A A'); auto.
Qed.

Lemma qlinks_nz : ltac2:(tb__ "0|0|
S1S1SfS17A1S13R3R2A2S3fS17S17SbS35S23R1A1A2Lb;R2A3S2eR5R3A2S2eR5R4A2F_;F_;F_;Fl;Fm';Fm;").
Proof.
  intros m m' l AH. induction l as [|b r IH]; intros HF H; [exact I|]. cbn in H |- *. destruct H as [H1 H2].
  inversion HF as [|b0 r0 Hb Hr]; subst.
  split; [eapply cell_ok_agree_above; [exact AH | cbn [c_addr]; lia | exact H1] | exact (IH Hr H2)].
Qed.

Lemma qhdr_repr_dyn : ltac2:(tb__ "0|0|
S1S1S0S0S0S0SfS17A1S13R7R6A2S36R6R5R4A3SbR6R4A2SbScR5Z20A2ScR7R6A2A2S26RbR6R5A3S26RbR7R6A3F_;F_;F_;F_;F_;Fl;Fhdr;Flen;Fa;Ftop;Fm';Fm;").
Proof.
  intros m m' top a len hdr l AH HD H0 H1 (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
  split; [eapply cell_ok_agree_dyn; [exact AH | exact HD | cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact Q1]|].
  split; [intros Hl; destruct (Q2 Hl) as [X Y]; split; (eapply cell_ok_agree_dyn; [exact AH | exact HD | cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | assumption])|].
  split; [eapply present_agree; [|exact Q3]; intros z Hz; apply AH; eapply nz_dyn; [exact HD | lia]|].
  eapply cell_ok_agree_dyn; [exact AH | exact HD | cbn [c_addr]; lia | cbn [c_addr c_w Z.of_nat]; lia | exact Q4].
Qed.
Lemma qhdr_repr_below : ltac2:(tb__ "0|0|
S1S1S0SfS17A1S13R4R3A2SbScR3Z20A2S27A2S26R6R4R3A3S26R6R5R4A3F_;F_;F_;Fl;Fhdr;Fm';Fm;").
Proof.
  intros m m' hdr l AL H1 (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
  split; [eapply cell_ok_agree_below; [exact AL | cbn [c_addr c_w Z.of_nat]; lia | exact Q1]|].
  split; [intros Hl; destruct (Q2 Hl) as [X Y]; split; (eapply cell_ok_agree_below; [exact AL | cbn [c_addr c_w Z.of_nat]; lia | assumption])|].
  split; [eapply present_agree; [|exact Q3]; intros z Hz; apply AL; apply nz_below; lia|].
  eapply cell_ok_agree_below; [exact AL | cbn [c_addr c_w Z.of_nat]; lia | exact Q4].
Qed.

Lemma quarantine_repr_nz : ltac2:(tb__ "0|3|
S1S1S14S14S7S19S15R1A1S15R2A1A3S7SfS1bA1S18R2A1S18R3A1A3S7SfS1cA1S16R3A1S16R4A1A3S7SfS17A1M0S20R4A1S20R5A1A3S7G0S1fR5A1S1fR6A1A3S36S24S15R7A1M1A1S22G1A1Z1000A3S13RaR9A2S33RbR9A2M2G2F_;F_;F_;F_;F_;F_;F_;F_;FA';FA;Fm';Fm;").
Proof.
  intros m m' A A' Eg Ec Es E1 E2 HT AH (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9). unfold quarantine_repr. rewrite Eg, E1, E2.
  assert (HB : Forall (fun b => IMG_HI <= qb_addr b) (aa_q_thread A ++ aa_q_global A)).
  { apply Forall_forall. intros b Hb. exact (proj1 (proj1 (Forall_forall _ _) Q1 b Hb)). }
  pose proof (proj1 (Forall_app _ _ _) HB) as [HB1 HB2].
  split; [apply Forall_forall; intros b Hb; apply (batch_repr_nz m m' A A' b Eg Ec Es AH); exact (proj1 (Forall_forall _ _) Q1 b Hb)|].
  split; [exact (qlinks_nz m m' _ AH HB1 Q2)|]. split; [exact (qlinks_nz m m' _ AH HB2 Q3)|].
  split; [apply (qhdr_repr_dyn m m' _ _ _ _ _ AH HT); [lia | lia | exact Q4]|].
  split; [apply (qhdr_repr_below m m'); [exact AH | unfold QG, IA_BEG; lia | exact Q5]|].
  split; [eapply cell_ok_agree_below; [exact AH | cbn [c_addr c_w Z.of_nat]; unfold QG, IA_BEG; lia | exact Q6]|].
  split; [eapply cell_ok_agree_below; [exact AH | cbn [c_addr c_w Z.of_nat]; unfold QG, IA_BEG; lia | exact Q7]|].
  split; [exact Q8|]. exact Q9.
Qed.

Lemma AInvA_ia_update : ltac2:(tb__ "0|0|
S14S3cS3cSfS3dQ40A1A1S40VAInvA;R5R4R2R1A4S0S8S25R1A1A1S7S11S3dQ8A1A1S5Vsegs;S3bR6A1R2A3S5Vsegs;S3bR7A1R2A3A3F_;Fz;S31S5Vsegs;S3bR5A1A2S2fR7A1A2VAInvA;S2fR8A1R6R5R4A4F_;F_;F_;Fmd;Ftp;Frho';Frho;FA;").
Proof.
  intros A rho rho' tp md HA Hout HIA'. pose proof HA as (HG & HR & HF & HRest & HM).
  pose proof (geom_nums (aa_geom A) HG) as (F1 & F2 & F0 & T1 & T2 & T0 & C1 & C2 & D1 & D2 & S1 & S2 & S0 & TG).
  pose proof HG as ((_ & FD) & _ & (_ & TD) & CD & DD & _).
  rewrite FS_total_val in F2, FD.
  assert (AH : agree_nz (view segs (rm rho)) (view segs (rm rho'))) by (intros z Hz; apply Hout; exact Hz).
  assert (AHM : agree_nz (maskv (fs_footb (aa_geom A)) (view segs (rm rho))) (maskv (fs_footb (aa_geom A)) (view segs (rm rho')))).
  { intros z Hz. unfold maskv. destruct (fs_footb (aa_geom A) z); [reflexivity | exact (AH z Hz)]. }
  unfold AInvA, Inv.AInvA. cbn [aa_geom set_inited].
  split; [exact HG|]. split.
  {   eapply cells_ok_frame; [|exact HR]. intros z Hz. apply Hout.
    unfold cells_footb in Hz. apply existsb_exists in Hz as (c & Hc & Hin). unfold in_cellb in Hin.
    apply andb_prop in Hin as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
    unfold rtc_cells in Hc. apply in_app_or in Hc as [Hc|Hc].
    - destruct (rtc_cells_img_lt _ _ Hc) as [X Y]. unfold ia_zone. lia.
    - unfold rtc_cells_geom in Hc.
      repeat (destruct Hc as [<-|Hc]; [cbn [c_addr c_w Z.of_nat] in Hlo, Hhi; unfold fs_log_cell, fs_needs_gc_cell in *;
        first [ eapply nz_dyn; [exact CD | lia] | eapply nz_dyn; [exact TD | lia] | eapply nz_dyn; [exact DD | lia] | eapply nz_dyn; [exact FD | lia] ] |]).
      destruct Hc. }
  split.
  {
    assert (E : restrictv (fs_footb (aa_geom A)) (view segs (rm rho')) = restrictv (fs_footb (aa_geom A)) (view segs (rm rho))).
    { apply restrictv_ext. intros z Hz. apply Hout.

      unfold fs_footb in Hz. apply orb_prop in Hz as [Hz|Hz]; [apply orb_prop in Hz as [Hz|Hz]|];
        apply andb_prop in Hz as [B1 B2]; apply Z.leb_le in B1; apply Z.ltb_lt in B2.
      - eapply nz_dyn; [exact FD | lia].
      - rewrite FS_kFlagsOffset_val in B1. rewrite FS_total_val in B2. eapply nz_dyn; [exact FD | lia].
      - rewrite FS_frames_off_val in B1. apply nz_above. pose proof (Sh_above (ag_fsb (aa_geom A) + 36864) ltac:(lia)). lia. }
    rewrite E. exact HF. }
  split; [|destruct HM as (HM1 & HM2 & HB); split; [exact HM1|]; split; [exact HM2|];

           eapply bandtp_agree; [|exact HB]; intros z Hz; apply Hout;
           unfold ia_zone, IA_BEG, IA_END, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *; clear -Hz; lia].
  destruct HRest as (Hsep & Hlive & Hprim & Hsec & Hq & Hdep & _ & Hth & Hmi).
  unfold rest_inv. cbn [aa_geom aa_live set_inited].
  split; [exact Hsep|].
  split; [exact (live_block_repr_nz _ _ A Hsep AHM Hlive)|].
  split.
  { destruct Hprim as (P1 & P2 & P3 & P4). unfold primary_repr. cbn [aa_cls aa_geom set_inited].
    split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
    intros c Hc. apply (class_repr_nz _ _ (aa_geom A) A (set_inited A) c _ HG Hc eq_refl eq_refl eq_refl AHM). exact (P4 c Hc). }
  split; [exact (secondary_repr_nz _ _ A (set_inited A) eq_refl eq_refl eq_refl eq_refl AHM Hsec)|].
  split; [exact (quarantine_repr_nz _ _ A (set_inited A) eq_refl eq_refl eq_refl eq_refl eq_refl TD AHM Hq)|].
  split; [exact (depot_wf_nz _ _ A AHM Hdep)|]. split.
  { assert (MV : forall z, z < IMG_HI -> maskv (fs_footb (aa_geom A)) (view segs (rm rho')) z = view segs (rm rho') z).
    { intros z Hz. apply maskv_out.
      pose proof (Sh_above (ag_fsb (aa_geom A) + FS_frames_off) ltac:(rewrite FS_frames_off_val; lia)).
      apply fs_footb_false_intro; rewrite ?FS_total_val, ?FS_kFlagsOffset_val; lia. }
    unfold ia_inv in HIA' |- *. cbn [aa_internal_inited set_inited] in HIA' |- *.
    destruct HIA' as (X1 & X2 & X3 & X4 & X5). unfold IMG_HI in MV.
    split; [rewrite MV by lia; exact X1|]. split; [rewrite MV by lia; exact X2|]. split; [rewrite MV by lia; exact X3|].
    split; [rewrite MV by lia; exact X4|].
    intros z Hz. rewrite MV by (unfold IA_MAP1, IA_MAP1_SZ in Hz; lia). exact (X5 z Hz). }
  split.
  { unfold thread_inv in Hth |- *. destruct Hth as [Hth1 Hth2].
    split; [rewrite AHM by (eapply nz_dyn; [exact TD | lia]); exact Hth1|].
    eapply present_agree; [|exact Hth2]. intros z Hz. apply AHM. eapply nz_dyn; [exact TD | lia]. }

  destruct Hmi as (Hc & Hp & He). unfold misc_inv. split; [|split].
  - eapply cells_ok_frame; [|exact Hc]. intros z Hz. unfold maskv. rewrite Hout; [reflexivity|].
    unfold cells_footb, rtc_extra in Hz. cbn [existsb in_cellb c_addr c_w Z.of_nat] in Hz.
    unfold ia_zone, IA_BEG, IA_END. intros Hiz.
    repeat (apply orb_prop in Hz as [Hz|Hz]); try discriminate Hz;
      unfold in_cellb in Hz; cbn [c_addr c_w Z.of_nat] in Hz;
      apply andb_prop in Hz as [B1 B2]; apply Z.leb_le in B1; apply Z.ltb_lt in B2; lia.
  - eapply present_agree; [|exact Hp]. intros z Hz. unfold maskv. rewrite Hout; [reflexivity|].
    unfold ia_zone, IA_BEG, IA_END. lia.
  - eapply present_agree; [|exact He]. intros z Hz. unfold maskv. rewrite Hout; [reflexivity|].
    unfold ia_zone, IA_BEG, IA_END, ERRNO_A in *. lia.
Qed.
End WithSegs.
End InvIA.

(* [comment removed for export] *)
Module GlueMA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "of_nat"; "eqb"; "div"; "opp"; "to_nat"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "not"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "gsv"; "@Corelib.Init.Datatypes"; "option"; "Some"; "bool"; "nat"; "true"; "list"; "None"; "fst"; "prod"; "app"; "pair"; "cons"; "false"; "length"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "rd_of"; "wok_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "acell"; "mkACell"; "view"; "RTC_A"; "cell_ok"; "rtc_cells"; "cells_ok"; "bview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "valuation"; "enc_bytes"; "sv"; "SLit"; "image_byte"; "obj_range"; "cell"; "holds"; "mkObj"; "odefault"; "rw"; "smatch"; "sobj"; "ss_objs"; "sstate"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "ageom"; "ag_fsb"; "AA"; "aa_fs_busy"; "aa_geom"; "fs_release"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Lists.ListDef"; "nth"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "fs_busy"; "fs_footb"; "@Stdlib.Lists.List"; "In"; "nth_error"; "existsb"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "find_segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "FS_total"; "Sh"; "FS_frames_off"; "FS_kFlagsOffset"; "fs_frame"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "stack_win"; "F_sp_high"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundM SymSoundR SymSoundV SymSoundL SymObj SymFrame SymEntail SymCFG SymSummary SymCall Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface Inv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma stack_win_range : ltac2:(tb__ "0|3|
S19S3dA1S2eS3cS1cS19S55A1S54A2S39R4R3R2R1A4S49S3aS52S3bR3A1A3S35R5S53A2SbS1Z7fff7f800000S1bS0S0S33R6S52A2M0A3M1A2SbSaS0S22S0S0G0A3M2S11Q40S38R6PaA2A2A3S1G1G2A2A2A2F_;F_;F_;Fw;FS;Frho;Fsegs;").
Proof.
  intros segs rho S w Hsm Hin Hf.
  destruct Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hall & _ & _) & _).
  pose proof (proj1 (Forall_forall _ _) Hall _ Hin) as Ho.
  unfold obj_holds, obj_lo_of, obj_hi_of, stack_win in Ho. cbn [ob_base ob_lo ob_hi] in Ho.
  destruct Ho as ((B1 & B2 & B3 & B4) & _).
  unfold obj_range, obj_lo_of, obj_hi_of, stack_win. cbn [ob_base ob_lo ob_hi fst snd].
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

Lemma obj_range_mk : ltac2:(tb__ "0|2|
S2eS30S0S0S19S34A1S37S1S8S4Z2Z3fA2M0A1R4A2S1R5R4A2S3R5G0A2SaS1cS0S0A2S33R9S36R8S31R7A1S31R6A1R5R4A5A2S1eS0S0S2S11Q40S2dR9R8A2A2M1R7A2S2G1R6A2A4A3F_;F_;F_;Fd;Fcs;Fhi;Flo;Fbase;Frho;").
Proof.
  intros. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite !soff_lit_small by lia. reflexivity.
Qed.

Lemma cells_ok_nth : ltac2:(tb__ "0|0|
S2cS19S25A1S17S25S2bR4R3A2SaS14S25A1S4aS25R4R3A3S15S25R2A2A3S29R6R3A2F_;F_;Fc;Fi;Fcs;Fm;").
Proof. intros m cs i c H Hn. exact (proj1 (Forall_forall _ _) H c (nth_error_In _ _ Hn)). Qed.

Lemma wok_of_imageA : ltac2:(tb__ "0|1|
S10Q40M0A1S14S10Q8A1A1F_;S0SbS1Ze1000R1A2S3R1Z643000A2A2SaS16S24S12R3SfG0R2A2A3S18A3F_;Fz;Fm;").
Proof.
  intros m z Hz. unfold wok_of. destruct (m (Z_to_bv 64 z)); [reflexivity|].
  unfold wseg_addr. rewrite u64_lit by lia.
  destruct (byte_cond_A z Hz) as [_ (seg & b & Hf & Hw & _)].
  change ImageFacts.segsA with segsA in Hf. rewrite Hf. exact Hw.
Qed.

Lemma find_segment_A_off : ltac2:(tb__ "0|0|
S0S1Z643000R1A2SaS14S3dA1S4cS12R2Z1A3S1aS3dA1A3F_;Fx;").
Proof.
  intros x Hx. unfold segsA. cbn -[Z.leb Z.ltb Z.add Z.of_N].
  change (Z.of_N 65536%N) with 65536. change (Z.of_N 176128%N) with 176128.
  change (Z.of_N 241664%N) with 241664. change (Z.of_N 679936%N) with 679936.
  change (Z.of_N 921600%N) with 921600. change (Z.of_N 20480%N) with 20480.
  change (Z.of_N 942080%N) with 942080. change (Z.of_N 5623808%N) with 5623808.
  destruct (Z.leb_spec 65536 x); destruct (Z.leb_spec (x + 1) (65536 + 176128)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec 241664 x); destruct (Z.leb_spec (x + 1) (241664 + 679936)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec 921600 x); destruct (Z.leb_spec (x + 1) (921600 + 20480)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec 942080 x); destruct (Z.leb_spec (x + 1) (942080 + 5623808)); cbn [andb]; try lia; reflexivity.
Qed.

Lemma image_byte_A_off : ltac2:(tb__ "0|1|
S0SbS1Z643000R1A2S3R1S4Z2Z40A2A2A2SaS14S10Q8A1M0A1S32S12SfQ40R2A2A2S1aG0A1A3F_;Fx;").
Proof.
  intros x Hx. unfold image_byte, memory_read. rewrite u64_lit by lia.
  change (Z.of_N 1) with 1. rewrite find_segment_A_off by lia. reflexivity.
Qed.

Lemma rd_off_image : ltac2:(tb__ "0|3|
S10Q40M0A1S14S10Q8A1M1A1M2F_;S0G1SbS1Z643000R2A2S3R2S4Z2Z40A2A2A2SaG2S23S12R4SfG0R3A2A3S15G1R2A2A3SaG2R5SfG0R4A2A1S15G1R3A2A3F_;F_;Fx;Fz;Fm;").
Proof.
  intros m z x Hz H. unfold rd_of in H. destruct (m (Z_to_bv 64 z)); [exact H|].
  rewrite image_byte_A_off in H by lia. discriminate.
Qed.

Lemma wok_rd_off_image : ltac2:(tb__ "0|3|
S10Q40M0A1S14S10Q8A1M1A1M2F_;S0G1SbS1Z643000R2A2S3R2S4Z2Z40A2A2A2SaG2S23S12R4SfG0R3A2A3S15G1R2A2A3SbSaS16S24S12R5SfG0R4A2A3S18A3ScG1G1SaG2S23S12R6SfG0R5A2A3S15G1R1A2A3Ly;A2A2F_;F_;Fx;Fz;Fm;").
Proof.
  intros m z x Hz H. pose proof (rd_off_image m z x Hz H) as M.
  unfold wok_of, rd_of. rewrite M. split; [reflexivity | exists x; reflexivity].
Qed.

Lemma find_segment_A_off2 : ltac2:(tb__ "0|1|
S0S1Z0R1A2SdS1S2R2Z1M0A2Z10000A2S1Z643000R2A2A2SaS14S3dA1S4cS12R3G0A3S1aS3dA1A3F_;F_;Fx;").
Proof.
  intros x Hx0 [Hx|Hx]; [|apply find_segment_A_off; exact Hx].
  unfold segsA. cbn -[Z.leb Z.ltb Z.add Z.of_N].
  change (Z.of_N 65536%N) with 65536. change (Z.of_N 176128%N) with 176128.
  change (Z.of_N 241664%N) with 241664. change (Z.of_N 679936%N) with 679936.
  change (Z.of_N 921600%N) with 921600. change (Z.of_N 20480%N) with 20480.
  change (Z.of_N 942080%N) with 942080. change (Z.of_N 5623808%N) with 5623808.
  destruct (Z.leb_spec 65536 x); destruct (Z.leb_spec (x + 1) (65536 + 176128)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec 241664 x); destruct (Z.leb_spec (x + 1) (241664 + 679936)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec 921600 x); destruct (Z.leb_spec (x + 1) (921600 + 20480)); cbn [andb]; try lia.
  all: destruct (Z.leb_spec 942080 x); destruct (Z.leb_spec (x + 1) (942080 + 5623808)); cbn [andb]; try lia; reflexivity.
Qed.
Lemma image_byte_A_off2 : ltac2:(tb__ "0|1|
S0SbS1Z0R1A2S3R1S4Z2Z40A2A2A2SdS1S2R2Z1A2Z10000A2S1Z643000R2A2A2SaS14S10Q8A1M0A1S32S12SfQ40R3A2A2S1aG0A1A3F_;F_;Fx;").
Proof.
  intros x Hx Ho. unfold image_byte, memory_read. rewrite u64_lit by lia.
  change (Z.of_N 1) with 1. rewrite find_segment_A_off2 by lia. reflexivity.
Qed.
Lemma rd_off_image2 : ltac2:(tb__ "0|3|
S10Q40M0A1S14S10Q8A1M1A1M2F_;S0G1SbS1Z0R2A2S3R2S4Z2Z40A2A2A2SdS1S2R3Z1A2Z10000A2S1Z643000R3A2A2SaG2S23S12R5SfG0R4A2A3S15G1R3A2A3SaG2R6SfG0R5A2A1S15G1R4A2A3F_;F_;F_;Fx;Fz;Fm;").
Proof.
  intros m z x Hz Ho H. unfold rd_of in H. destruct (m (Z_to_bv 64 z)); [exact H|].
  rewrite image_byte_A_off2 in H by lia. discriminate.
Qed.
Lemma wok_rd_off_image2 : ltac2:(tb__ "0|3|
S10Q40M0A1S14S10Q8A1M1A1M2F_;S0G1SbS1Z0R2A2S3R2S4Z2Z40A2A2A2SdS1S2R3Z1A2Z10000A2S1Z643000R3A2A2SaG2S23S12R5SfG0R4A2A3S15G1R3A2A3SbSaS16S24S12R6SfG0R5A2A3S18A3ScG1G1SaG2S23S12R7SfG0R6A2A3S15G1R1A2A3Ly;A2A2F_;F_;F_;Fx;Fz;Fm;").
Proof.
  intros m z x Hz Ho H. pose proof (rd_off_image2 m z x Hz Ho H) as M.
  unfold wok_of, rd_of. rewrite M. split; [reflexivity | exists x; reflexivity].
Qed.

Lemma fs_footb_true2 : ltac2:(tb__ "0|1|
S3eS0SbS1S2S3fR2A1M0S50A2R1A2S3R1S2G0S4dA2A2A2SaS16S48R3R2A2S18A3F_;Fz;FG;").
Proof.
  intros G z Hz. unfold fs_footb. cbn zeta. apply orb_true_intro. left. apply orb_true_intro. right.
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma fs_footb_true3 : ltac2:(tb__ "0|1|
S3eS0SbS1S4eS2S3fR2A1M0S4fA2A1R1A2S3R1S4eS2G0S4dA2A1A2A2SaS16S48R3R2A2S18A3F_;Fz;FG;").
Proof.
  intros G z Hz. unfold fs_footb. cbn zeta. apply orb_true_intro. right.
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma fs_footb_true1 : ltac2:(tb__ "0|1|
S3eS0SbS1S3fR2A1M0R1A2S3R1S2G0Z58A2A2A2SaS16S48R3R2A2S18A3F_;Fz;FG;").
Proof.
  intros G z Hz. unfold fs_footb. cbn zeta. apply orb_true_intro. left. apply orb_true_intro. left.
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma existsb_app : forall {T} (g : T -> bool) l1 l2, existsb g (l1 ++ l2) = existsb g l1 || existsb g l2.
Proof. intros T g l1 l2. induction l1; cbn; [reflexivity|]. rewrite IHl1, orb_assoc. reflexivity. Qed.

Lemma existsb_pos_false : ltac2:(tb__ "0|1|
S19S1cS0S0A2M0A1S0SeS49S0R1S46G0S0S1bS0S0A2R2A4A3A1SaS16S4bG0G0S6S1bS0S0R1A3R3A2Lpf;R3A3S20A3F_;Fpos;Fl;").
Proof.
  induction l as [|[p g] l IH]; intros pos Hn; cbn; [reflexivity|].
  destruct (Z.eqb_spec p pos); [exfalso; apply Hn; left; cbn; lia|]. cbn. apply IH. intros Hi. apply Hn. right. exact Hi.
Qed.

Lemma fs_busy_release : ltac2:(tb__ "0|3|
S40S0S0S0S19S1cS0S0A2M0A1M1G1S1Z0M2R5A2S1G2R4A2S44S9R7A1S21G1S41R8A1A2A2SaG1S47R9R8A2S1dG0R5S1fG0S1eS0S0R7S51S3fS42R9A1A1R8R7A3A4R4A3A3A3SeS49S0R8S46G0S0S1bS0S0A2R6A4A3A1SaG1S47S43RbRaR9A3R8A2S16G1L_;S6R8RaA2S1dG0R7R6A3S47RbR8A2X16x2A3F_;F_;F_;F_;F_;Fv;Fu;Fc0;Fpos;Fc;FA;").
Proof.
  intros A c pos c0 u v Hc Hc0 Hlen E Hn. unfold fs_busy, nthZ, fs_release. cbn [aa_fs_busy].
  destruct (Z.eqb_spec c0 c).
  - subst c0. rewrite nth_list_upd_same by exact Hlen. change (nth (Z.to_nat c) (aa_fs_busy A) []) with (fs_busy A c).
    rewrite E. apply remove_pos_split. exact Hn.
  - rewrite nth_list_upd_other; [reflexivity|]. intros E'. apply n. lia.
Qed.

Lemma gsv_val : ltac2:(tb__ "0|1|
S2eS30SaS0S11Q40M0S2dR2S13R1A1A2A2S7S11G0S2dR2R1A2A2Z8A2A3Fe;Frho;").
Proof. intros. unfold gsv. cbn [eval]. rewrite srl_val. change (3 mod 64) with 3. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma nth0_enc1_zero : ltac2:(tb__ "0|4|
S2eSaS10Q8M0A1M1S45G1U0S2fU1S2dR1S31Z0M2A1A2A2SfG0G2A2M3A4G3A3Frho;").
Proof. intros. reflexivity. Qed.

Lemma rd_of_imageA : ltac2:(tb__ "0|3|
S10Q40M0A1S14S10Q8A1M1A1M2F_;S0SbS1Ze1000R1A2S3R1Z643000A2A2ScG1G1SaG2S23S12R4SfG0R3A2A3S15G1R1A2A3Lx;A2F_;Fz;Fm;").
Proof.
  intros m z Hz. unfold rd_of. destruct (m (Z_to_bv 64 z)) as [b|]; [exists b; reflexivity|].
  destruct (byte_cond_A z Hz) as [[b Hb] _]. exists b. exact Hb.
Qed.

Lemma civ_cell : ltac2:(tb__ "0|6|
S2eS10Q40M0A1M1S14S10Q8M2A1M3A1M4F_;S0S0S17S0S30S29S27S12R6A2S26S2R5R4A2R3R2A3A2SaG1S2dR8R2A2SfG0R3A2A3S1Z0M5S2R7R6A2A2S1S2S2R8R7A2S5R6A1A2S4Z2Z40A2A2S17S44R1R8A2SaG4S23S12RcSfG0S2S2RbRaA2S5R2A1A2A2A3S15G3S45G3R2S2fR9S2dRdR7A2A2SfG2G5A2A4A2A3F_;Fj;F_;F_;F_;F_;Fe;Fv;Fk;Foff;Fb;Fm;Frho;").
Proof.
  intros rho m b off k v e Hc He Hb1 Hb2 j Hj. rewrite He. specialize (Hc j Hj). cbn [c_addr c_w c_val] in Hc.
  rewrite view_in in Hc by lia. exact Hc.
Qed.

Lemma civ_nth : ltac2:(tb__ "0|6|
S2eS10Q40M0A1M1S14S10Q8M2A1M3A1M4F_;S3eS17S0S17S0S0S0S30S2bS27S12R9A2S2aS28R8A2A2SaS14S25A1S4aS25S2aS28R9A2R8A3S15S25S26R7R6R5A3A2A3SaS0R8S2R5R4A2A3SaG1S2dRdR4A2SfG0R7A2A3S1Z0M5RaA2S1S2RbS5RaA1A2S4Z2Z40A2A2S17S44R1RcA2SaG4S23S12R11SfG0S2S2RbRaA2S5R2A1A2A2A3S15G3S45G3R2S2fRdS2dR12R9A2A2SfG2G5A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;F_;Fe;Foff;Fb;Fv;Fk;Fa;Fn;FG;Fm;Frho;").
Proof.
  intros rho m G n a k v b off e HR Hn -> He Ha1 Ha2. eapply civ_cell; eauto. eapply cells_ok_nth; eauto.
Qed.

Lemma cell_wok_rd : ltac2:(tb__ "0|3|
S10Q40M0A1S14S10Q8A1M1A1M2F_;S0S17S0S0S29S27S12R5A2S26R4R3R2A3A2SbS1R5R2A2S3R2S2R5S5R4A1A2A2A2S1Z643000R6A2S1S2R7S5R6A1A2S4Z2Z40A2A2SbSaS16S24S12R9SfG0R5A2A3S18A3ScG1G1SaG2S23S12RaSfG0R6A2A3S15G1R1A2A3Ly;A2A2F_;F_;F_;F_;Fz;Fv;Fk;Fa;Fm;").
Proof.
  intros m a k v z Hc Hz Ha1 Ha2. specialize (Hc (Z.to_nat (z - a)) ltac:(cbn [c_w]; lia)). cbn [c_addr c_w c_val] in Hc.
  rewrite view_in in Hc by lia. replace (a + Z.of_nat (Z.to_nat (z - a))) with z in Hc by lia.
  eapply wok_rd_off_image; [lia | exact Hc].
Qed.

Lemma cell_wok_rd2 : ltac2:(tb__ "0|3|
S10Q40M0A1S14S10Q8A1M1A1M2F_;S0S17S0S0S29S27S12R5A2S26R4R3R2A3A2SbS1R5R2A2S3R2S2R5S5R4A1A2A2A2S1Z0R6A2SdS1S2R7S5R6A1A2Z10000A2S1Z643000R7A2A2S1S2R8S5R7A1A2S4Z2Z40A2A2SbSaS16S24S12RaSfG0R6A2A3S18A3ScG1G1SaG2S23S12RbSfG0R7A2A3S15G1R1A2A3Ly;A2A2F_;F_;F_;F_;F_;Fz;Fv;Fk;Fa;Fm;").
Proof.
  intros m a k v z Hc Hz Ha0 Ho Ha2. specialize (Hc (Z.to_nat (z - a)) ltac:(cbn [c_w]; lia)). cbn [c_addr c_w c_val] in Hc.
  rewrite view_in in Hc by lia. replace (a + Z.of_nat (Z.to_nat (z - a))) with z in Hc by lia.
  eapply wok_rd_off_image2; [lia | lia | exact Hc].
Qed.

Ltac civ_try HR E n :=
  eapply (civ_nth _ _ _ n); [exact HR | reflexivity | unfold fs_log_cell, fs_needs_gc_cell; lia | cbn [eval]; E; reflexivity | unfold fs_log_cell, fs_needs_gc_cell; lia | unfold fs_log_cell, fs_needs_gc_cell; lia].
Ltac civ_any HR E := first [ civ_try HR E 0%nat | civ_try HR E 1%nat | civ_try HR E 2%nat | civ_try HR E 3%nat | civ_try HR E 4%nat | civ_try HR E 5%nat | civ_try HR E 6%nat | civ_try HR E 7%nat | civ_try HR E 8%nat | civ_try HR E 9%nat | civ_try HR E 10%nat | civ_try HR E 11%nat | civ_try HR E 12%nat | civ_try HR E 13%nat | civ_try HR E 14%nat | civ_try HR E 15%nat | civ_try HR E 16%nat | civ_try HR E 17%nat | civ_try HR E 18%nat | civ_try HR E 19%nat | civ_try HR E 20%nat | civ_try HR E 21%nat | civ_try HR E 22%nat | civ_try HR E 23%nat | civ_try HR E 24%nat | civ_try HR E 25%nat | civ_try HR E 26%nat | civ_try HR E 27%nat | civ_try HR E 28%nat | civ_try HR E 29%nat | civ_try HR E 30%nat | civ_try HR E 31%nat | civ_try HR E 32%nat | civ_try HR E 33%nat | civ_try HR E 34%nat | civ_try HR E 35%nat | civ_try HR E 36%nat | civ_try HR E 37%nat | civ_try HR E 38%nat | civ_try HR E 39%nat | civ_try HR E 40%nat | civ_try HR E 41%nat | civ_try HR E 42%nat | civ_try HR E 43%nat | civ_try HR E 44%nat | civ_try HR E 45%nat | civ_try HR E 46%nat | civ_try HR E 47%nat | civ_try HR E 48%nat | civ_try HR E 49%nat | civ_try HR E 50%nat | civ_try HR E 51%nat | civ_try HR E 52%nat | civ_try HR E 53%nat | civ_try HR E 54%nat ].
Lemma civ_nth2 : ltac2:(tb__ "0|5|
S10Q40M0A1S14S10Q8M1A1M2A1M3F_;S3eS17S0S17S0S0S0S2bS27S12R8A2S2aS28R7A2A2SaS14S25A1S4aS25S2aS28R8A2R7A3S15S25S26R6R5R4A3A2A3SaS0R7S2R4R3A2A3S1Z0M4R8A2S1S2R9S5R8A1A2S4Z2Z40A2A2S17S44R1RaA2SaG3S23S12RfSfG0S2S2R9R8A2S5R2A1A2A2A3S15G2S45G2R2S2fRbSfG0RaA2A2SfG1G4A2A4A2A3F_;Fj;F_;F_;F_;F_;F_;Foff;Fb;Fv;Fk;Fa;Fn;FG;Fm;").
Proof.
  intros m G n a k v b off HR Hn -> Ha1 Ha2 j Hj. pose proof (cells_ok_nth _ _ n _ HR Hn j Hj) as C. cbn [c_addr c_w c_val] in C.
  rewrite view_in in C by lia. exact C.
Qed.
Ltac civ_try2 HR n :=
  eapply (civ_nth2 _ _ n); [exact HR | reflexivity | unfold fs_log_cell, fs_needs_gc_cell; lia | unfold fs_log_cell, fs_needs_gc_cell; lia | unfold fs_log_cell, fs_needs_gc_cell; lia].
Ltac civ_any2 HR := first [ civ_try2 HR 0%nat | civ_try2 HR 1%nat | civ_try2 HR 2%nat | civ_try2 HR 3%nat | civ_try2 HR 4%nat | civ_try2 HR 5%nat | civ_try2 HR 6%nat | civ_try2 HR 7%nat | civ_try2 HR 8%nat | civ_try2 HR 9%nat | civ_try2 HR 10%nat | civ_try2 HR 11%nat | civ_try2 HR 12%nat | civ_try2 HR 13%nat | civ_try2 HR 14%nat | civ_try2 HR 15%nat | civ_try2 HR 16%nat | civ_try2 HR 17%nat | civ_try2 HR 18%nat | civ_try2 HR 19%nat | civ_try2 HR 20%nat | civ_try2 HR 21%nat | civ_try2 HR 22%nat | civ_try2 HR 23%nat | civ_try2 HR 24%nat | civ_try2 HR 25%nat | civ_try2 HR 26%nat | civ_try2 HR 27%nat | civ_try2 HR 28%nat | civ_try2 HR 29%nat | civ_try2 HR 30%nat | civ_try2 HR 31%nat | civ_try2 HR 32%nat | civ_try2 HR 33%nat | civ_try2 HR 34%nat | civ_try2 HR 35%nat | civ_try2 HR 36%nat | civ_try2 HR 37%nat | civ_try2 HR 38%nat | civ_try2 HR 39%nat | civ_try2 HR 40%nat | civ_try2 HR 41%nat | civ_try2 HR 42%nat | civ_try2 HR 43%nat | civ_try2 HR 44%nat | civ_try2 HR 45%nat | civ_try2 HR 46%nat | civ_try2 HR 47%nat | civ_try2 HR 48%nat | civ_try2 HR 49%nat | civ_try2 HR 50%nat | civ_try2 HR 51%nat | civ_try2 HR 52%nat | civ_try2 HR 53%nat | civ_try2 HR 54%nat ].

Ltac wr_cell HR n :=
  eapply (cell_wok_rd _ _ _ _ _ (cells_ok_nth _ _ n _ HR eq_refl)); cbn [c_addr c_w Z.of_nat]; unfold fs_log_cell, fs_needs_gc_cell; lia.

Ltac wr_cell2 HR n tacW :=
  eapply (cell_wok_rd2 _ _ _ _ _ (cells_ok_nth _ _ n _ HR eq_refl)); cbn [c_addr c_w Z.of_nat]; unfold fs_log_cell, fs_needs_gc_cell; [lia | lia | tacW | lia].
Ltac wr_any2 HR tacW := first [ wr_cell2 HR 43%nat tacW | wr_cell2 HR 44%nat tacW | wr_cell2 HR 45%nat tacW | wr_cell2 HR 46%nat tacW | wr_cell2 HR 47%nat tacW | wr_cell2 HR 48%nat tacW | wr_cell2 HR 49%nat tacW | wr_cell2 HR 50%nat tacW | wr_cell2 HR 51%nat tacW | wr_cell2 HR 52%nat tacW | wr_cell2 HR 53%nat tacW | wr_cell2 HR 54%nat tacW ].
Ltac wr_any HR := first [ wr_cell HR 43%nat | wr_cell HR 44%nat | wr_cell HR 45%nat | wr_cell HR 46%nat | wr_cell HR 47%nat | wr_cell HR 48%nat | wr_cell HR 49%nat | wr_cell HR 50%nat | wr_cell HR 51%nat | wr_cell HR 52%nat | wr_cell HR 53%nat | wr_cell HR 54%nat ].

End GlueMA.

