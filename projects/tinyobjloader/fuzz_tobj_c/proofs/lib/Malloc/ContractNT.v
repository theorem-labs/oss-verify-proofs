(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "iff"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "ameta"; "astate"; "region"; "am_sc"; "mslot"; "META_SIZE"; "IRet"; "MFree"; "RkMap"; "am_freed"; "am_maplen"; "am_mem"; "am_next"; "am_prev"; "itree"; "nontrivial_free"; "page_round"; "prid"; "rg_kind"; "rg_len"; "rg_live"; "rkind"; "st_init_done"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT.ContractsNT"; "magree"; "in_zslots"; "zv"; "J_nt_pre"; "Posts_nt"; "Pre_nt"; "zslotb"; "JL_nt"; "L_nt"; "V_RES1"; "xzomb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "option"; "None"; "cons"; "list"; "nat"; "nil"; "pair"; "prod"; "Some"; "bool"; "false"; "true"; "app"; "andb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "ma_s"; "ma_L"; "MA"; "mkMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "rw"; "valuation"; "sobj"; "rm"; "FcsrFrm0"; "mkSS"; "sstate"; "sv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractNT"; "NT_D"; "NTE_P"; "NTE_U"; "nt_sumI"; "nt_sumI_ex"; "ne_entry"; "ne_ret"; "nt_stack"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "pre_fregs"; "segsP"; "segsU"; "cut_regs"; "pre_regs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "rd_of"; "wok_of"; "F_depth"; "F_sp_aligned"; "F_sp_high"; "stack_win"; "NPOSTM"; "V_DEPTH"; "V_RES"; "mem_kept_owned"; "ok_sideK"; "top_high"; "vm_insensitive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "addr_of"; "C_P"; "C_U"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "MT"; "usedX"; "Inv"; "active_hd"; "layout"; "ly_reg"; "region_of"; "@Stdlib.Lists.List"; "In"; "existsb"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "leb"; "ltb"; "mul"; "of_nat"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "LQP"; "jpost"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIfaceI"; "MInvI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.NestTier"; "reach_ok"; "tier"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ContractI"; "canary_kept"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFrame"; "ub_same"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocWfFree"; "corr"; "fneed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.ZEval"; "toS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zomb"; "zomb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Zones2"; "xraw"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymFrame SymSummary SymCall SymComplete ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocFooter MallocIface MallocIfaceI MallocWfFrame MallocWfFree NestTier Contract ContractI ZEval Zones2 Zomb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Record ntentry_consts := NTE { ne_entry : Z; ne_ret : Z }.
Definition NTE_P : ntentry_consts := NTE 0x2010c 0x204dc.
Definition NTE_U : ntentry_consts := NTE (0x2010c + 0x740) (0x204dc + 0x740).

Definition NT_D : Z := 96.
Definition nt_stack (t : nat) : Z := ltac2:(tb__ "0|0|
S76S47S71S77Vt;A1Z1A2A2").

Section ContractsNT.
Variable segs : list Segment.
Variable C : mconsts.
Variable E : ntentry_consts.

Definition V_RES1 : positive := 111%positive.

Definition Pre_nt : sstate := ltac2:(tb__ "0|0|
S44S4cVE;A1S57S53S43S2dS46A1S2eS41S5dS47A1S31S41A1A3S38S3eS2eS3eS5bS2eS3eS5cS47A1S31S3eA1A3A3S5aS47A1A3S52S36A9").

Definition L_nt : sstate := ltac2:(tb__ "0|0|
S44S4dVE;A1S56S52A1S53S43S2dS46A1S2eS41S5dS47A1S31S41A1A3S38S3eS2eS3eS5bS2eS3eS5cS47A1S31S3eA1A3A3S5aS47A1A3S5eS36A9").

Definition in_zslots (L : layout) (X : list sptr) (a : Z) : Prop := ltac2:(tb__ "0|1|
S2S6S6S0S6fS6R1VX;A3S0S72S65VL;R1A2M0Va;A2S73Va;S71G0ScA2A2A2A2Lx;A2").
Definition magree (L : layout) (X : list sptr) (mv mr : word -> option byte) : Prop := ltac2:(tb__ "0|5|
S0S2aQ40M0A1M1S3S20VL;VX;S2bG0R1A2A3A1S1S2cS2aQ8A1M2A1M3Vmv;R2A1Vmr;R2A1A3F_;Fa;G1S4S1G3Vmv;R1A1S2dG2A1M4A3S1G3Vmr;R1A1G4A3A2Fa;A2").
Definition xzomb (X : list sptr) (s : astate) : Prop := ltac2:(tb__ "0|1|
S6S6fS6R1VX;A3S1S2cSbA1S68Vs;R2A2S34SbSeS2dS6A1M0G0A2A2A3F_;Fx;").

Definition zv (X : list sptr) (A : MA) : MA := ltac2:(tb__ "0|0|
S3dS88VX;S3aVA;A1A2S3bVA;A1A2").

Definition zslotb (L : layout) (X : list sptr) (a : Z) : bool := ltac2:(tb__ "0|1|
S70S6S6S39S74S65VL;R1A2M0Va;A2S75Va;S71G0ScA2A2A2Lx;VX;A3").
Lemma zslotb_spec L X a : ltac2:(tb__ "0|0|
S4S1S35S25VL;VX;Va;A3S37A3S20VL;VX;Va;A3A2").
Proof using .
  unfold zslotb, in_zslots. rewrite existsb_exists. split.
  - intros (x & Hx & B). apply andb_prop in B as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2. exists x. auto.
  - intros (x & Hx & R). exists x. split; [exact Hx|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma zslotb_false L X a : ltac2:(tb__ "0|0|
S4S1S35S25VL;VX;Va;A3S36A3S3S20VL;VX;Va;A3A1A2").
Proof using . rewrite <- zslotb_spec. destruct (zslotb L X a); split; congruence. Qed.

Lemma xzomb_xraw X s : ltac2:(tb__ "0|0|
S29VX;Vs;A2S89VX;Vs;A2F_;").
Proof using . intros H x Hx. right. exact (H x Hx). Qed.
Lemma magree_refl L X m : ltac2:(tb__ "0|0|
S1fVL;VX;Vm;Vm;A4").
Proof using . split; [intros; reflexivity | intros; tauto]. Qed.
Lemma magree_sym L X m1 m2 : ltac2:(tb__ "0|0|
S1fVL;VX;Vm1;Vm2;A4S1fVL;VX;Vm2;Vm1;A4F_;").
Proof using . intros [A B]. split; [intros a Ha; symmetry; exact (A a Ha) | intros a; symmetry; exact (B a)]. Qed.
Lemma magree_trans L X m1 m2 m3 : ltac2:(tb__ "0|0|
S1fVL;VX;Vm1;Vm2;A4S1fVL;VX;Vm2;Vm3;A4S1fVL;VX;Vm1;Vm3;A4F_;F_;").
Proof using . intros [A B] [A' B']. split; [intros a Ha; rewrite (A a Ha); exact (A' a Ha) | intros a; rewrite (B a); exact (B' a)]. Qed.
Lemma magree_nil L mv mr : ltac2:(tb__ "0|0|
S1fVL;S31S6A1Vmv;Vmr;A4S2aQ40A1S1S2cS2aQ8A1A1Vmv;R1A1Vmr;R1A1A3Fa;F_;").
Proof using . intros [A _] a. apply A. intros (x & [] & _). Qed.
Lemma magree_wok L X mv mr : ltac2:(tb__ "0|0|
S1fVL;VX;Vmv;Vmr;A4S2aQ40A1S1S35S59Vsegs;Vmv;R1A3S59Vsegs;Vmr;R1A3A3Fa;F_;").
Proof using . intros [_ B] a. unfold wok_of. destruct (mv a) eqn:E1, (mr a) eqn:E2; try reflexivity; [pose proof (proj2 (B a) E2) | pose proof (proj1 (B a) E1)]; congruence. Qed.
Lemma magree_rd L X mv mr : ltac2:(tb__ "0|1|
S1fVL;VX;Vmv;Vmr;A4S2aQ40M0A1S3S20VL;VX;S2bG0R1A2A3A1S1S2cS2aQ8A1A1S58Vsegs;Vmv;R2A3S58Vsegs;Vmr;R2A3A3F_;Fa;F_;").
Proof using . intros [A _] a Ha. unfold rd_of. rewrite (A a Ha). reflexivity. Qed.

Definition J_nt_pre (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) : jpred := ltac2:(tb__ "0|9|
S40S2fS50A1S4fS2bQ40M0S3fR3PcA2A2S1eS2bG0S3fR4PdA2A2S1eS2S6S6S2S7S7S2S2aG0A1S2cS2aQ8A1A1F_;M1G1S0S1S1eS65S3bVA;A1M2R3A2R5A3S0S7cVC;VX;S34S33S6S1eA2S32S6S1eR3R4A4A2M3VU;S21VX;VA;A2M4S58Vsegs;R1A2S59Vsegs;R1A2S51R6A1A8S0S1fG2VX;R1S42R8A1A4S0S6aVX;G3VU;S3aVA;A1M5A4S0S69VX;G5R3R2A4S0S1eS72Z0M6VU;R1A1A2Fc;S0S3S1S33S2cS6A1M7G7A2S32G7G7S14R2A1S13R2A1A4S32G7G7S2dS6A1M8G8A4A3A1S3S1G7S6bG5SaR3A1A2S34S6R4A2A3A1S3S1S1eS10R4A1G6A3A1F_;F_;S0S72S87Z40S2bG0S3fR8S5fA2A2A2S78S4eS7eSaR2A1A1A1A1A2S0S7dS3aG4A1A1S0VKc;R7R6A2S63VA;R8A2A2A2A2A2A2A2A2A2A2A2Lmv;A2Lam;A2Lg;A2Ti;Tga;Lmd;Ltr;Lrho;").

Definition JL_nt (X : list sptr) (U : Z -> Z) (A : MA) (Kc : list event -> Model -> Prop) : jpost := ltac2:(tb__ "0|f|
S40S40S2fS50A1S4fS2bQ40M0S3fR3S60A2A2S1eS2bG0S3fR4S28A2A2S1eS2S3cS3cS2S2aG0A1S2cS2aQ8A1A1F_;M1G1S2S2cS33S30S1eA2M2A1M3G3S0S7cVC;VX;S2dS33S6S1eA2A1M4VU;S21VX;R3A2M5S58Vsegs;R2A2S59Vsegs;R2A2S51R6A1A8S0S1fS3bVA;A1M6VX;R2S42R8A1M7A4S0S1S6cS3bR3A1G6A3S0S1S35S1dS3aR3A1M8A1S37A3S0S6aVX;G4VU;G8A4S0S6S6fS6R1VX;A3S1S2cSbA1S68S3aR5A1M9R2A2S68S3aVA;A1MaR2A2A3F_;Fx;S0S85VX;GaG8A3S0S84GaG8A2S0S7dS3aG5A1A1S0S5S0S1G3R1S2dG2A1A3S0S1S1eR4Z0MbA3S1S1eR5GbA3A2A2S2S30S30S2S9S9S0S1G3R3S34G2S32S30S1eR2S1aR1A1McA4A2A3S0S73GbR6A2S0S1S2cS9A1S6eG9R2A2S34S9R1A2A3S0S1S1cS19R1A1SfA3S0S1S35S1bR1A1S37A3S0S1S1eGcS17R6A1A3S0S1S1eS6dS3bR5A1R2A2R7A3S6S7S69VX;S3aR7A1R2R1A4S73GbS11R2A1A2S3S1S30S18S12R3A1A1R6A3A1F_;F_;Fa;Fq;A2A2A2A2A2A2A2Lrg;A2Lk;A2A2S0S6S7S30S1S1eS65G6R3A2S2bG0S3fRcPcA2A2A3S69VX;GaR4R3A4S7fS86SaR4A1A1R3A2S1S15S8S33G3S8A2MdA2S16R4R6S2bG0S3fRfPdA2A2GaA4SdS8GdS32G3S8R7S3aR9A1A4A3A3F_;F_;F_;FF;Fam;Fg;S0S61VC;S21VX;VA;A2G5S42R9A1MeG7A5S0S83Vsegs;VC;GeG7A4VKc;R7R6A2A2A2A2A2A2A2A2A2A2A2A2A2A2Lr;A2Lmv';A2LA';A2Tlen;Tbase;Lmd;Ltr;Lrho';Lrho0;").

Definition Posts_nt X U A Kc : list (sstate * jpost) := ltac2:(tb__ "0|1|
S2eS33S45S7bA2M0S32S45S7bS27S26VX;VU;VA;VKc;A4A4S31G0A1A3").

Definition nt_sumI : Prop := ltac2:(tb__ "0|0|
S82OF_;S2fS6A1S1eS1eF_;S3cS2fS50A1S4fOF_;F_;S40S62Vsegs;R6R2A3S81Vsegs;R7S79Vsegs;S22R6R5R4R3A4S24R2A4S7aVsegs;S52R2S23R6R5R4R3A4A4A4F_;Frho;FKc;FA;FU;FX;Fok;").

Definition nt_sumI_ex : Prop := ltac2:(tb__ "0|0|
S2fS6A1S1eS1eF_;S3cS2fS50A1S4fOF_;F_;S40S64R2A1S80Vsegs;S79Vsegs;S22R6R5R4R3A4S24R2A4S7aVsegs;S52R2S23R6R5R4R3A4A4A3F_;Frho;FKc;FA;FU;FX;").

End ContractsNT.

Definition nt_sumI_P : Prop := ltac2:(tb__ "0|0|
S4aS54S66S48A3").
Definition nt_sumI_U : Prop := ltac2:(tb__ "0|0|
S4aS55S67S49A3").
Definition nt_sumI_ex_P : Prop := ltac2:(tb__ "0|0|
S4bS54S66S48A3").
Definition nt_sumI_ex_U : Prop := ltac2:(tb__ "0|0|
S4bS55S67S49A3").
