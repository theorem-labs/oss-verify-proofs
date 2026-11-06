(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg Lib_opt_push1 ec Lib_opt_push3.

(* [comment removed for export] *)
Module Lib_vec_finalizeZ.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "prod"; "list"; "cons"; "nil"; "bool"; "true"; "Some"; "fst"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "JA_pre"; "emeasA"; "JA"; "JLA"; "NDA"; "ejcertA"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "ss_facts"; "holds"; "ss_next"; "SLit"; "SPBranch"; "SPNot"; "sobj"; "sprop_below"; "sprop_eqb"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ei.Lib_vec_finalizeZ"; "nd0z"; "CHz"; "cutsVz"; "exitsVz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_vec_finalize_pf"; "P0_vf"; "PD_adv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@Stdlib.Lists.List"; "In"; "existsb"; "forallb"; "@Corelib.Init.Logic"; "and"; "eq"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_finalize"; "z0"; "X_go"; "C_go"; "P_fail"; "P_ok"; "P_zero"; "Pre_vf"; "nd0"; "nd_fail"; "nd_ok"; "E_call"; "go_facts"; "vC"; "CHv"; "FUEL_vf"; "am_vf"; "cutpcs_vf"; "eC"; "tv_vf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "batom"; "bitem"; "ASv"; "BI"; "BXok_d"; "bxt"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "mul"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ei.Lib_vec_finalizeZ.Sum"; "Posts_vfZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ef.Lib_arena_dup_pf"; "P0_ad"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup"; "Pre_ad"; "nd0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "PostsC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "payA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ed.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ef.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_finalize.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ef.Lib_arena_dup_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_finalize OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_vec_finalize_pf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import VFAddr ADAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition CHz : list bitem := ltac2:(tb__ "0|6|
S3S55S57Z1M0Z0M1S3S1SdS54A2M2S0SdS54Z2S56S52A1M3A4S3G2S0SdS54Z60S56S4dA1M4A4S4G2A1M5A3A3G1A4S3S55S57G1G0S3G2S0SdS54Z4G3A4S3G2S0SdS54Z40G4A4G5A3A3G1A4S4S55A1A3A3").
Definition nd0z : ndesc := ltac2:(tb__ "0|0|
S15S53S4S1S1S19SdA2S19A2A1S2fS50A4").

Definition cutsVz : list edescA := ltac2:(tb__ "0|3|
S3S1S1SaSfA2M0S1SdS19A2M1A2M2S0G0G1S0SaSfS47S2eA4S0SdS19Z64S41A4A4S3G2S0G0G1S0SaSfS43S48A4S0SdS19Z50S41A4A4S4G2A1A3A3").
Definition exitsVz : list edescA := ltac2:(tb__ "0|4|
S3S1S1SaSfA2M0S1SdS19A2M1A2M2S0G0G1S0SaSfS42S2eA4S0SdS19Z5aS41A4A4S3G2S0G0G1S0SaSfS4bS48A4S0SdS19Z46S41A4A4S3G2S0G0G1S0SaSfS46S2eA4S0SdS19Z0S41A4M3A4S3G2S0G0G1S0SaSfS44S49A4G3A4S3G2S0G0G1S0SaSfS45S4aA4G3A4S4G2A1A3A3A3A3A3").
Lemma ejcertVz_ok : ltac2:(tb__ "0|0|
S3eS5S16SeS32S4fS51P64S30S31A7S6A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma go_checks : ltac2:(tb__ "0|0|
S3dS3eS5S3bS1bS24S21S20S6eS4dS1fZ0A1A3A1A1S1cSbS43A1A1A3S6A3S3eS5S3cS1bS23S1eSbS42A1A1A1S4cA3S6A3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S78S1aS2S25Q40A1A1S3fOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S6cSeVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
SdS6dVCST;R1A2S3dS5aZ0R2A2S5bR2S68A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
SdS6dVXGL;R1A2S3dS5aZ0R2A2S5bR2S68A2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S1S1SdSdA2SdA2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 4 BX.
Variable rho0 : valuation.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.

Let JL (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S14VAInv;VCST;VXGL;VKc;S33VCST;VFB;VFF;A3VFB;VFF;VBX;S10Vnd;Aa").
Definition Posts_vfZ : list (axst * jpostA) := ltac2:(tb__ "0|1|
S3S1SaS29A2M0S0SaS29S46VJL;S2eA1A4S3G0S0SaS29S44VJL;S49A1A4S3G0S0SaS29S45VJL;S4aA1A4S4G0A1A3A3A3").
Definition PD_vfZ : list (axst * ndesc) := ltac2:(tb__ "0|1|
S3S1SaSfA2M0S0SaSfS46S2eA4S3G0S0SaSfS44S49A4S3G0S0SaSfS45S4aA4S4G0A1A3A3A3").

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S13VAInv;VCST;VXGL;S32VKc;Vrho0;S33VCST;VFB;VFF;A3VFB;VFF;VBX;S10Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S1SaSfA2S73Fn;") := ltac2:(tb__ "0|0|
S17VAInv;VCST;VXGL;S32VKc;Vrho0;S33VCST;VFB;VFF;A3VFB;VFF;VBX;S10Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
S2aSeS32Vrho0;Vtp0;S5eA5").

Lemma pay_go : ltac2:(tb__ "0|1|
S77S32Vrho0;S33VCST;VFB;VFF;A3S1cSbS43A1A1S1fZ0M0A1G0S2fS4eA8").
Proof.
  split; [reflexivity|]. split; [lia|].
  intros r HF _ _ HNN. unfold pay_sem. rewrite uval_lit by lia.
  pose proof (holds_mem _ _ _ HF (proj1 go_checks)) as F0. apply (proj1 (holds_nbeq _ _ _)) in F0.
  change (bv_unsigned (eval r vC)) with (uval r vC) in F0. change (bv_unsigned (eval r (SLit 0))) with (uval r (SLit 0)) in F0. rewrite uval_lit in F0 by lia.
  pose proof (uval_range r vC) as RC. pose proof (uval_range r eC) as RE.
  unfold CHz, CHv, bd_nn. cbn -[uval Z.mul Z.add Z.sub]. unfold bival. cbn -[uval Z.mul Z.add Z.sub].
  split; [lia|]. split; [lia|]. repeat (apply Forall_cons; [unfold bival; cbn -[uval Z.mul Z.add Z.sub]; lia|]). constructor.
Qed.

Lemma go_holdsZ : ltac2:(tb__ "0|0|
S1aS2S25Q40A1A1S2S40A1S3fVJAv;S2eR4R3R2R1A5S62S1bS1dR5A1S1cSbS42A1A1A3S62S1bS1dR6A1S4cA3F_;F_;Fmd;Ftr;Ftp;Frho;").
Proof.
  intros rho tp tr md (Ai & kc & HJ) HF.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & _ & _ & _ & HP0 & _).
  fact HF (SPBranch BC_EQ (SMd M_MULHU vC vE) (SLit 0)) F1. fact HF (SPNot (SPBranch BC_EQ vC (SLit 0))) F2.
  fact HF (SPUle (SLit 1) vE) F3. fact HF (SPUle eC vL) F4.
  apply (proj1 (holds_beq _ _ _)) in F1. apply (proj1 (holds_nbeq _ _ _)) in F2. rewrite h_ule in F3, F4.
  rewrite U_mulhu in F1. change (bv_unsigned (eval rho (SLit 0))) with (uval rho (SLit 0)) in F1, F2.
  change (bv_unsigned (eval rho vC)) with (uval rho vC) in F1, F2. change (bv_unsigned (eval rho vE)) with (uval rho vE) in F1.
  rewrite uval_lit in F1 by lia. rewrite uval_lit in F2 by lia. rewrite uval_lit in F3 by lia.
  pose proof (uval_range rho vC) as RC. pose proof (uval_range rho vE) as RE. pose proof (uval_range rho vL) as RL. pose proof (uval_range rho vD) as RD.
  rewrite Z.shiftr_div_pow2 in F1 by lia. unfold M64v in F1.
  assert (HP : uval rho vC * uval rho vE < 2 ^ 64).
  { destruct (Z_lt_dec (uval rho vC * uval rho vE) (2 ^ 64)) as [L|L]; [exact L|]. exfalso.
    assert (1 <= uval rho vC * uval rho vE / 2 ^ 64) by (apply Z.div_le_lower_bound; lia).
    assert (uval rho vC * uval rho vE / 2 ^ 64 < 2 ^ 64) by (apply Z.div_lt_upper_bound; [lia|]; nia).
    rewrite Z.mod_small in F1 by lia. lia. }
  assert (EC : uval rho eC = uval rho vE * uval rho vC).
  { unfold eC, uval. rewrite U_mul. unfold M64v. change (bv_unsigned (eval rho vE)) with (uval rho vE). change (bv_unsigned (eval rho vC)) with (uval rho vC).
    rewrite Z.mod_small by nia. reflexivity. }
  assert (G1 : 1 <= uval rho eC) by (rewrite EC; nia).
  unfold go_facts. constructor; [|constructor; [|constructor]]; rewrite h_ule; rewrite uval_lit by lia; [|exact G1].
  destruct (P0_now CST FB FF rho0 rho Hav HP0) as [_ [HL|[(b & n & Hin & H1 & H2)|(f & s & fl & Hin & H1 & H2)]]]; [exfalso; lia| |].
  - destruct (law_blocks _ _ _ ALA Ai rho tp md HM) as (_ & HBl & _). destruct (HBl b n (HB _ Hin)) as (_ & _ & B3 & _). lia.
  - destruct (law_blocks _ _ _ ALA Ai rho tp md HM) as (_ & _ & HFr). destruct (HFr f s (proj1 (HFF _ _ _ Hin))) as (_ & _ & _ & F4' & _).
    unfold IMG_HI in F4'. lia.
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
SdS2S25Q40A1A1S35F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S27SaS1aS2S25Q40A1A1S35S62S1bS1dR3A1S1cSbR4A1A1A3VTR;S26SeR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S35S35S35S38R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S27S27SaSaS61S2S22A1M0S2S1SaS29A2M1A1S2S1S19S19A2M2A1S35S1aS2S25Q40A1A1M3G2S3aG2R1R5A3S3aG2R2ScRbA1A3F_;Fr;S3eS9G0A1S2dRaR9R8A3S7G0R7A2A3S3eS5S2cRbRaR9R8S63G1SaS8SaS29A2R7A4A5S6A3S1aG3VTR;S26SeRfRdR2R1A5S2aSeS1eSbRdA1A1R2R1RaA5A2Ftp1;Frho1;S2S40A1M4S64S3fS28SeR9R8R10S0G4S65R3S66R2R1A2A4A5R13RaR9R4R2A4R13S60S5fRbRfS39R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;SaS29G4S64S3fS1aG3G4S64S3fS3aG1S0SaS29RaR9A4R14A3S28SeR12R11R19S0G4S65R9S66R8R7A2A4A5R1cR13R12RaR8A4S71S1eSbR1aA1A1S60S5fR14R18S39R9R13RaA3A3R19A2R8A3S28SeR9R8ReS0G4S65R7S66R6R5A2A4A5ReS60S5fR16R1aS39RbR15RcA3A3R1bA2R15RaR9R8R6A6S3dS74R17S39RcR16RdA3R1bR1cR1dR10R1eR19RbA9S1aS72R18S39RdR17ReA3R1cR1dSbR1eA1SbR1fA1SbR11A1R1RcA9VTR;S26SeS2bR11S60S5fR19R1dS39ReR18RfA3A3R1eA2R18RdRcA5S75R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S26SeR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CAD : ltac2:(tb__ "0|1|
S2S1SdSdA2M0A1S2S1G0SdA2A1S59S1aS2S25Q40A1A1S58Z3R3A2VTR;S26SeS11VAInv;VCST;VXGL;VKc;S67VCST;R6R5A3R6R5R4S10S70AaS6fR3R2A5S2aSeS32R3R2S76VAInv;VCST;VXGL;VKc;S67VCST;A1S10S34R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
SaSfS1SdS19A2M0S1aS2S25Q40A1A1M1SdG1S3aS1S1SaSfA2M2G0A2S0G2G0S0SaSfR7R6A4R5A4S30A3S3dS5aZ0S12S0G2G0S0SaSfR8R7A4R6A4R5A2M3A2S5bG3R3A2A2VTR;S26SeVJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
SaSfS1aS2S25Q40A1A1M0SdG0S3aS1SaS29A2S0SaS29R6VJL;R5A1A4S5eA3VTR;S26SeVJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac meas := unfold emeasA; cbn [eda_rank eda_var fst snd z0 eval]; rewrite lit_unsigned; cbn; lia.
Ltac vmr := vm_compute; reflexivity.
Tactic Notation "innth" integer(n) := cbn [In cutsVz exitsVz Posts_vfZ PD_vfZ PD_adv]; do n right; left; reflexivity.

Lemma X_X_goZ : ltac2:(tb__ "0|1|
S1aS2S25Q40A1A1M0SdG0S5aS5cZ5aS5dZ2Z40A2A2R2A2VTR;S26SeVJAv;S2eA1S42R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre; [|apply (REENTER C_go nd0 (80, z0)); [innth 1 | meas]].
  intros w Hw. unfold nd0.
  apply (JA_repay segs AInv CST XGL NF Kc rho0 (P0_vf CST FB FF) FB FF BX PTrue tv_vf [] CHz CHv am_vf C_go rho tp w pay_go).
  rewrite <- C_go_eq. apply (SPA_refacts_JA segs); [exact Hw | exact (proj2 go_checks) |].
  intros tr md HJ HF. apply Forall_app. split; [exact (go_holdsZ rho tp tr md HJ HF) | exact HF].
Qed.

Lemma X_E_callZ : ltac2:(tb__ "0|1|
S1aS2S25Q40A1A1M0SdG0S5aS5cZ46S5dZ2Z40A2A2R2A2VTR;S26SeVJAv;S48A1S4bR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF. unfold nd0. change tv_vf with ([] ++ tv_vf).
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_vf CST FB FF) FB FF BX PTrue HKc HBX (P0_ad CST) PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_ad OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup.nd0 PD_adv NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CAD eq_refl
           E_call s_call R_call Xk_call rho tp [] tv_vf [] CHv [] am_vf (FAM b tp0)).
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - apply payA_of_bud_pay. vmr.
  - vmr.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR HM HT HTK. exact (HIN_call CST XGL FB FF rho0 rho ms HF' HP0 Hav).
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_adv In] in Hd. destruct Hd as [Hd|[Hd|[]]]; injection Hd as <- <-;
      cbn [fst snd nd_tv nd_bd nd_am ndF ndK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ed.Lib_arena_dup.nd0 ND am_subst app].
    + rewrite P_fail_eq, imp_fail_tv, imp_fail_am. change (bd_subst _ []) with (@nil bitem). cbn [app]. apply POST. innth 1.
    + rewrite P_ok_eq, imp_ok_tv, imp_ok_am. change (bd_subst _ []) with (@nil bitem). cbn [app]. apply POST. innth 2.
Qed.

Lemma exits_okTz : ltac2:(tb__ "0|3|
SaSfS1SdS19A2M0S1aS2S25Q40A1A1M1G1S3aS1S1SaSfA2M2G0A2S0G2G0S0SaSfR6R5A4R4A4S31A3VTR;S26SeVJAv;R6A1R7R4R3A5VFAM;S12S0G2G0S0SaSfR7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsVz] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[]]]]]]; injection H as <- <- <-.
  - apply X_X_goZ. meas.
  - apply X_E_callZ. meas.
  - apply POST. innth 0.
  - apply POST. innth 1.
  - apply POST. innth 2.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S18SeVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
S6aSeS69VAInv;VCST;VXGL;A5").

Theorem vec_finalizeZ_sum : ltac2:(tb__ "0|0|
S2S25Q40A1A1S37SeVok;S26SeS11VAInv;VCST;VXGL;VKc;S33VCST;VFB;VFF;A3VFB;VFF;VBX;S10S2eAaS47Vrho0;R1A5S2aSeS32Vrho0;R1S5eA5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_vf CST FB FF) FB FF BX PTrue HKc ALA FUEL_vf cutpcs_vf 100
                (map edropA cutsVz) (map edropA exitsVz) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertVz_ok))
         with (ndT := nd0z); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okTz (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsVz)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (arena_dup_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ok Hok AC tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_vf CST FB FF) FB FF BX PTrue ok (map edropA cutsVz) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_vf CST FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_vfZ P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
S6bSeS69VAInv;VCST;VXGL;A5").

Theorem vec_finalizeZ_sum_ex : ltac2:(tb__ "0|0|
S2S25Q40A1A1S36SeS26SeS11VAInv;VCST;VXGL;VKc;S33VCST;VFB;VFF;A3VFB;VFF;VBX;S10S2eAaS47Vrho0;R1A5S2aSeS32Vrho0;R1S5eA5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_vf CST FB FF) FB FF BX PTrue HKc ALA FUEL_vf cutpcs_vf 100 cutsVz exitsVz (Q tp0) ejcertVz_ok)
         with (ndT := nd0z) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okTz (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_vf CST FB FF) FB FF BX PTrue) cutsVz) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HB0. apply (arena_dup_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HB0 rho1 ACX tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_vf CST FB FF) FB FF BX PTrue cutsVz T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_vf CST FB FF) FB FF BX PTrue rho0 tp0 nd Posts_vfZ P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_vec_finalizeZ.

(* [comment removed for export] *)
Module Lib_handle_mtllib_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "true"; "pair"; "nat"; "cons"; "fst"; "nil"; "option"; "None"; "Some"; "snd"; "andb"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "sobj"; "ss_facts"; "ss_next"; "SLit"; "holds"; "ss_objs"; "obj_range"; "sv_eqb"; "SPEq"; "SPUle"; "SVar"; "swf"; "agree_below"; "ob_base"; "ob_hi"; "ob_lo"; "rw"; "sprop_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "leafA"; "g8"; "has_facts"; "la_state"; "ax_base"; "ax_setS"; "@Corelib.Init.Logic"; "eq"; "and"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "PTrue"; "TPA"; "frinA"; "tvinA"; "emeasA"; "nd_below"; "JA_pre"; "fbinA"; "ffinA"; "JA"; "JLA"; "frozen"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs"; "NPH"; "hG"; "xCFG"; "hF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ei.Lib_handle_mtllib_pf"; "P0_ml"; "bF"; "extraOM"; "extraXM"; "P0_ml_b"; "cfgb"; "fF"; "@Stdlib.ZArith.BinInt.Z"; "le"; "pow"; "lt"; "mul"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "entails_frA"; "J_ofPA"; "call_checkA"; "call_checkPA"; "import_postA"; "@Stdlib.Lists.List"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_handle_mtllib"; "ndP"; "nd0"; "cutsM"; "z0"; "Pre_ml"; "epi_state"; "fr_ml"; "E_da0"; "E_sm0"; "L_sm"; "P_fail"; "P_ok"; "Pre_sm"; "X_pro"; "X_rl"; "exitsM"; "sel_rel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_handle_mtllib.HMLAddr"; "DW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ei.Lib_handle_mtllib_pf.Sum"; "Posts_mlJ"; "JLm"; "HNPH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T_ok"; "tvd"; "tvz"; "remove_nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "FFx"; "pclMA"; "xr_eqb"; "xrs_okL"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf"; "basez"; "P0_builder"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS"; "robjs_checkF"; "xrs_checkL"; "release_objs_ok"; "shadow_reopen_stateA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI";
"SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf"; "extraOH"; "extraOH_client"; "extraXH"; "frozen_stableH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXSelect"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "ccount"; "is_shadowZ"; "robjs_okA"; "xrs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "JL_stack_malloc"; "J_stack_malloc_pre"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "robjs_okF"; "xrs_ok47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT"; "robjs_checkP"; "@Stdlib.PArith.BinPos.Pos"; "le"; "leb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR TobjJAS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAT.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAT.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e7.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e7.Lib_diag_append.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eg.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eh.Lib_builder_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_builderH_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_builderH_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eg.Lib_handle_mtllib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require eb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Import ScanDoubleAddr VRAddr RA.ReallocAddr DiagAppendAddr HMLAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Definition P0_ml (CST : list (Z * Z)) (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S30S97VCST;VFB;VFF;Vr;A4S30Sa7VFF;S34Q40S24Vr;P6dA2A2Z90A3S2fS7Sa8Z1S80S3S3S0S0A2M0S0A2G0S9G0S0A2VFF;A4A2U0A3A2A2").
Lemma P0_ml_b : ltac2:(tb__ "0|2|
S2S3S0S0A2M0A1M1G1S2S3G0S0A2A1S12S4cR4R3R2R1A4S97R5R4R3R2A4F_;Fr;FFF;FFB;FCST;").
Proof. intros CST FB FF r [H _]. exact H. Qed.

Definition bF (F : list sprop) : bool := baseF DW F.
Definition fF (F : list sprop) : bool := frameF hG 160 128 F.
Lemma DW_rng : 0 <= DW < 2 ^ 40. Proof. unfold DW. lia. Qed.
Lemma sz_rng : 0 <= 128 < 2 ^ 40. Proof. lia. Qed.

Definition cfgb (o : sobj) : bool := ltac2:(tb__ "0|0|
SfSfS1bS21Vo;A1S46A2S1bS23Vo;A1S17Z0A1A2A2S1bS22Vo;A1S17Z90A1A2A2").
Definition extraOM (o : sobj) : bool := ltac2:(tb__ "0|0|
S10Sa0Vo;A1S51Vo;A1A2").
Definition extraXM (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S10Sa2Vr;A1S91Vr;S6S11S11S46S17Z90A1A4A2A2").

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
S7cS12S2S33Q40A1A1S64OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
Sb1S32VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S9fVCST;R1A2S30S53Z0R2A2S55R2S9dA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S9fVXGL;R1A2S30S53Z0R2A2S55R2S9dA2A2F_;Fa;").
Hypothesis LFLAG : law_flag_stmt AInv.
Hypothesis LFSH : law_fshadow_stmt AInv.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S2S3S3S0S0A2S0A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 5 BX.
Let HNP : NP_okA NF := NP_okA_intro NF eq_refl.
Variable rho0 : valuation.
Let HTOP : InitState.segs_top segs <= IMG_HI := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok.
Lemma HNPH : (NF <= NPH)%positive. Proof. unfold NF, NPH. lia. Qed.

Definition JLm (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S40VAInv;VCST;VXGL;VKc;S4cVCST;VFB;VFF;A3VFB;VFF;VBX;S36Vnd;Aa").
Definition Posts_mlJ : list (axst * jpostA) := ltac2:(tb__ "0|2|
S8S3S26S59A2M0S6S26S59S70S85S67A1M1A4S8G0S6S26S59S71G1A4SaG0A1A3A3").
Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S3fVAInv;VCST;VXGL;S44VKc;Vrho0;S4cVCST;VFB;VFF;A3VFB;VFF;VBX;S36Vnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S3S26S35A2Sb4Fn;") := ltac2:(tb__ "0|0|
S42VAInv;VCST;VXGL;S44VKc;Vrho0;S4cVCST;VFB;VFF;A3VFB;VFF;VBX;S36Ab").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
S5aS32S44Vrho0;Vtp0;S84A5").
Let frozen_stable : ltac2:(tb__ "0|0|
S1S1S35S12SbbS44R3A2S2fS4S3bR4R3A2S5A3S4bS32R6S41VAInv;VCST;VXGL;S44VKc;Vrho0;S4cVCST;VFB;VFF;A3VFB;VFF;VBX;S36R4R3AdA3F_;F_;Frho;Fnd;Fm;Fn;") := ltac2:(tb__ "0|0|
Sa3VAInv;VCST;VXGL;VALA;S44VKc;VHKc;VFB;VFF;VBX;Vrho0;S4cVCST;VFB;VFF;A3Ac").
Let extra_client : ltac2:(tb__ "0|1|
S12S14S0S2S3S11S11A2A1S2S3S3S11S0A2S11A2A1S96S83R5A2S62S44Vrho0;R6A3S4cVCST;VFB;VFF;Vrho0;A4S2fS4Sa0R7A1S5A3S30S53S9S0S0S1aR9R8A2M0A3R7A2S55R7SeS0S0G0A3A2A2S90VCST;Vrho0;S8aVFB;RaR7A3S8fVFF;RaR6A3R8A5F_;F_;F_;F_;F_;Ffrs;Fkept;Fa;Fo;Frho;") := ltac2:(tb__ "0|0|
Sa1VCST;S44S86VFB;VFF;Vrho0;S4cVCST;VFB;VFF;A3S50VCST;VFB;VFF;A3S83A9").

Lemma P0_now : ltac2:(tb__ "0|1|
S12S62S44Vrho0;R1A3S4cVCST;VFB;VFF;Vrho0;A4S30Sa7VFF;S98R3S46A2Z90A3S2fS7Sa8Z1S80S3S3S0S0A2M0S0A2G0S9G0S0A2VFF;A4A2U0A3A2F_;F_;Frho;").
Proof.
  intros rho Hav (_ & B & C). split; [|exact C]. unfold uval, xCFG. cbn [eval]. rewrite <- (proj1 Hav 109%positive eq_refl). exact B.
Qed.

Lemma extraOM_client : ltac2:(tb__ "0|1|
S12S14S0S2S3S11S11A2A1S2S3S3S11S0A2S11A2A1S96S83R5A2S62S44Vrho0;R6A3S4cVCST;VFB;VFF;Vrho0;A4S2fS4S4eR7A1S5A3S30S53S9S0S0S1aR9R8A2M0A3R7A2S55R7SeS0S0G0A3A2A2S90VCST;Vrho0;S8aVFB;RaR7A3S8fVFF;RaR6A3R8A5F_;F_;F_;F_;F_;Ffrs;Fkept;Fa;Fo;Frho;").
Proof.
  intros rho o a kept frs BZ Hav HP0 HE Hr. unfold extraOM in HE. apply orb_prop in HE as [HE|HE]; [exact (extra_client rho o a kept frs BZ Hav HP0 HE Hr)|].
  destruct (P0_now rho Hav HP0) as [Hc _]. unfold cfgb in HE. apply andb_prop in HE as [HE Hh]. apply andb_prop in HE as [Hb Hl].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  eapply obj_rangeZ in Hr; [| rewrite Hl; apply soff_lit_small; lia | rewrite Hh; apply soff_lit_small; lia]. rewrite Hb in Hr.
  destruct Hc as (f & sz & fl & Hin & H1 & H2). right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
Qed.
Lemma extraXM_client : ltac2:(tb__ "0|2|
S12S3S11S11A2M0S0S2G0A1S2S3S3S11S0A2S11A2A1S96S83R5A2S62S44Vrho0;R6A3S4cVCST;VFB;VFF;Vrho0;A4S2fS4S4fR7A1S5A3S30S53S98R9S9S11S11R8A3A2M1R7A2S55R7S57G1S98R9SeS11S11R8A3A2A2A2A2S31S90VCST;Vrho0;S8aVFB;RaR7A3S8fVFF;RaR6A3R8A5S9fVXGL;R8A2A2F_;F_;F_;F_;F_;Ffrs;Fkept;Fa;Fr;Frho;").
Proof.
  intros rho r a kept frs BZ Hav HP0 HE Hr. unfold extraXM in HE. apply orb_prop in HE as [HE|HE].
  - left. apply (in_callersH_ok CST NPH HNPH FB FF rho0 (P0_ml CST FB FF) (P0_ml_b CST FB FF) rho a kept frs Hav HP0). exact (extraXH_sound DW rho r a BZ HE Hr).
  - apply xr_eqb_sound in HE. subst r. cbn [fst snd] in Hr. rewrite uval_lit in Hr by lia. destruct (P0_now rho Hav HP0) as [Hc _].
    destruct Hc as (f & sz & fl & Hin & H1 & H2). left. right; right; right. exists f, sz, fl. split; [apply In_FFx; left; exact Hin | lia].
Qed.

Lemma siteP : ltac2:(tb__ "0|0|
S7cS12S2S13A1S2S3S11S11A2A1S2S3S3S11S0A2S11A2A1SbS7A1S2S14A1S12S2S33Q40A1A1S64VAInv;RaR3R2R1A4S7fS13S18RaA1R9A3S2fS4S4dRaA1S5A3S62S44Vrho0;RcA3S4cVCST;VFB;VFF;Vrho0;A4S37Vrho0;RfA2S8bRfS7eS7dR10A1A1A2S3dVFB;R11A2S3eVFF;R12A2S39VFB;R13R12R10A4S8cR13R11A2S8dR14R12A2S38VFF;R16R15R12A4S2fS4SbaR15R14R13R12S4eR11A6S5A3SaaVCST;R18ScS0A1R17R12A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr skip R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR Hchk.
  eapply (robjsP_okA segs AInv CST ALA rho0 FB FF Ai rho facts tv fr skip extraOM R rho1 tp1 md1 HM HF HT HTK HBf HFF HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraOM_client rho o a _ _ (basez_of DW rho facts DW_rng HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteF : ltac2:(tb__ "0|0|
S7cS12S2S13A1S2S3S11S11A2A1S2S3S3S11S0A2S11A2A1S2S14A1S12S2S33Q40A1A1S64VAInv;R9R3R2R1A4S7fS13S18R9A1R8A3S2fS4S4dR9A1S5A3S62S44Vrho0;RbA3S4cVCST;VFB;VFF;Vrho0;A4S37Vrho0;ReA2S8bReS7eS7dRfA1A1A2S39VFB;R10RfRdA4S8cR10ReA2S8dR11RfA2S38VFF;R13R12RfA4S2fS4S99R12R11R10ScS7A1S4eRfA6S5A3Sb8VCST;Vrho0;VFB;VFF;R14R12R11R10A8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hchk.
  eapply (robjsP_okF segs AInv CST ALA rho0 FB FF Ai rho facts tv fr extraOM R rho1 tp1 md1 HM HF HT HTK HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraOM_client rho o a _ _ (basez_of DW rho facts DW_rng HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteH : ltac2:(tb__ "0|1|
S7cS12S2S13A1S2S3S11S11A2A1S2S3S3S11S0A2S11A2A1S2S14A1S12S2S33Q40A1A1S64VAInv;R9R3R2R1A4S7fS13S18R9A1R8A3S2fS4S4dR9A1S5A3S62S44Vrho0;RbA3S4cVCST;VFB;VFF;Vrho0;A4S37Vrho0;ReA2S8bReS7eS7dRfA1A1A2S39VFB;R10RfRdA4S8cR10ReA2S8dR11RfA2S38VFF;R13R12RfA4S2fS4S99R12R11R10ScS7A1S4eRfA6S5A3S14S0S60S14R2R12A3S30S53S9S0S0S1aR17R3A2M0A3R2A2S55R2SeS0S0G0A3A2A2S31S90VCST;Vrho0;S8aVFB;R18R16A3S8fVFF;R18R15A3R3A5S31S30S53Z0R3A2S55R3S9dA2A2Sa9R3A1A2A2F_;F_;Fa;Fo;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr R rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR Hchk.
  eapply (robjsP_hse segs AInv CST ALA rho0 FB FF Ai rho facts tv fr extraOM R rho1 tp1 md1 HM HF HT HTK HN HD HZ HFR Hchk).
  intros o a Ho HE Hr. exact (extraOM_client rho o a _ _ (basez_of DW rho facts DW_rng HF HB) Hav HP0 HE Hr).
Qed.
Lemma siteX : ltac2:(tb__ "0|4|
S7cS12S2S13A1S2S3S11S11A2A1M0S2S3S3S11S0A2S11A2M1A1M2SbS7A1M3S2S14A1G0S12S2S33Q40A1A1S64VAInv;RbR3R2R1A4S7fS13S18RbA1RaA3S2fS4S4dRbA1S5A3S62S44Vrho0;RdA3S4cVCST;VFB;VFF;Vrho0;A4S37Vrho0;R10A2S8bR10S7eS7dR11A1A1A2S3dVFB;R12A2S3eVFF;R13A2S39VFB;R14R13R11A4S8cR14R12A2S8dR15R13A2S38VFF;R17R16R13A4S2fS4S9aVXGL;R16R15R14R13R12S4fR11A8S5A3S30S92VCST;VXGL;Vrho0;VFB;VFF;R18R16G3G2Lskip;R14S7S8eG1R1R16A3Li;R15Xbx2R12A9S30SabVCST;VXGL;R19ScS0A1R18R12A6Sb9R18R12A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fobjs;Fskip;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof.
  intros Ai rho facts tv fr skip objs X rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR Hchk.
  assert (HEX : forall r a, In r X -> extraXM r = true -> uval rho (fst r) <= a < uval rho (fst r) + uval rho (snd r) ->
            pclMA CST rho0 (FBx FB rho tv) (FFx FF rho (match skip with Some i => remove_nth i fr | None => fr end)) a \/ RtCells.in_rangesZ XGL a).
  { intros r a Hr HE Ha. exact (extraXM_client rho r a _ _ (basez_of DW rho facts DW_rng HF HB) Hav HP0 HE Ha). }
  split; [exact (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho facts tv fr skip objs extraXM X rho1 tp1 md1 HM HF (T_ok_T0 rho0 _ Ai HT HTK) HN HD HZ HFR Hchk HEX)|].
  exact (xrs_checkL_okA segs AInv CST XGL ALA HCST HXGL rho0 FB FF Ai rho facts tv fr skip objs extraXM X rho1 tp1 md1 HM HF HT HTK HBf HFF HN HD HZ HFR Hchk HEX).
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S0S2S33Q40A1A1S77F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S49S26S12S2S33Q40A1A1S77S7fS13S18R3A1S15S27R4A1A1A3VTR;S48S32R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S77S77S77S7aR3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_exw : forall (T : Type) (P : T -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S49S49S26S26S89S2S14A1M0S2S3S26S59A2M1A1S2S3S11S11A2M2A1S77S12S2S33Q40A1A1M3G2S60G2R1R5A3S60G2R2S28RbA1A3F_;Fr;S2fSbG0A1S5bRaR9R8A3SdG0R7A2A3S2fS4S5eRbRaR9R8S80G1S26S9S26S59A2R7A4A5S5A3S12G3VTR;S48S32RfRdR2R1A5S5aS32S16S27RdA1A1R2R1RaA5A2Ftp1;Frho1;S2S65A1M4S93S64S4aS32R9R8R10S6G4S94R3S95R2R1A2A4A5R13RaR9R4R2A4R13S88S87RbRfS7bR3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S26S59G4S93S64S12G3G4S93S64S60G1S6S26S59RaR9A4R14A3S4aS32R12R11R19S6G4S94R9S95R8R7A2A4A5R1cR13R12RaR8A4S62S16S27R1aA1A1S88S87R14R18S7bR9R13RaA3A3R19A2R8A3S4aS32R9R8ReS6G4S94R7S95R6R5A2A4A5ReS88S87R16R1aS7bRbR15RcA3A3R1bA2R15RaR9R8R6A6S30Sb6R17S7bRcR16RdA3R1bR1cR1dR10R1eR19RbA9S12S63R18S7bRdR17ReA3R1cR1dS27R1eA1S27R1fA1S27R11A1R1RcA9VTR;S48S32S5cR11S88S87R19R1dS7bReR18RfA3A3R1eA2R18RdRcA5Sb7R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S48S32R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").
Hypothesis CSM : ltac2:(tb__ "0|2|
S7cS12S2S33Q40A1A1VTR;S48S32SaeVAInv;Z1M0R3VKc;A4S72R2R1A5S5aS32Sb5R2R1S8S3S26S59A2M1S6S26S59S6fSadVAInv;VCST;VXGL;G0R3VKc;A6A4SaG1A1A3A5A2Ftp1;Frho1;FAi;").
Definition pure_rule (Pre : axst) (Posts : list leafA) : Prop := ltac2:(tb__ "0|2|
S26S89S2S14A1M0S12S2S33Q40A1A1S35S77S2fSbG0A1S5bR7VPre;R6A3SdG0R5A2A3S2fS4S5dR8VPre;R7R6S80S29S26S2cVPosts;A4A5S5A3S2fS4SbcS44S16S27R9A1A1A2S5A3S2fS4S3bS16S27RaA1A1R5A2S5A3S2fS4S61S13S25S16S27RbA1M1A1A1S15G1A1A3S5A3S29S12S60S29R2VPosts;A3S20S16S27RfA1A1RcR2A3VTR;S48S32VJAv;RbA1Sb3S15S27R10A1A1S5fRfVPre;S2cR4A1R10ReA5A2R3RcA5RaA2F_;F_;Frho';FL;VTR;S48S32VJAv;R8A1RdRaR9A5R7A2F_;F_;F_;F_;F_;F_;FQ;Fnd;Ftp;Frho;FR;Fs;FCl;").
Hypothesis CALL_da : pure_rule Pre_da Posts_da.
Hypothesis REENTER : ltac2:(tb__ "0|4|
S26S35S3S0S11A2M0S12S2S33Q40A1A1M1S0G1S60S3S3S26S35A2M2G0A2S6G2G0S6S26S35R7R6A4R5A4S68A3S30S53Z0S3aS6G2G0S6S26S35R8R7A4R6A4R5A2M3A2S55G3R3A2A2VTR;S48S32VJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S26S35S12S2S33Q40A1A1M0S0G0S60S3S26S59A2S6S26S59R6S85R5A1A4S84A3VTR;S48S32VJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Ltac vmr := vm_compute; reflexivity.
Tactic Notation "innth" integer(n) := cbn [In cutsM exitsM Posts_mlJ]; do n right; left; reflexivity.
Lemma emeas_z0 : ltac2:(tb__ "0|0|
S26S35S0S12S2fS0S3aS6S3S26S35A2S3S0S11A2S6S26S35R4R3A4S6S0S11R2S69A4A4R1A2S56R2S54Z2Z40A2A2A3Frho;Fr;Fnd;FT;").
Proof. intros. unfold emeasA. cbn [eda_rank eda_var fst snd z0 eval]. rewrite lit_unsigned by lia. lia. Qed.

Lemma XH_X_pro : ltac2:(tb__ "0|1|
S12S2S33Q40A1A1M0S0G0S53S56Z5eS54Z2Z40A2A2R2A2VTR;S48S32VJAv;S66A1S73R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. unfold ndP.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv (NDA [] fr_ml [] ANone)) C_pre rho' tp w)).
  { intros [tr [ms md]] Hw. exists (rho_absorb rho [shobj hG 0 16 cells_pro DZero] (vms md tp ms)). rewrite <- C_pre_eq.
    apply (JA_shadow_release segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_ml CST FB FF) FB FF BX PTrue HKc HBX HNP
             [] fr_ml [] ANone 0%nat 160%positive 1 170%positive hG 0 16 cells_pro DZero X_pro objs_pro [] rho tp tr ms md
             eq_refl ltac:(lia) eq_refl X_pro_objs ltac:(lia) ltac:(change (fs_frame_size 1) with 128; lia) eq_refl ltac:(vmr) eq_refl ltac:(vmr)); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR.
    exact (siteF Ai rho _ [] fr_ml objs_pro rho1 tp1 md1 HM HF ltac:(vmr) Hav HP0 HT HTK HN HD HZ HFR ltac:(vmr)). }
  apply TR_exw. intros rho'. apply (REENTER C_pre ndP (92, z0)); [innth 2 | rewrite emeas_z0; lia].
Qed.

Lemma X_epi : ltac2:(tb__ "0|9|
S26S26S12S2S33Q40A1A1M0S0G0S0S2fS11S2dR7A1S17S9eA1A3S2fS4S2bS8S13S1cS2aS45A1S47A2S8S13S1dS1eS45A1S17S58S54Z2M1Z3dA2Z1M2A2A1A2SaS13A1A3A3S15S27R8A1A1A2S5A3S2fS4S1fS27S9cR9S28R9A1S45Z0M3Z10A5A1A1S5A3S2fS4S1fS27S6bRaA1A1A1S5A3S2fS4S4dS15S27RbA1A1A1S5A3S2fS4S52S15S27RcA1A1A1S5A3S2fS4S99S15S27RdA1M4A1SaS3S11S11A2A1M5S6cScS7A1S4eS19G4A1A6S5A3S2fS4S9aVXGL;S15S27ReA1M6A1G5S6cSdS7U0A2S19G6A1S4fS28ReA1A8S5A3S2fS26S6bRfA1ReA3S60S3S3S26S35A2M7S3S0S11A2M8A2S6G7G8S6S26S35RfS66A4S6S0S11RaS69A4A4S68A3S53G3RbA2S53S56S57RcG2A2S54G1Z40A2A2ReA2VTR;S48S32VJAv;S66A1R13R11R10A5VFAM;RfReA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frk;Ftp0;Fb;Ftp;Frho;FC;FY;").
Proof.
  intros Y C rho tp b tp0 rk Hbase Hfe Hwf1 Hwf2 HB HFRF HRO HXL HC HinC Hrk Hb.
  eapply TR_pre; [|apply (REENTER C ndP (rk, z0)); [exact HinC | rewrite emeas_z0; lia]].
  intros w Hw. rewrite <- HC. unfold epi_state, ndP.
  apply (JA_flag_carve segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NPH Kc rho0 (P0_ml CST FB FF) FB FF BX PTrue HKc HBX HNP
           [] fr_ml [] ANone 0%nat 160%positive 1 170%positive (shadow_reopen_stateA Y (ax_X Y) hG 0 16) rho tp w eq_refl ltac:(lia)).
  - exact Hbase.
  - exact Hwf2.
  - intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. cbn [shadow_reopen_stateA ax_S ss_facts ss_objs ax_X] in HF |- *. split.
    + intros o a Ho Hr. apply in_app_or in Ho as [Ho|[<-|[]]].
      * exact (siteH Ai rho _ [] fr_ml _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO o a Ho Hr).
      * right. right. exact (shobj_range_hse hG 160 128 0 16 rho _ a sz_rng ltac:(lia) ltac:(cbn; lia) HF HFRF Hr).
    + exact (proj2 (proj2 (siteX Ai rho _ [] fr_ml (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL))).
  - apply (JA_shadow_reopen segs HTOP AInv CST XGL ALA HCST HXGL LFSH NPH Kc rho0 (P0_ml CST FB FF) FB FF BX PTrue HKc HBX HNP
             [] fr_ml [] ANone 0%nat 160%positive 1 170%positive hG 0 16 Y (ax_X Y) rho tp w eq_refl ltac:(lia) Hbase ltac:(lia)
             ltac:(change (fs_frame_size 1) with 128; lia) Hfe (fun r H => H) Hwf1); [|exact Hw].
    intros Ai rho1 tp1 md1 HF HP0 Hav HM HT HTK HBf HFF HN HD HZ HFR. split.
    + exact (siteF Ai rho _ [] fr_ml _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HN HD HZ HFR HRO).
    + intros r y Hr Hy. left. exact (proj1 (siteX Ai rho _ [] fr_ml (Some 0%nat) _ _ rho1 tp1 md1 HM HF HB Hav HP0 HT HTK HBf HFF HN HD HZ HFR HXL) r y Hr Hy).
Qed.

Lemma XH_E_da : ltac2:(tb__ "0|1|
S12S2S33Q40A1A1M0S0G0S53S56Z5aS54Z2Z40A2A2R2A2VTR;S48S32VJAv;S66A1S6dR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ [AXSplit 0 (SLit (-96))] rho E_da0 E_da tp w E_da_eq Hw)|].
  apply (CALL_da E_da s_da R_da rho tp ndP _); [vmr|vmr|vmr|vmr|vmr|].
  intros L rho' HL Hag. cbn [In Posts_da] in HL. destruct HL as [<-|[]]. cbn [la_state]. rewrite T_da0_eq.
  eapply TR_pre; [intros w Hw; exact (SPA_axforms segs _ xf_tda rho' T_da0 Y_da tp w Y_da_eq Hw)|].
  apply (X_epi Y_da C_epi rho' tp b tp0 50); [vmr|vmr|vmr|vmr|vmr|vmr|vmr|vmr| exact C_epi_eq | innth 3 | lia | lia].
Qed.

Lemma X_X_rl : ltac2:(tb__ "0|7|
S26S26S26S12S2S33Q40A1A1M0S0G0S0S2fSbS26A1Sa6R8S8Sa4Sa5S76A1SaSa4A1A3A2SdS26R7A2A3S2fS26S2eR8Sb2S27R8A1M1S81S14UcM2S19G1A1A3A2A2R7A3S2fS4S9bPa0PaaS45Z1M3S82S14G2S19S27R9A1A1A3A5S5A3S2fS4S2bS8S13S1cS2aS45A1S47A2S8S13S1dS1eS45A1S17S58S54Z2M4Z3dA2G3A2A1A2SaS13A1A3A3S15S27RaA1A1A2S5A3S2fS4S3bS16S27RbA1A1S66A2S5A3S60S3S3S26S35A2M5S3S0S11A2M6A2S6G5G6S6S26S35RbS67A4S6S0S11R6S69A4A4S68A3S53Z0R7A2S53S56S57R8G3A2S54G4Z40A2A2RaA2VTR;S48S32VJAv;S66A1R10RdRcA5VFAM;RbRaA2A2F_;F_;F_;F_;F_;F_;F_;F_;Frk;Ftp0;Fb;Ftp;Frho;FC;FX1;FX;").
Proof.
  intros X X1 C rho tp b tp0 rk HX1 HC HR Hfe Hnb HinC Hrk Hb.
  apply (TR_pre (fun w => exists rho', SPA segs (JAv nd0) C rho' tp w)).
  { intros [tr [ms md]] Hw. pose proof (SPA_axforms segs _ [AXSelect sel_rel] rho X X1 tp _ HX1 Hw) as Hw1.
    exists (rho_absorb rho (skipn 12 (ss_objs (ax_S X1))) (vms md tp ms)). rewrite <- HC.
    change (ax_setS X1 (set_objs (ax_S X1) (firstn 12 (ss_objs (ax_S X1))))) with (drop_lastA X1 (firstn 12 (ss_objs (ax_S X1)))).
    unfold nd0, ND. change (@nil (sv * Z * sv)) with (remove_nth 0 fr_ml). unfold ndP in Hw1, Hnb.
    apply (JA_release_inline segs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.eb.Lib_arena_alloc.HTOP_ok AInv CST XGL ALA HCST HXGL LFLAG LFSH NPH Kc rho0 (P0_ml CST FB FF) FB FF BX PTrue HKc HBX HNP
             [] fr_ml [] ANone 0%nat 160%positive 1 170%positive hG X1 (firstn 12 (ss_objs (ax_S X1))) (skipn 12 (ss_objs (ax_S X1))) rho tp tr ms md);
      [reflexivity | lia | symmetry; apply firstn_skipn | exact HR | exact Hfe | exact Hnb | intros A1 A2 _; exact I | exact Hw1]. }
  apply TR_exw. intros rho'. apply (REENTER C nd0 (rk, z0)); [exact HinC | rewrite emeas_z0; lia].
Qed.
Lemma XH_X_rl : ltac2:(tb__ "0|1|
S12S2S33Q40A1A1M0S0G0S53S56Z1eS54Z2Z40A2A2R2A2VTR;S48S32VJAv;S66A1S74R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply (X_X_rl X_rl _ C_rl rho tp b tp0 20 X_rl_eq); [vmr|vmr|vmr|vmr| innth 4 | lia | lia].
Qed.

Lemma XH_E_sm : ltac2:(tb__ "0|1|
S12S2S33Q40A1A1M0S0G0S53S56Z62S54Z2Z40A2A2R2A2VTR;S48S32VJAv;S67A1S6eR5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof.
  intros rho tp b tp0 Hb. apply TR_facts. intros HF.
  apply (smalloc_callT segs AE_A AInv CST XGL ALA HCST HXGL NPH Kc rho0 (P0_ml CST FB FF) FB FF BX PTrue HKc TR TR_facts TR_ex TR_pre TR_callP
           1 E_sm0 s_sm R_sm rho tp nd0 160 170 (FAM b tp0) CSM).
  - lia.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - intros A A' _; exact I.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR (rho1 & tp1 & md1 & HM) HT HTK. destruct (P0_now rho Hav HP0) as [_ HC0].
    cbn [nd_tv nd_fr nd0 ND] in HN, HD, HZ, HFR |- *.
    split; [|split].
    + exact (siteP Ai rho _ [] [] None R_sm rho1 tp1 md1 HM HF' ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HD HZ HFR ltac:(vmr)).
    + exact (proj1 (proj2 (siteX Ai rho _ [] [] None (ss_objs (ax_S E_sm0)) (ax_X E_sm0) rho1 tp1 md1 HM HF' ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HD HZ HFR ltac:(vmr)))).
    + split; [change (wsub_get s_sm 12) with (SLit 96); rewrite uval_lit by lia; change (fs_frame_size 1) with 128; lia|].
      unfold ffpairs. change (map (fun y : Z * Z * Z => fst y) FF) with (map fst FF). rewrite HC0. cbn. lia.
  - intros rho' tp'. rewrite T_sm_eq.
    eapply TR_pre with (P := SPA segs (JAv ndP) T_sm1 rho' tp').
    { intros w Hw. exact (SPA_axforms segs _ [AXSelect sel_sm] rho' T_sm T_sm1 tp' w T_sm1_eq Hw). }
    apply (TR_pre (fun w => exists rho2, SPA segs (JAv ndP) C_pro rho2 tp' w)).
    { intros w Hw. unfold ndP.
      destruct (JA_frame_open segs HTOP AInv CST XGL ALA HCST HXGL LFLAG NPH Kc rho0 (P0_ml CST FB FF) FB FF BX PTrue HKc HBX HNP
                  [] fr_ml [] ANone 0%nat 160 1 170 T_sm1 objs_sm1 X_ml [] rho' tp' w eq_refl ltac:(lia) eq_refl T_sm1_objs T_sm1_X
                  ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc) eq_refl ltac:(OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc)) as (rho2 & _ & Hw2); [| exact Hw |].
      - intros Ai rho1 tp1 md1 HF2 HP0 Hav HM HT HTK HBf HFF HN HDt HZt HFR. rewrite app_nil_r.
        exact (proj1 (siteX Ai rho' _ [] fr_ml (Some 0%nat) (ss_objs (ax_S T_sm1)) X_ml rho1 tp1 md1 HM HF2 ltac:(vmr) Hav HP0 HT HTK HBf HFF HN HDt HZt HFR ltac:(vmr))).
      - exists rho2. rewrite app_nil_r in Hw2. rewrite C_pro0_eq in Hw2. rewrite <- C_pro_eq.
        apply (SPA_x_len0 segs (JAv ndP) C_pro0 160 5 rho2 tp' w); [vmr | lia | vmr | exact Hw2]. }
    apply TR_exw. intros rho2. apply (REENTER C_pro ndP (96, z0)); [innth 1 | rewrite emeas_z0; lia].
Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S26S35S3S0S11A2M0S12S2S33Q40A1A1M1G1S60S3S3S26S35A2M2G0A2S6G2G0S6S26S35R6R5A4R4A4S75A3VTR;S48S32VJAv;R6A1R7R4R3A5VFAM;S3aS6G2G0S6S26S35R7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsM] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[]]]]]]]; injection H as <- <- <-.
  - apply XH_E_sm. rewrite emeas_z0. lia.
  - apply XH_X_pro. rewrite emeas_z0. lia.
  - apply XH_E_da. rewrite emeas_z0. lia.
  - apply XH_X_rl. rewrite emeas_z0. lia.
  - apply POST. innth 0.
  - apply POST. innth 1.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S43S32VKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
SafS32SacVAInv;VCST;VXGL;A5").

Theorem handle_mtllib_sum : ltac2:(tb__ "0|0|
S2S33Q40A1A1S79S32Vok;S48S32S3cVAInv;VCST;VXGL;VKc;S4cVCST;VFB;VFF;A3VFB;VFF;VBX;S36S67AaS6aVrho0;R1A5S5aS32S44Vrho0;R1S84A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NPH Kc rho0 (P0_ml CST FB FF) FB FF BX PTrue HKc ALA FUEL_ml cutpcs_ml NPH
                (map edropA cutsM) (map edropA exitsM) ok (Q tp0) Hok (ejcertA_jcertA segs NPH _ _ _ _ _ ejcertM_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0 & Hin). cbn in E0. injection E0 as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsM)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (@triple_ex segs ok) (call_soundPA3 segs ok)) with (rvX := rv) (tp0 := tp0).
       - intros Ai rho1 tp1. apply (aca_stack_malloc _ _ _ _ _ AC 1 ltac:(cbn; tauto)); [exact HKc|]. eapply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & K & _). exact K.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA segs AInv CST XGL NPH Kc rho0 (P0_ml CST FB FF) FB FF BX PTrue HKc ALA ok Cl Pre_da s R Posts_da rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply diag_append_sum; [apply frozen_ok_frameA; exact Hok | apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb]].
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NPH Kc rho0 (P0_ml CST FB FF) FB FF BX PTrue ok (map edropA cutsM) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NPH Kc (P0_ml CST FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_mlJ P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
Sb0S32SacVAInv;VCST;VXGL;A5").

Theorem handle_mtllib_sum_ex : ltac2:(tb__ "0|0|
S2S33Q40A1A1S78S32S48S32S3cVAInv;VCST;VXGL;VKc;S4cVCST;VFB;VFF;A3VFB;VFF;VBX;S36S67AaS6aVrho0;R1A5S5aS32S44Vrho0;R1S84A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NPH Kc rho0 (P0_ml CST FB FF) FB FF BX PTrue HKc ALA FUEL_ml cutpcs_ml NPH cutsM exitsM (Q tp0) ejcertM_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NPH Kc rho0 (P0_ml CST FB FF) FB FF BX PTrue) cutsM) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (@etriple_ex segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros Ai rho1 tp1. apply (acx_stack_malloc _ _ _ _ _ ACX 1 ltac:(cbn; tauto)). exact HKc.
       - intros Cl s R rho1 tp1 nd Q' He Hc Hn Hb Hf Hk.
         apply (pure_callA_ex segs AInv CST XGL NPH Kc rho0 (P0_ml CST FB FF) FB FF BX PTrue HKc ALA Cl Pre_da s R Posts_da rho1 tp1 nd Q'); try assumption.
         intros rho2 tp2. apply diag_append_sum_ex. apply (frozen_stable NF (ss_next (ax_S Cl)) nd rho1); [apply Pos.leb_le; exact Hn | exact Hb].
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NPH Kc rho0 (P0_ml CST FB FF) FB FF BX PTrue cutsM T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NPH Kc (P0_ml CST FB FF) FB FF BX PTrue rho0 tp0 nd Posts_mlJ P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_handle_mtllib_pf.

(* [comment removed for export] *)
Module Lib_opt_push1_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_opt_push1"; "s_vr"; "E_2d"; "E_2v"; "E_vrL"; "Xk_op"; "pK"; "xf_vback"; "bd_op"; "pD"; "R_2d"; "R_2v"; "R_vrL"; "xf_vcall"; "T_fail2d0"; "T_fail2v0"; "T_failL0"; "T_grown2d0"; "T_grown2v0"; "T_grownL0"; "T_keep2d0"; "T_keep2v0"; "T_keepL0"; "vKg2d"; "vKg2v"; "vKgL"; "E_2d0"; "E_2v0"; "E_vrL0"; "FUEL_op"; "T_fail2d"; "T_fail2v"; "T_failL"; "T_grown2d"; "T_grown2v"; "T_grownL"; "T_keep2d"; "T_keep2v"; "T_keepL"; "cutpcs_all"; "cutsO"; "exitsO"; "vDg2d"; "vDg2v"; "vDgL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN"; "Pre_vr"; "P_grown"; "P_keep"; "P_fail"; "bdP"; "tv0"; "vN"; "tvP"; "vK"; "vKn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "@Corelib.Init.Datatypes"; "list"; "Some"; "option"; "prod"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "tv_vec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_subst"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ejcertA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_opt_push1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_opt_push1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRNAddr RA.ReallocAddr OPAddr.

Lemma ejcertO_ok : ltac2:(tb__ "0|0|
S0S3dS48S46S47S1eS28P64S29S2aA7S3eA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma E_vrL_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S1dSeA2S3aS1S5A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_2v_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S1cSeA2S3aS1S4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_2d_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S1bSeA2S3aS1S3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keepL0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS5S2S5A1SdS30S6A6S17A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_failL0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS5S2S5A1SdS31S6A6S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grownL0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS5S2S5A1SdS2fS6A6S14A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep2v0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS4S2S4A1ScS30S6A6S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail2v0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS4S2S4A1ScS31S6A6S10A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown2v0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS4S2S4A1ScS2fS6A6S13A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep2d0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS3S2S3A1SbS30S6A6S15A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail2d0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS3S2S3A1SbS31S6A6SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown2d0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS3S2S3A1SbS2fS6A6S12A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keepL_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S17S8A2S3aS1S27A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_failL_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S11S8A2S3aS1S21A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grownL_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S14S8A2S3aS1S24A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep2v_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S16S8A2S3aS1S26A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail2v_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S10S8A2S3aS1S20A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown2v_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S13S8A2S3aS1S23A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep2d_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S15S8A2S3aS1S25A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail2d_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40SfS8A2S3aS1S1fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown2d_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S12S8A2S3aS1S22A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma imp_keepL_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S5A1S2eS30S5A4S33A2S41SaS7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keepL_bd : ltac2:(tb__ "0|0|
S0S39S45A1S44S3fS2S5A1S2eS30S5A4S32S34S36A2A2S9S7A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_failL_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S5A1S2eS31S5A4S33A2S41SaS7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grownL_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S5A1S2eS2fS5A4S35A2S41S2dS1aA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grownL_bd : ltac2:(tb__ "0|0|
S0S39S45A1S44S3fS2S5A1S2eS2fS5A4S32S34S37A2A2S9S1aA1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep2v_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S4A1S2eS30S4A4S33A2S41SaS7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep2v_bd : ltac2:(tb__ "0|0|
S0S39S45A1S44S3fS2S4A1S2eS30S4A4S32S34S36A2A2S9S7A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail2v_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S4A1S2eS31S4A4S33A2S41SaS7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown2v_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S4A1S2eS2fS4A4S35A2S41S2cS19A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown2v_bd : ltac2:(tb__ "0|0|
S0S39S45A1S44S3fS2S4A1S2eS2fS4A4S32S34S37A2A2S9S19A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep2d_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S3A1S2eS30S3A4S33A2S41SaS7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep2d_bd : ltac2:(tb__ "0|0|
S0S39S45A1S44S3fS2S3A1S2eS30S3A4S32S34S36A2A2S9S7A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail2d_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S3A1S2eS31S3A4S33A2S41SaS7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown2d_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S3A1S2eS2fS3A4S35A2S41S2bS18A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown2d_bd : ltac2:(tb__ "0|0|
S0S39S45A1S44S3fS2S3A1S2eS2fS3A4S32S34S37A2A2S9S18A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Lib_opt_push1_eqs.

(* [comment removed for export] *)
Module Lib_opt_push1_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "ax_X"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "valuation"; "SPUle"; "SLit"; "ss_facts"; "sprop_eqb"; "ss_next"; "sobj"; "holds"; "SVar"; "rw"; "SMd"; "SAlu"; "SPBranch"; "sprop_below"; "DUnknown"; "SPNot"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "odefault"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "bool"; "list"; "true"; "cons"; "nil"; "app"; "Some"; "fst"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "emeasA"; "PTrue"; "JA_pre"; "nd_below"; "JA"; "JLA"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bd_subst"; "bud_le"; "BXok_d"; "bd_wpos"; "bitem"; "bxt"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "pow"; "lt"; "add"; "sub"; "div"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_opt_push1"; "ndC"; "pK"; "pC"; "VB"; "nd0"; "CM"; "pCM"; "s_vr"; "pD"; "vDEF"; "vVALS"; "bd_op"; "vVIDX"; "C_L"; "E_2d0"; "E_2v0"; "E_vrL0"; "Pre_op"; "X_back0"; "X_back1"; "inL_at"; "vALo"; "z0"; "O_deflt"; "O_vals"; "PD_op"; "PD_vrN"; "P_op0"; "P_op1"; "X_Lin0"; "X_Lin1"; "Xk_op"; "cutsO"; "exitsO"; "nd0'"; "nd1"; "slot4_at"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.Lists.List"; "existsb"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ei.Lib_opt_push1_pf"; "P0_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN"; "B32"; "vC"; "vK"; "spm"; "vV"; "Pre_vr"; "nd0"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ei.Lib_opt_push1_pf.Sum"; "Posts_op"; "baseOF"; "JLo"; "baseOz"; "base_factsO"; "is_siteobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "wsub"; "wsub_id_below"; "sv_subst"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "tv_vec"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.Riscv.Instr"; "M_DIVU"; "ALU_ADD"; "BC_GEU"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Lib_vec_reserveN_pf"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "tvz"; "FBx";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "PostsC"; "FFx"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "payA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_opt_push1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Lib_vec_reserveN_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_opt_push1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ei.Lib_opt_push1_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRNAddr RA.ReallocAddr OPAddr.
Local Open Scope lazy_bool_scope.

Definition P0_op (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S1S78VFF;S39Q40M0S14Vr;PcA2A2Z20A3S1S78VFF;S39G0S14Vr;P24A2A2Z30A3S1S78VFF;S39G0S14Vr;P21A2A2S42Z4S4dA2M1A3S78VFF;S39G0S14Vr;P22A2A2G1A3A2A2A2").

Lemma uval_divu_lit : ltac2:(tb__ "0|0|
SbSaS8S1S44Z0R1A2S44R1S43Z2Z40A2A2A2S0S8S3aR4S15S9aR3SdR2A1A3A2S47S3aR4R3A2R2A2A3F_;Fc;Fa;Frho;").
Proof.
  intros rho a c Hc. unfold uval. cbn [eval]. unfold mul_div.
  rewrite Z_to_bv_unsigned. rewrite bv_wrap_small by (unfold bv_modulus; cbn; lia).
  destruct (Z.eqb_spec c 0) as [E|E]; [lia|]. rewrite bv_divu_unsigned. rewrite Z_to_bv_unsigned. rewrite bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

Lemma VB_val : ltac2:(tb__ "0|0|
SbSaS8S41S3aR3R2A2S79A2S1S41Z0R2A2S44R2Z40A2A2S0S8S3aR5S4bR4R3A2A2S45S42Z20S46S45S43Z2Z2fA2Z1000A2S3aR5R4A2A2A2R3A2A3F_;F_;Fph;Fc;Frho;").
Proof.
  intros rho c ph Hc Hph. unfold VB, two47, RA.two47, Lib_scan_double.two47, B32 in *. pose proof (uval_range rho c) as Rc.
  assert (ES : uval rho (SAlu ALU_SUB (SLit (2 ^ 47 + 4096)) c) = 2 ^ 47 + 4096 - uval rho c).
  { unfold uval in *. rewrite U_sub, U_lit. unfold M64v. rewrite (Z.mod_small (2 ^ 47 + 4096)) by lia. apply Z.mod_small. lia. }
  assert (EM : uval rho (SMd M_MUL (SLit 32) (SAlu ALU_SUB (SLit (2 ^ 47 + 4096)) c)) = 32 * (2 ^ 47 + 4096 - uval rho c)).
  { rewrite uval_mul_lit by (rewrite ?ES; lia). rewrite ES. reflexivity. }
  rewrite uval_add_small by (rewrite EM, uval_lit by lia; lia). rewrite EM, uval_lit by lia. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sb4SbS23S38Q40A1A1S95OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
SaeS2bVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S8SafVCST;R1A2S1S41Z0R2A2S44R2SaaA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S8SafVXGL;R1A2S1S41Z0R2A2S44R2SaaA2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S23S21S21S8S8A2S8A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 4 BX.
Variable rho0 : valuation.

Definition JLo (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S32VAInv;VCST;VXGL;VKc;S77VFB;VFF;A2VFB;VFF;VBX;S2eVnd;Aa").
Definition Posts_op : list (axst * jpostA) := ltac2:(tb__ "0|1|
S25S21S4S72A2M0S20S4S72S64S88S6bA1A4S25G0S20S4S72S63S88S6aA1A4S26G0A1A3A3").
Lemma Posts_op_PD : ltac2:(tb__ "0|0|
S0S23S21S4S72A2A1S86Sa6VAInv;VCST;VXGL;VKc;S77S2eS61VFB;VFF;VBX;AaA3").
Proof. reflexivity. Qed.

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S31VAInv;VCST;VXGL;S6eVKc;Vrho0;S77VFB;VFF;A2VFB;VFF;VBX;S2eVnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S21S4S2cA2Sa2Fn;") := ltac2:(tb__ "0|0|
S33VAInv;VCST;VXGL;S6eVKc;Vrho0;S77VFB;VFF;A2VFB;VFF;VBX;S2eAb").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
S73S2bS6eVrho0;Vtp0;S86A5").

Definition base_factsO : list sprop := ltac2:(tb__ "0|5|
S25S9ScS13PaA1M0SdS80A1M1A2S25S9ScS13P1eA1M2S7cZ80A1A2S25S9ScSdZ1000A1M3S52A2S25S9ScS16S9bS52SdS42Z4S4dA2A1M4A3G2A2S25S9ScS52G1A2S25S9ScG3S51A2S25S9ScS16S9bS51G4A3G2A2S25S9ScS51G1A2S25S9ScS54SdS43Z2Z1bA2A1A2S25S9ScG2G0A2S25S9ScSdZ7fff7f800000A1G2A2S25S9ScG2SdZ7fffff800000A1A2S26S9A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition baseOF (F : list sprop) : bool := ltac2:(tb__ "0|0|
S71S9S9S6fS9SfR1A1VF;A3Lp;S8aA3").
Record baseOz (rho : valuation) : Prop := BZO {
  bz_sp : aceil + 128 <= uval rho (SVar 10) <= 2 ^ 47;
  bz_vals : 4096 <= uval rho vVALS /\ uval rho vVALS + 4 * CM <= bv_unsigned (rw rho V_TOP);
  bz_def : 4096 <= uval rho vDEF /\ uval rho vDEF + 4 * CM <= bv_unsigned (rw rho V_TOP);
  bz_vidx : uval rho vVIDX <= 2 ^ 27;

  bz_top : bv_unsigned (rw rho V_TOP) + 128 <= uval rho (SVar 10) /\ 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma uval_spm : ltac2:(tb__ "0|1|
SbS8S1S41Z0R1A2S41R1S3aR2S13PaA1M0A2A2A2S0S8S3aR3S7cR2A1A2S46S3aR3G0A2R2A2A3F_;Fk;Frho;").
Proof.
  intros rho k Hk. unfold spm, RA.spm, uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *.
  rewrite Zplus_mod_idemp_r. replace (x + - k) with (x - k) by lia. apply Z.mod_small. lia.
Qed.
Lemma baseOz_of : ltac2:(tb__ "0|0|
SbS23S9A1S92S9S12R2A1R1A3S0S22S87R2A1S24A3S89R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF HB. unfold baseOF in HB.
  assert (G : forall p, In p base_factsO -> holds rho p).
  { intros p Hp. apply (holds_mem rho F p HF). exact (proj1 (forallb_forall _ _) HB p Hp). }
  cbn [base_factsO] in G.
  pose proof (G _ ltac:(left; reflexivity)) as F1. pose proof (G _ ltac:(do 1 right; left; reflexivity)) as F2.
  pose proof (G _ ltac:(do 2 right; left; reflexivity)) as F3. pose proof (G _ ltac:(do 3 right; left; reflexivity)) as F4.
  pose proof (G _ ltac:(do 4 right; left; reflexivity)) as F5. pose proof (G _ ltac:(do 5 right; left; reflexivity)) as F6.
  pose proof (G _ ltac:(do 6 right; left; reflexivity)) as F7. pose proof (G _ ltac:(do 7 right; left; reflexivity)) as F8.
  pose proof (G _ ltac:(do 8 right; left; reflexivity)) as F9. pose proof (G _ ltac:(do 9 right; left; reflexivity)) as F10.
  pose proof (G _ ltac:(do 10 right; left; reflexivity)) as F11. pose proof (G _ ltac:(do 11 right; left; reflexivity)) as F12.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12.
  change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in *.
  unfold two47, RA.two47, Lib_scan_double.two47, CM in *. rewrite !uval_lit in F1, F3, F5, F6, F8, F9, F11, F12 by lia.
  pose proof (uval_range rho vVALS). pose proof (uval_range rho vDEF).
  rewrite uval_add_small in F4 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F4 by lia.
  rewrite uval_add_small in F7 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F7 by lia.
  rewrite uval_spm in F2 by lia.
  constructor; rewrite ?aceil_val; unfold CM; lia.
Qed.

Lemma P0o_now : ltac2:(tb__ "0|1|
SbS9fS6eVrho0;R1A3S77VFB;VFF;Vrho0;A3S1S78VFF;S3aR3S7dA2Z20A3S1S78VFF;S3aR3S5dA2Z30A3S1S78VFF;S3aR3S52A2S42Z4S4dA2M0A3S78VFF;S3aR3S51A2G0A3A2A2A2F_;F_;Frho;").
Proof.
  intros rho Hav (A & B & C & D). unfold uval, vV, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.vV, vALo, vVALS, vDEF. cbn [eval].
  rewrite <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 36%positive eq_refl), <- (proj1 Hav 33%positive eq_refl), <- (proj1 Hav 34%positive eq_refl).
  auto.
Qed.

Lemma tvz_kd : ltac2:(tb__ "0|1|
SbSaSaSa4R3S97R2R1A2A2S41S3aR4R2A2S79A2S2S0S8S3aR5R3A2Z0M0A3A1S2S0S8S3aR6R5A2G0A3A1F_;F_;F_;Fk;Fd;Frho;").
Proof.
  intros rho d k HZ HK Hk Hd. apply Forall_inv in HZ. unfold tnz, tvv in HZ. cbn [fst snd] in HZ. unfold uval in Hd, Hk, HK.
  specialize (HZ ltac:(intros H; exact (H Hd))). unfold B32 in HK.
  pose proof (uval_mul_lit rho 4 k ltac:(lia) ltac:(unfold uval; lia)) as E4. unfold uval, kb4 in E4. unfold kb4 in HZ. rewrite E4 in HZ. lia.
Qed.

Definition is_siteobj (o : sobj) : Prop := ltac2:(tb__ "0|0|
S3S1S0SaS1bVo;A1S13PaA1A3S1S0SaS1eVo;A1SdN80A1A3S1S0SaS1dVo;A1SdZ0A1A3S0S1fS1cVo;A1S19A3A2A2A2S3S0S11Vo;S60A3S0S11Vo;S5fA3A2A2").
Lemma HIN_site : ltac2:(tb__ "0|2|
S4S23S11A1SbS94S11S70S11R1R4A3S8bR2A1F_;Fo;S0SaS8eS4fR5A1P11A2S49A3S0SaS8eS4fR6A1PfA2S50A3S0SaS8eS4fR7A1PcA2S7dA3S0SaS8eS4fR8A1PeA2S5dA3S0S22S6fS9SfScS49SdS79A1A2A1SeS5R9A1A1A3S24A3S0S22S87SeS5RaA1A1A1S24A3S92S9S12R9A1SeS5RbA1A1A3S77VFB;VFF;Vrho0;A3S9fS6eVrho0;RbA3Sa4RcS97S50S49A2A2S1Sa8VCST;Vrho0;VFB;VFF;RdS26S21SaSaA2A1M0S26S21S21SaS8A2SaA2A1M1ReA8S1Sa9VCST;VXGL;Vrho0;VFB;VFF;RdG0G1S67A9S9eSa5VFB;RdG0A3Sa7VFF;RdG1A3S8dS8cRdReRcA3S4fRfA1A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;Frho;FR;FE;").
Proof.
  intros E R rho ms HR H17 H15 H12 H14 HK HB HF HP0 Hav HZ. destruct (P0o_now rho Hav HP0) as (HV & HA & HS & HD).
  pose proof (baseOz_of rho _ HF HB) as [Bsp Bv Bd _ Btop]. rewrite aceil_val in *. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET.
  split; [|split].
  - intros o a Ho Hr. destruct (HR o Ho) as [(H1 & H2 & H3 & H4)|[->| ->]].
    + left. destruct o as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi ob_dflt] in H1, H2, H3, H4. subst. apply range_lit' in Hr; [|lia|lia]. lia.
    + unfold O_vals in Hr. apply range_lit' in Hr; [|lia|unfold CM; lia]. eapply (infrFF_pclMA CST rho0 FF); [exact HS | unfold CM in *; lia].
    + unfold O_deflt in Hr. apply range_lit' in Hr; [|lia|unfold CM; lia]. eapply (infrFF_pclMA CST rho0 FF); [exact HD | unfold CM in *; lia].
  - intros r a Hr Ha. cbn in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; rewrite uval_lit in Ha by (unfold CM; lia); left.
    + eapply (infrFF_pclMA CST rho0 FF); [exact HV | lia].
    + eapply (infrFF_pclMA CST rho0 FF); [exact HA | lia].
    + eapply (infrFF_pclMA CST rho0 FF); [exact HS | lia].
    + eapply (infrFF_pclMA CST rho0 FF); [exact HD | lia].
  - unfold P0_vr. rewrite !rw_call'. rewrite H17, H15, H12, H14.
    split; [|split].
    + intros Hk. pose proof (holds_mem _ _ _ HF HK) as HKB. rewrite h_ule in HKB. unfold B32 in HKB. rewrite uval_lit in HKB by lia. exact (tvz_kd rho pD pK HZ HKB Hk).
    + destruct HV as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin|]. unfold uval in H1, H2. lia.
    + destruct HA as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin|]. unfold uval in H1, H2. lia.
Qed.

Lemma slot4_holds : ltac2:(tb__ "0|1|
SbS23S9A1SaS92S9S12R3A1R2A3S0S22S6fS9SfScS4eR2A2A1R3A3S24A3S0S22S6fS9SfScR3SdS79A1M0A2A1R4A3S24A3S0S22S6fS9SfScS4aS49A2A1R5A3S24A3S0S22S6fS9SfScS49G0A2A1R6A3S24A3S12R8S6cR6A1A2F_;F_;F_;F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF H1 H2 H3 H4. pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2.
  pose proof (holds_mem _ _ _ HF H3) as F3. pose proof (holds_mem _ _ _ HF H4) as F4. rewrite h_ule in F1, F2, F3, F4.
  unfold B32 in F2, F4. rewrite uval_lit in F2 by lia. rewrite uval_lit in F4 by lia. unfold pCM in F1. pose proof (uval_range rho pC) as RC. unfold CM in *.
  rewrite uval_add_small in F1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F1 by lia.
  unfold slot4_at. apply (proj2 (h_ule _ _ _)).
  assert (E1 : uval rho (SMd M_MUL pC (SLit 4)) = uval rho pC * 4) by (rewrite uval_mul_comm; rewrite uval_mul_lit by lia; lia).
  assert (E2 : uval rho (kb4 k) = 4 * uval rho k) by (unfold kb4; rewrite uval_mul_lit by lia; lia).
  unfold CM. rewrite uval_add_small by (rewrite E1, uval_lit by lia; lia). rewrite E1, E2, uval_lit by lia. lia.
Qed.

Lemma payA_same : ltac2:(tb__ "0|1|
SbOF_;S23S9A1S23S3fA1S0S22S3eR1A1S24A3Sb3S6eVrho0;R4R3SdZ0M0A1G0R2R2A8F_;Fbd;Ffacts;FP0f;").
Proof.
  intros P0f facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia. split; [lia|]. split; [lia | exact Hn].
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S8S23S38Q40A1A1S81F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S36S4SbS23S38Q40A1A1S81S92S9S12R3A1SeS5R4A1A1A3VTR;S35S2bR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S81S81S81S84R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S36S36S4S4S8fS23S11A1M0S23S21S4S72A2M1A1S23S21SaSaA2M2A1S81SbS23S38Q40A1A1M3G2S70G2R1R5A3S70G2R2S7RbA1A3F_;Fr;S0S2aG0A1S76RaR9R8A3S28G0R7A2A3S0S22S75RbRaR9R8S93G1S4S29S4S72A2R7A4A5S24A3SbG3VTR;S35S2bRfRdR2R1A5S73S2bS10S5RdA1A1R2R1RaA5A2Ftp1;Frho1;S23S96A1M4S94S95S37S2bR9R8R10S20G4S98R3S99R2R1A2A4A5R13RaR9R4R2A4R13S8dS8cRbRfS85R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S4S72G4S94S95SbG3G4S94S95S70G1S20S4S72RaR9A4R14A3S37S2bR12R11R19S20G4S98R9S99R8R7A2A4A5R1cR13R12RaR8A4S9fS10S5R1aA1A1S8dS8cR14R18S85R9R13RaA3A3R19A2R8A3S37S2bR9R8ReS20G4S98R7S99R6R5A2A4A5ReS8dS8cR16R1aS85RbR15RcA3A3R1bA2R15RaR9R8R6A6S1Sb1R17S85RcR16RdA3R1bR1cR1dR10R1eR19RbA9SbSa0R18S85RdR17ReA3R1cR1dS5R1eA1S5R1fA1S5R11A1R1RcA9VTR;S35S2bS74R11S8dS8cR19R1dS85ReR18RfA3A3R1eA2R18RdRcA5Sb2R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S35S2bR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CVRES : ltac2:(tb__ "0|1|
S23S21S8S8A2M0A1S23S21G0S8A2A1S40SbS23S38Q40A1A1S3dZ3R3A2VTR;S35S2bS2fVAInv;VCST;VXGL;VKc;S9eR6R5A2R6R5R4S2eS7fAaS7eR3R2A5S73S2bS6eR3R2Sa6VAInv;VCST;VXGL;VKc;S9eS2eS62R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S4S2cS21S8SaA2M0SbS23S38Q40A1A1M1S8G1S70S21S21S4S2cA2M2G0A2S20G2G0S20S4S2cR7R6A4R5A4S68A3S1S41Z0S2dS20G2G0S20S4S2cR8R7A4R6A4R5A2M3A2S44G3R3A2A2VTR;S35S2bVJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S4S2cSbS23S38Q40A1A1M0S8G0S70S21S4S72A2S20S4S72R6S88R5A1A4S86A3VTR;S35S2bVJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Tactic Notation "innth" integer(n) := cbn [In cutsO exitsO Posts_op PD_op]; do n right; left; reflexivity.

Lemma meas_VB : ltac2:(tb__ "0|2|
S4S2cS8SaS8SbS41S3aR1R3A2S79A2S1S41Z0R3A2S44R3Z40M0A2A2S0S8S2dS20S21S4S2cA2S21S8SaA2S20S4S2cR8R7A4S20S8SaR6S4bR5R4A2A4A4R3A2S45S42R6S43Z2M1G0A2A2S45S42Z20S46S45S43G1Z2fA2Z1000A2S3aR3R5A2A2A2R4A2A2A3F_;F_;Frho;Fph;Fc;Frk;Fnd;FT;").
Proof. intros T nd rk c ph rho Hc Hph. unfold emeasA. cbn [eda_rank eda_var fst snd]. change (bv_unsigned (eval rho (VB c ph))) with (uval rho (VB c ph)). rewrite (VB_val rho c ph Hc Hph). unfold two47, RA.two47, Lib_scan_double.two47. reflexivity. Qed.

Lemma meas_lit : ltac2:(tb__ "0|1|
S4S2cS8S8SbS1S41Z0R2A2S44R2S43Z2Z40A2M0A2A2S0S8S2dS20S21S4S2cA2S21S8SaA2S20S4S2cR6R5A4S20S8SaR4SdR3A1A4A4R2A2S45S42R4G0A2R3A2A3F_;Frho;Fz;Frk;Fnd;FT;").
Proof. intros T nd rk z rho Hz. unfold emeasA. cbn [eda_rank eda_var fst snd]. change (bv_unsigned (eval rho (SLit z))) with (uval rho (SLit z)). rewrite uval_lit by lia. reflexivity. Qed.

Ltac meas0 := unfold z0; rewrite meas_lit by lia; lia.

Lemma X_E_L : ltac2:(tb__ "0|1|
SbS23S38Q40A1A1M0G0VTR;S35S2bVJAv;S48A1S58R3R2A5VFAM;S2dS20S21S4S2cA2S21S8SaA2S20S4S2cS58S48A4S20S8SaZ32S4bS4aZ13A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre with (P := SPA segs (JAv ndC) E_vrL rho tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_vcall rho E_vrL0 E_vrL tp w E_vrL_eq Hw). }
  apply TR_facts. intros HF.
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc HBX P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_vr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.nd0 PD_vrN NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRES eq_refl
           E_vrL (s_vr E_vrL) R_vrL Xk_op rho tp [] (tv_vec pD pK) [] (bd_op pK) [] ANone (FAM (emeasA (E_vrL0, ndC, (50, VB pC 19)) rho) tp0)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply payA_of_bud_pay. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR HM HT HTK.
    apply (HIN_site E_vrL R_vrL rho ms); [| reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact HF' | exact HP0 | exact Hav | exact HZ].
    intros o Ho. cbn in Ho. unfold is_siteobj. destruct Ho as [<-|[<-|[<-|[]]]]; cbn; auto 10.
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vrN In] in Hd.
    assert (HC : uval rho' pC = uval rho pC /\ uval rho pC <= B32).
    { split.
      - unfold uval. change (eval rho' pC) with (rw rho' 241%positive). change (eval rho pC) with (rw rho 241%positive).
        rewrite (proj1 Hag 241%positive) by (vm_compute; reflexivity). reflexivity.
      - factz HF (SPUle pC pK) H1. factz HF (SPUle pK (SLit B32)) H2. unfold B32 in *. rewrite uval_lit in H2 by lia. lia. }
    destruct HC as [HC1 HC2].
    destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.nd0 ND am_subst app].
    +   rewrite T_keepL0_eq, imp_keepL_tv, imp_keepL_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER TA_Ls ndC (50, VB pC 18) (rho_sub rho' s_keepL)); [innth 2 | assert (ES : sv_subst s_keepL pC = pC) by (vm_compute; reflexivity);
          assert (EC : uval (rho_sub rho' s_keepL) pC = uval rho pC) by (unfold uval at 1; rewrite <- eval_subst, ES; exact HC1);
          rewrite (meas_VB TA_Ls ndC 50 pC 18 (rho_sub rho' s_keepL)) by (rewrite ?EC; unfold B32 in *; lia);
          rewrite (meas_VB E_vrL0 ndC 50 pC 19 rho) by (unfold B32 in *; lia); rewrite EC; unfold B32 in *; pose proof (uval_range rho pC); lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_keepL0 T_keepL tp' w T_keepL_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_keepLs TA_Ls s_keepL (ND (tv_vec pD pK) [] (bd_op pK)) ndC);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity |].
      unfold T_keepLs, ax_add_facts. apply (SPA_refacts_JA segs _ rho' T_keepL ([slot4_at pK] ++ ss_facts (ax_S T_keepL))); [exact Hw1 | vm_compute; reflexivity |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. constructor; [|constructor]. apply (slot4_holds rho' _ pK HF2); vm_compute; reflexivity.
    +   rewrite T_failL0_eq, imp_failL_tv. change (bd_subst _ [] ++ []) with (@nil bitem).
      eapply TR_pre; [|apply (REENTER TF_L ndF (45, z0) (rho_sub rho' s_failL)); [innth 3 | unfold z0; rewrite (meas_VB E_vrL0 ndC 50 pC 19 rho) by (unfold B32 in *; lia); rewrite meas_lit by lia; pose proof (uval_range rho pC); unfold B32 in *; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_failL0 T_failL tp' w T_failL_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_failL TF_L s_failL (ND (tv_vec pD pK) [] []) ndF);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | exact Hw1].
    +   rewrite T_grownL0_eq, imp_grownL_tv, imp_grownL_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER TA_Ls ndC (50, VB pC 18) (rho_sub rho' s_grownL)); [innth 2 | assert (ES : sv_subst s_grownL pC = pC) by (vm_compute; reflexivity);
          assert (EC : uval (rho_sub rho' s_grownL) pC = uval rho pC) by (unfold uval at 1; rewrite <- eval_subst, ES; exact HC1);
          rewrite (meas_VB TA_Ls ndC 50 pC 18 (rho_sub rho' s_grownL)) by (rewrite ?EC; unfold B32 in *; lia);
          rewrite (meas_VB E_vrL0 ndC 50 pC 19 rho) by (unfold B32 in *; lia); rewrite EC; unfold B32 in *; pose proof (uval_range rho pC); lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_grownL0 T_grownL tp' w T_grownL_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_grownLs TA_Ls s_grownL (ND (tv_vec vDgL vKgL) [] (bd_op vKgL)) ndC);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity |].
      unfold T_grownLs, ax_add_facts. apply (SPA_refacts_JA segs _ rho' T_grownL ([slot4_at vKgL] ++ ss_facts (ax_S T_grownL))); [exact Hw1 | vm_compute; reflexivity |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. constructor; [|constructor]. apply (slot4_holds rho' _ vKgL HF2); vm_compute; reflexivity.
Qed.

Lemma X_E_2v : ltac2:(tb__ "0|1|
SbS23S38Q40A1A1M0G0VTR;S35S2bVJAv;S48A1S57R3R2A5VFAM;S2dS20S21S4S2cA2S21S8SaA2S20S4S2cS57S48A4S20S8SaZ23S5eA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre with (P := SPA segs (JAv ndC) E_2v rho tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_vcall rho E_2v0 E_2v tp w E_2v_eq Hw). }
  apply TR_facts. intros HF.
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc HBX P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_vr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.nd0 PD_vrN NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRES eq_refl
           E_2v (s_vr E_2v) R_2v Xk_op rho tp [] (tv_vec pD pK) [] (bd_op pK) [] ANone (FAM (emeasA (E_2v0, ndC, (35, z0)) rho) tp0)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply payA_of_bud_pay. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR HM HT HTK.
    apply (HIN_site E_2v R_2v rho ms); [| reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact HF' | exact HP0 | exact Hav | exact HZ].
    intros o Ho. cbn in Ho. unfold is_siteobj. destruct Ho as [<-|[<-|[<-|[]]]]; cbn; auto 10.
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vrN In] in Hd.
    assert (HC : uval rho' pC = uval rho pC /\ uval rho pC <= B32).
    { split.
      - unfold uval. change (eval rho' pC) with (rw rho' 241%positive). change (eval rho pC) with (rw rho 241%positive).
        rewrite (proj1 Hag 241%positive) by (vm_compute; reflexivity). reflexivity.
      - factz HF (SPUle pC pK) H1. factz HF (SPUle pK (SLit B32)) H2. unfold B32 in *. rewrite uval_lit in H2 by lia. lia. }
    destruct HC as [HC1 HC2].
    destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.nd0 ND am_subst app].
    +   rewrite T_keep2v0_eq, imp_keep2v_tv, imp_keep2v_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER (TA_2s vVALS) ndC (30, SLit (10 + 4 * CM)) (rho_sub rho' s_keep2v)); [innth 6 | unfold z0; rewrite !meas_lit by (unfold CM; lia); unfold CM; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_keep2v0 T_keep2v tp' w T_keep2v_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_keep2vs (TA_2s vVALS) s_keep2v (ND (tv_vec pD pK) [] (bd_op pK)) ndC);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity |].
      unfold T_keep2vs, ax_add_facts. apply (SPA_refacts_JA segs _ rho' T_keep2v ([slot4_at pK] ++ ss_facts (ax_S T_keep2v))); [exact Hw1 | vm_compute; reflexivity |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. constructor; [|constructor]. apply (slot4_holds rho' _ pK HF2); vm_compute; reflexivity.
    +   rewrite T_fail2v0_eq, imp_fail2v_tv. change (bd_subst _ [] ++ []) with (@nil bitem).
      eapply TR_pre; [|apply (REENTER TF_2 ndF (30, z0) (rho_sub rho' s_fail2v)); [innth 8 | unfold z0; rewrite !meas_lit by (unfold CM; lia); unfold CM; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_fail2v0 T_fail2v tp' w T_fail2v_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_fail2v TF_2 s_fail2v (ND (tv_vec pD pK) [] []) ndF);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | exact Hw1].
    +   rewrite T_grown2v0_eq, imp_grown2v_tv, imp_grown2v_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER (TA_2s vVALS) ndC (30, SLit (10 + 4 * CM)) (rho_sub rho' s_grown2v)); [innth 6 | unfold z0; rewrite !meas_lit by (unfold CM; lia); unfold CM; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_grown2v0 T_grown2v tp' w T_grown2v_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_grown2vs (TA_2s vVALS) s_grown2v (ND (tv_vec vDg2v vKg2v) [] (bd_op vKg2v)) ndC);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity |].
      unfold T_grown2vs, ax_add_facts. apply (SPA_refacts_JA segs _ rho' T_grown2v ([slot4_at vKg2v] ++ ss_facts (ax_S T_grown2v))); [exact Hw1 | vm_compute; reflexivity |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. constructor; [|constructor]. apply (slot4_holds rho' _ vKg2v HF2); vm_compute; reflexivity.
Qed.

Lemma X_E_2d : ltac2:(tb__ "0|1|
SbS23S38Q40A1A1M0G0VTR;S35S2bVJAv;S48A1S56R3R2A5VFAM;S2dS20S21S4S2cA2S21S8SaA2S20S4S2cS56S48A4S20S8SaZ23S5eA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre with (P := SPA segs (JAv ndC) E_2d rho tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_vcall rho E_2d0 E_2d tp w E_2d_eq Hw). }
  apply TR_facts. intros HF.
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc HBX P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_vr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.nd0 PD_vrN NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRES eq_refl
           E_2d (s_vr E_2d) R_2d Xk_op rho tp [] (tv_vec pD pK) [] (bd_op pK) [] ANone (FAM (emeasA (E_2d0, ndC, (35, z0)) rho) tp0)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply payA_of_bud_pay. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR HM HT HTK.
    apply (HIN_site E_2d R_2d rho ms); [| reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact HF' | exact HP0 | exact Hav | exact HZ].
    intros o Ho. cbn in Ho. unfold is_siteobj. destruct Ho as [<-|[<-|[<-|[]]]]; cbn; auto 10.
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vrN In] in Hd.
    assert (HC : uval rho' pC = uval rho pC /\ uval rho pC <= B32).
    { split.
      - unfold uval. change (eval rho' pC) with (rw rho' 241%positive). change (eval rho pC) with (rw rho 241%positive).
        rewrite (proj1 Hag 241%positive) by (vm_compute; reflexivity). reflexivity.
      - factz HF (SPUle pC pK) H1. factz HF (SPUle pK (SLit B32)) H2. unfold B32 in *. rewrite uval_lit in H2 by lia. lia. }
    destruct HC as [HC1 HC2].
    destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.nd0 ND am_subst app].
    +   rewrite T_keep2d0_eq, imp_keep2d_tv, imp_keep2d_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER (TA_2s vDEF) ndC (30, SLit (10 + 4 * CM)) (rho_sub rho' s_keep2d)); [innth 7 | unfold z0; rewrite !meas_lit by (unfold CM; lia); unfold CM; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_keep2d0 T_keep2d tp' w T_keep2d_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_keep2ds (TA_2s vDEF) s_keep2d (ND (tv_vec pD pK) [] (bd_op pK)) ndC);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity |].
      unfold T_keep2ds, ax_add_facts. apply (SPA_refacts_JA segs _ rho' T_keep2d ([slot4_at pK] ++ ss_facts (ax_S T_keep2d))); [exact Hw1 | vm_compute; reflexivity |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. constructor; [|constructor]. apply (slot4_holds rho' _ pK HF2); vm_compute; reflexivity.
    +   rewrite T_fail2d0_eq, imp_fail2d_tv. change (bd_subst _ [] ++ []) with (@nil bitem).
      eapply TR_pre; [|apply (REENTER TF_2 ndF (30, z0) (rho_sub rho' s_fail2d)); [innth 8 | unfold z0; rewrite !meas_lit by (unfold CM; lia); unfold CM; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_fail2d0 T_fail2d tp' w T_fail2d_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_fail2d TF_2 s_fail2d (ND (tv_vec pD pK) [] []) ndF);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | exact Hw1].
    +   rewrite T_grown2d0_eq, imp_grown2d_tv, imp_grown2d_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER (TA_2s vDEF) ndC (30, SLit (10 + 4 * CM)) (rho_sub rho' s_grown2d)); [innth 7 | unfold z0; rewrite !meas_lit by (unfold CM; lia); unfold CM; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_grown2d0 T_grown2d tp' w T_grown2d_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_grown2ds (TA_2s vDEF) s_grown2d (ND (tv_vec vDg2d vKg2d) [] (bd_op vKg2d)) ndC);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity |].
      unfold T_grown2ds, ax_add_facts. apply (SPA_refacts_JA segs _ rho' T_grown2d ([slot4_at vKg2d] ++ ss_facts (ax_S T_grown2d))); [exact Hw1 | vm_compute; reflexivity |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. constructor; [|constructor]. apply (slot4_holds rho' _ vKg2d HF2); vm_compute; reflexivity.
Qed.

Lemma X_Lin : ltac2:(tb__ "0|3|
S4S4S8fSbS23S38Q40A1A1M0S8G0S0S4Sa1S25S9S5cS7aA1S26S9A1A3M1R7A2R6A3S0S22S6fS9SfS1aS17S9cS15S9aS7aSdS4dA1A3S54A3A1A1SeS5R8A1A1A3S24A3S0S22S6fS9SfScS7aS7bA2A1SeS5R9A1A1A3S24A3S0S22S6fS9SfScS7bSdS79A1A2A1SeS5RaA1A1A3S24A3S0S22S87SeS5RbA1A1A1S24A3S0S22S71S9S18S10S5RcA1M2A1A1S27S9G1SeG2A1A3A3S24A3S0S22S6RcS55RbA3S24A3S0S22S90RcS6eA2S24A3S0S22Sb0S6eS10S5ReA1A1A2S24A3S0S22S30S10S5RfA1A1S4cA2S24A3S0S22Sa3RfS6dS97S50S49A2A3S24A3S0S22S3cSeS5R11A1A1S3bR10S53S49A1A2S53S7bA1A3S24A3S41S42Z33S43Z2Z40A2A2ReA2VTR;S35S2bVJAv;S4cA1R14R11R10A5VFAM;RfReA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fs;FXf;FX;").
Proof.
  intros X Xf s rho tp b tp0 HXf Hdiv HCK HKB HB Hfb He Hid Hnf Hnb Htv Hle Hb. apply TR_facts. intros HF.
  pose proof (baseOz_of rho _ HF HB) as [_ _ _ Bvidx].
  pose proof (holds_mem _ _ _ HF Hdiv) as H1. apply (proj1 (holds_nbgeu _ _ _)) in H1. change (bv_unsigned (eval rho vVIDX)) with (uval rho vVIDX) in H1.
  change (bv_unsigned (eval rho (SMd M_DIVU vC (SLit CM)))) with (uval rho (SMd M_DIVU vC (SLit CM))) in H1. rewrite uval_divu_lit in H1 by (unfold CM; lia).
  pose proof (holds_mem _ _ _ HF HCK) as H2. pose proof (holds_mem _ _ _ HF HKB) as H3. rewrite h_ule in H2, H3. unfold B32 in H3. rewrite uval_lit in H3 by lia.
  assert (HIN : holds rho (inL_at vC)).
  { unfold inL_at. apply (proj2 (h_ule _ _ _)). rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia.
    rewrite uval_mul_lit by (unfold CM; lia). unfold CM in *. pose proof (Z.mul_div_le (uval rho vC) CM). nia. }
  eapply TR_pre; [|apply (REENTER C_L ndC (50, VB pC 20) (rho_sub rho s)); [innth 1 |]].
  - intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc Xf C_L s nd0 ndC);
      [exact He | exact Hid | exact Hnf | exact Hnb | exact Htv | reflexivity | exact Hle | reflexivity |].
    rewrite <- HXf. unfold ax_add_facts. apply (SPA_refacts_JA segs _ rho X ([inL_at vC] ++ ss_facts (ax_S X))); [exact Hw | exact Hfb | intros tr md _ HF2; apply Forall_app; split; [constructor; [exact HIN | constructor] | exact HF2]].
  - unfold emeasA. cbn [eda_rank eda_var fst snd]. pose proof (U_range (eval (rho_sub rho s) (VB pC 20))). unfold M64v in *. lia.
Qed.
Lemma X_X_Lin0 : ltac2:(tb__ "0|1|
SbS23S38Q40A1A1M0S8G0S41S42Z33S43Z2Z40A2A2R2A2VTR;S35S2bVJAv;S4cA1S65R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof. intros rho tp b tp0 Hb. apply (X_Lin X_Lin0 X_Lin0f s_Lin0); [reflexivity | vm_compute; reflexivity .. | exact Hb]. Qed.
Lemma X_X_Lin1 : ltac2:(tb__ "0|1|
SbS23S38Q40A1A1M0S8G0S41S42Z33S43Z2Z40A2A2R2A2VTR;S35S2bVJAv;S4cA1S66R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof. intros rho tp b tp0 Hb. apply (X_Lin X_Lin1 X_Lin1f s_Lin1); [reflexivity | vm_compute; reflexivity .. | exact Hb]. Qed.

Lemma X_back : ltac2:(tb__ "0|5|
S4S4S8fSbS23S38Q40A1A1M0S8G0S0S4Sa1S25S9S5cS4eA1S26S9A1A3M1R7A2R6A3S0S22S6fS9SfS17S9dS15S9aS4eSdS4dA1A3S54A3A1SeS5R8A1A1A3S24A3S0S22S6fS9SfScS4eS49A2A1SeS5R9A1A1A3S24A3S0S22S6fS9SfScS49SdS79A1A2A1SeS5RaA1A1A3S24A3S0S22S6fS9SfScS4aS49A2A1SeS5RbA1A1A3S24A3S0S22S87SeS5RcA1A1A1S24A3S0S22S71S9S18S10S5RdA1M2A1A1S27S9G1SeG2A1A3A3S24A3S0S22S6RdS55RcA3S24A3S0S22S90RdS6eA2S24A3S0S22Sb0S6eS10S5RfA1A1A2S24A3S0S22S30S10S5R10A1A1S48A2S24A3S0S22Sa3R10S97S50S49A2M3G3A3S24A3S0S22S3cSeS5R12A1A1S3bR11S53S49A1M4A2G4A3S24A3S0SaS91R12S4aA2S4eA3S41S2dS20S21S4S2cA2S21S8SaA2S20S4S2cR15S48A4S20S8SaZ32S4bS4aZ0A2A4A4R12A2R10A2VTR;S35S2bVJAv;S48A1R16R13R12A5VFAM;R11R10A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fs;FXf;FX;").
Proof.
  intros X Xf s rho tp b tp0 HXf Hdiv HCK HKB HCK0 HB Hfb He Hid Hnf Hnb Htv Hle Hs Hb. apply TR_facts. intros HF.
  pose proof (baseOz_of rho _ HF HB) as [_ _ _ Bvidx].
  pose proof (holds_mem _ _ _ HF Hdiv) as H1. apply (proj1 (holds_bltu _ _ _)) in H1. change (bv_unsigned (eval rho vVIDX)) with (uval rho vVIDX) in H1.
  change (bv_unsigned (eval rho (SMd M_DIVU pCM (SLit CM)))) with (uval rho (SMd M_DIVU pCM (SLit CM))) in H1. rewrite uval_divu_lit in H1 by (unfold CM; lia).
  pose proof (holds_mem _ _ _ HF HCK) as H2. pose proof (holds_mem _ _ _ HF HKB) as H3. pose proof (holds_mem _ _ _ HF HCK0) as H4.
  rewrite h_ule in H2, H3, H4. unfold B32 in H3. rewrite uval_lit in H3 by lia.
  pose proof (uval_range rho pC) as RC.
  assert (ECM : uval rho pCM = uval rho pC + CM).
  { unfold pCM, CM in *. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity. }
  assert (HIN : holds rho (inL_at pCM)).
  { unfold inL_at. apply (proj2 (h_ule _ _ _)). rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia.
    rewrite uval_mul_lit by (unfold CM; lia). unfold CM in *. pose proof (Z.mul_div_le (uval rho pCM) CM). nia. }
  eapply TR_pre; [|apply (REENTER C_L ndC (50, VB pC 20) (rho_sub rho s)); [innth 1 |]].
  - intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc Xf C_L s ndC ndC);
      [exact He | exact Hid | exact Hnf | exact Hnb | exact Htv | reflexivity | exact Hle | reflexivity |].
    rewrite <- HXf. unfold ax_add_facts. apply (SPA_refacts_JA segs _ rho X ([inL_at pCM] ++ ss_facts (ax_S X))); [exact Hw | exact Hfb | intros tr md _ HF2; apply Forall_app; split; [constructor; [exact HIN | constructor] | exact HF2]].
  - rewrite (meas_VB X ndC 50 pC 0 rho) in Hb by (unfold B32 in *; lia).
    assert (EC : uval (rho_sub rho s) pC = uval rho pCM).
    { unfold uval. rewrite <- eval_subst, Hs. reflexivity. }
    rewrite (meas_VB C_L ndC 50 pC 20 (rho_sub rho s)) by (rewrite ?EC; unfold B32 in *; lia). rewrite EC, ECM. unfold CM in *. lia.
Qed.
Lemma X_X_back0 : ltac2:(tb__ "0|1|
SbS23S38Q40A1A1M0G0VTR;S35S2bVJAv;S48A1S5aR3R2A5VFAM;S2dS20S21S4S2cA2S21S8SaA2S20S4S2cS5aS48A4S20S8SaZ32S4bS4aZ0A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0. apply (X_back X_back0 X_back0f s_back0); [reflexivity | vm_compute; reflexivity .. | lia]. Qed.
Lemma X_X_back1 : ltac2:(tb__ "0|1|
SbS23S38Q40A1A1M0G0VTR;S35S2bVJAv;S48A1S5bR3R2A5VFAM;S2dS20S21S4S2cA2S21S8SaA2S20S4S2cS5bS48A4S20S8SaZ32S4bS4aZ0A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0. apply (X_back X_back1 X_back1f s_back1); [reflexivity | vm_compute; reflexivity .. | lia]. Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S4S2cS21S8SaA2M0SbS23S38Q40A1A1M1G1S70S21S21S4S2cA2M2G0A2S20G2G0S20S4S2cR6R5A4R4A4S69A3VTR;S35S2bVJAv;R6A1R7R4R3A5VFAM;S2dS20G2G0S20S4S2cR7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsO] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]; injection H as <- <- <-.
  - apply X_X_Lin0. meas0.
  - apply X_X_Lin1. meas0.
  - apply X_E_L.
  - apply X_X_back0.
  - apply X_X_back1.
  - apply X_E_2v.
  - apply X_E_2d.
  - apply POST. left. reflexivity.
  - apply POST. right. left. reflexivity.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S34S2bVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
SacS2bSabVAInv;VCST;VXGL;A5").

Theorem opt_push1_sum : ltac2:(tb__ "0|0|
S23S38Q40A1A1S83S2bVok;S35S2bS2fVAInv;VCST;VXGL;VKc;S77VFB;VFF;A2VFB;VFF;VBX;S2eS4cAaS59Vrho0;R1A5S73S2bS6eVrho0;R1S86A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc ALA FUEL_op cutpcs_all 100
                (map edropA cutsO) (map edropA exitsO) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertO_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0' & Hin). cbn in E0'. injection E0' as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsO)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (call_soundPA3 segs ok))
         with (rvX := rv) (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HBXc. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Lib_vec_reserveN_pf.vec_reserveN_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HBXc rho1 ok Hok AC tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue ok (map edropA cutsO) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_op FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_op P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
SadS2bSabVAInv;VCST;VXGL;A5").

Theorem opt_push1_sum_ex : ltac2:(tb__ "0|0|
S23S38Q40A1A1S82S2bS35S2bS2fVAInv;VCST;VXGL;VKc;S77VFB;VFF;A2VFB;VFF;VBX;S2eS4cAaS59Vrho0;R1A5S73S2bS6eVrho0;R1S86A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc ALA FUEL_op cutpcs_all 100 cutsO exitsO (Q tp0) ejcertO_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue) cutsO) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HBXc. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Lib_vec_reserveN_pf.vec_reserveN_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HBXc rho1 ACX tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue cutsO T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_op FB FF) FB FF BX PTrue rho0 tp0 nd Posts_op P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_opt_push1_pf.

(* [comment removed for export] *)
Module Lib_opt_push3_eqs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_opt_push3"; "s_vr"; "E_2d"; "E_2v"; "E_vrL"; "Xk_op"; "pK"; "xf_vback"; "bd_op"; "pD"; "R_2d"; "R_2v"; "R_vrL"; "xf_vcall"; "T_fail2d0"; "T_fail2v0"; "T_failL0"; "T_grown2d0"; "T_grown2v0"; "T_grownL0"; "T_keep2d0"; "T_keep2v0"; "T_keepL0"; "vKg2d"; "vKg2v"; "vKgL"; "E_2d0"; "E_2v0"; "E_vrL0"; "FUEL_op"; "T_fail2d"; "T_fail2v"; "T_failL"; "T_grown2d"; "T_grown2v"; "T_grownL"; "T_keep2d"; "T_keep2v"; "T_keepL"; "cutpcs_all"; "cutsO"; "exitsO"; "vDg2d"; "vDg2v"; "vDgL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN"; "Pre_vr"; "P_grown"; "P_keep"; "P_fail"; "bdP"; "tv0"; "vN"; "tvP"; "vK"; "vKn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "@Corelib.Init.Datatypes"; "list"; "Some"; "option"; "prod"; "bool"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "import_subA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "tv_vec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "import_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "T_afterA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bd_subst"; "bitem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ejcertA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_opt_push3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_opt_push3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRNAddr RA.ReallocAddr OPAddr.

Lemma ejcertO_ok : ltac2:(tb__ "0|0|
S0S3dS48S46S47S1eS28P64S29S2aA7S3eA3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma E_vrL_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S1dSeA2S3aS1S5A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_2v_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S1cSeA2S3aS1S4A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E_2d_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S1bSeA2S3aS1S3A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keepL0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS5S2S5A1SdS30S6A6S17A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_failL0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS5S2S5A1SdS31S6A6S11A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grownL0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS5S2S5A1SdS2fS6A6S14A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep2v0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS4S2S4A1ScS30S6A6S16A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail2v0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS4S2S4A1ScS31S6A6S10A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown2v0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS4S2S4A1ScS2fS6A6S13A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep2d0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS3S2S3A1SbS30S6A6S15A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail2d0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS3S2S3A1SbS31S6A6SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown2d0_eq : ltac2:(tb__ "0|0|
S0S1S43S2eS3S2S3A1SbS2fS6A6S12A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keepL_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S17S8A2S3aS1S27A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_failL_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S11S8A2S3aS1S21A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grownL_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S14S8A2S3aS1S24A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep2v_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S16S8A2S3aS1S26A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail2v_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S10S8A2S3aS1S20A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown2v_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S13S8A2S3aS1S23A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_keep2d_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S15S8A2S3aS1S25A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_fail2d_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40SfS8A2S3aS1S1fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma T_grown2d_eq : ltac2:(tb__ "0|0|
S0S3bS1A1S40S12S8A2S3aS1S22A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma imp_keepL_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S5A1S2eS30S5A4S33A2S41SaS7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keepL_bd : ltac2:(tb__ "0|0|
S0S39S45A1S44S3fS2S5A1S2eS30S5A4S32S34S36A2A2S9S7A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_failL_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S5A1S2eS31S5A4S33A2S41SaS7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grownL_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S5A1S2eS2fS5A4S35A2S41S2dS1aA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grownL_bd : ltac2:(tb__ "0|0|
S0S39S45A1S44S3fS2S5A1S2eS2fS5A4S32S34S37A2A2S9S1aA1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep2v_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S4A1S2eS30S4A4S33A2S41SaS7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep2v_bd : ltac2:(tb__ "0|0|
S0S39S45A1S44S3fS2S4A1S2eS30S4A4S32S34S36A2A2S9S7A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail2v_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S4A1S2eS31S4A4S33A2S41SaS7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown2v_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S4A1S2eS2fS4A4S35A2S41S2cS19A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown2v_bd : ltac2:(tb__ "0|0|
S0S39S45A1S44S3fS2S4A1S2eS2fS4A4S32S34S37A2A2S9S19A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep2d_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S3A1S2eS30S3A4S33A2S41SaS7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_keep2d_bd : ltac2:(tb__ "0|0|
S0S39S45A1S44S3fS2S3A1S2eS30S3A4S32S34S36A2A2S9S7A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_fail2d_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S3A1S2eS31S3A4S33A2S41SaS7A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown2d_tv : ltac2:(tb__ "0|0|
S0S39S3cS38S38A2A1S42S3fS2S3A1S2eS2fS3A4S35A2S41S2bS18A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma imp_grown2d_bd : ltac2:(tb__ "0|0|
S0S39S45A1S44S3fS2S3A1S2eS2fS3A4S32S34S37A2A2S9S18A1A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
End Lib_opt_push3_eqs.

(* [comment removed for export] *)
Module Lib_opt_push3_pf.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "ax_X"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "sv"; "valuation"; "SPUle"; "SLit"; "ss_facts"; "sprop_eqb"; "ss_next"; "sobj"; "holds"; "SVar"; "rw"; "SMd"; "SAlu"; "SPBranch"; "sprop_below"; "DUnknown"; "SPNot"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "odefault"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "bool"; "list"; "true"; "cons"; "nil"; "app"; "Some"; "fst"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "emeasA"; "PTrue"; "JA_pre"; "nd_below"; "JA"; "JLA"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "smatchA"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "bd_subst"; "bud_le"; "BXok_d"; "bd_wpos"; "bitem"; "bxt"; "@Stdlib.ZArith.BinInt.Z"; "le"; "mul"; "pow"; "lt"; "add"; "sub"; "div"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_opt_push3"; "ndC"; "pK"; "pC"; "VB"; "nd0"; "CM"; "pCM"; "s_vr"; "pD"; "vDEF"; "vVALS"; "bd_op"; "vVIDX"; "C_L"; "E_2d0"; "E_2v0"; "E_vrL0"; "Pre_op"; "X_back0"; "X_back1"; "inL_at"; "vALo"; "z0"; "O_deflt"; "O_vals"; "PD_op"; "PD_vrN"; "P_op0"; "P_op1"; "X_Lin0"; "X_Lin1"; "Xk_op"; "cutsO"; "exitsO"; "nd0'"; "nd1"; "slot4_at"; "tv0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Stdlib.Lists.List"; "existsb"; "In"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "LQPA"; "J_ofPA"; "call_checkPA"; "entails_frA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ei.Lib_opt_push3_pf"; "P0_op"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA"; "infrFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN"; "B32"; "vC"; "vK"; "spm"; "vV"; "Pre_vr"; "nd0"; "two47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ei.Lib_opt_push3_pf.Sum"; "Posts_op"; "baseOF"; "JLo"; "baseOz"; "base_factsO"; "is_siteobj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub_get"; "wsub"; "wsub_id_below"; "sv_subst"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs"; "tv_vec"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.Riscv.Instr"; "M_DIVU"; "ALU_ADD"; "BC_GEU"; "BC_LTU"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Lib_vec_reserveN_pf"; "P0_vr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "call_linkP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_sub_eqb"; "tvz"; "FBx";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC"; "PostsC"; "FFx"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "AE_A"; "alloc_contractsA"; "alloc_contractsA_ex"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "payA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA SummaryA3 TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Code Lib_scan_double.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ec.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require ee.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Lib_opt_push3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Lib_vec_reserveN_pf OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ee.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Lib_opt_push3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ei.Lib_opt_push3_eqs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import VRNAddr RA.ReallocAddr OPAddr.
Local Open Scope lazy_bool_scope.

Definition P0_op (FB : list (Z * Z)) (FF : list (Z * Z * Z)) (r : valuation) : Prop := ltac2:(tb__ "0|2|
S1S78VFF;S39Q40M0S14Vr;PcA2A2Z20A3S1S78VFF;S39G0S14Vr;P24A2A2Z30A3S1S78VFF;S39G0S14Vr;P21A2A2S42Z4S4dA2M1A3S78VFF;S39G0S14Vr;P22A2A2G1A3A2A2A2").

Lemma uval_divu_lit : ltac2:(tb__ "0|0|
SbSaS8S1S44Z0R1A2S44R1S43Z2Z40A2A2A2S0S8S3aR4S15S9aR3SdR2A1A3A2S47S3aR4R3A2R2A2A3F_;Fc;Fa;Frho;").
Proof.
  intros rho a c Hc. unfold uval. cbn [eval]. unfold mul_div.
  rewrite Z_to_bv_unsigned. rewrite bv_wrap_small by (unfold bv_modulus; cbn; lia).
  destruct (Z.eqb_spec c 0) as [E|E]; [lia|]. rewrite bv_divu_unsigned. rewrite Z_to_bv_unsigned. rewrite bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

Lemma VB_val : ltac2:(tb__ "0|0|
SbSaS8S41S3aR3R2A2S79A2S1S41Z0R2A2S44R2Z40A2A2S0S8S3aR5S4bR4R3A2A2S45S42Z20S46S45S43Z2Z2fA2Z1000A2S3aR5R4A2A2A2R3A2A3F_;F_;Fph;Fc;Frho;").
Proof.
  intros rho c ph Hc Hph. unfold VB, two47, RA.two47, Lib_scan_double.two47, B32 in *. pose proof (uval_range rho c) as Rc.
  assert (ES : uval rho (SAlu ALU_SUB (SLit (2 ^ 47 + 4096)) c) = 2 ^ 47 + 4096 - uval rho c).
  { unfold uval in *. rewrite U_sub, U_lit. unfold M64v. rewrite (Z.mod_small (2 ^ 47 + 4096)) by lia. apply Z.mod_small. lia. }
  assert (EM : uval rho (SMd M_MUL (SLit 32) (SAlu ALU_SUB (SLit (2 ^ 47 + 4096)) c)) = 32 * (2 ^ 47 + 4096 - uval rho c)).
  { rewrite uval_mul_lit by (rewrite ?ES; lia). rewrite ES. reflexivity. }
  rewrite uval_add_small by (rewrite EM, uval_lit by lia; lia). rewrite EM, uval_lit by lia. lia.
Qed.

Section Sum.
Variable AInv : ltac2:(tb__ "0|0|
Sb4SbS23S38Q40A1A1S95OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
SaeS2bVAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S8SafVCST;R1A2S1S41Z0R2A2S44R2SaaA2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S8SafVXGL;R1A2S1S41Z0R2A2S44R2SaaA2A2F_;Fa;").
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S23S21S21S8S8A2S8A2A1").
Variable BX : bxt.
Hypothesis HBX : BXok_d 4 BX.
Variable rho0 : valuation.

Definition JLo (nd : ndesc) : jpostA := ltac2:(tb__ "0|0|
S32VAInv;VCST;VXGL;VKc;S77VFB;VFF;A2VFB;VFF;VBX;S2eVnd;Aa").
Definition Posts_op : list (axst * jpostA) := ltac2:(tb__ "0|1|
S25S21S4S72A2M0S20S4S72S64S88S6bA1A4S25G0S20S4S72S63S88S6aA1A4S26G0A1A3A3").
Lemma Posts_op_PD : ltac2:(tb__ "0|0|
S0S23S21S4S72A2A1S86Sa6VAInv;VCST;VXGL;VKc;S77S2eS61VFB;VFF;VBX;AaA3").
Proof. reflexivity. Qed.

Let JAv (nd : ndesc) : jpredA := ltac2:(tb__ "0|0|
S31VAInv;VCST;VXGL;S6eVKc;Vrho0;S77VFB;VFF;A2VFB;VFF;VBX;S2eVnd;Ac").
Let nI : ltac2:(tb__ "0|0|
S21S4S2cA2Sa2Fn;") := ltac2:(tb__ "0|0|
S33VAInv;VCST;VXGL;S6eVKc;Vrho0;S77VFB;VFF;A2VFB;VFF;VBX;S2eAb").
Let Q (tp0 : list word) : assn := ltac2:(tb__ "0|0|
S73S2bS6eVrho0;Vtp0;S86A5").

Definition base_factsO : list sprop := ltac2:(tb__ "0|5|
S25S9ScS13PaA1M0SdS80A1M1A2S25S9ScS13P1eA1M2S7cZ80A1A2S25S9ScSdZ1000A1M3S52A2S25S9ScS16S9bS52SdS42Z4S4dA2A1M4A3G2A2S25S9ScS52G1A2S25S9ScG3S51A2S25S9ScS16S9bS51G4A3G2A2S25S9ScS51G1A2S25S9ScS54SdS43Z2Z1bA2A1A2S25S9ScG2G0A2S25S9ScSdZ7fff7f800000A1G2A2S25S9ScG2SdZ7fffff800000A1A2S26S9A1A3A3A3A3A3A3A3A3A3A3A3A3").
Definition baseOF (F : list sprop) : bool := ltac2:(tb__ "0|0|
S71S9S9S6fS9SfR1A1VF;A3Lp;S8aA3").
Record baseOz (rho : valuation) : Prop := BZO {
  bz_sp : aceil + 128 <= uval rho (SVar 10) <= 2 ^ 47;
  bz_vals : 4096 <= uval rho vVALS /\ uval rho vVALS + 4 * CM <= bv_unsigned (rw rho V_TOP);
  bz_def : 4096 <= uval rho vDEF /\ uval rho vDEF + 4 * CM <= bv_unsigned (rw rho V_TOP);
  bz_vidx : uval rho vVIDX <= 2 ^ 27;

  bz_top : bv_unsigned (rw rho V_TOP) + 128 <= uval rho (SVar 10) /\ 140735332483072 <= bv_unsigned (rw rho V_TOP) <= 140737479966720 }.
Lemma uval_spm : ltac2:(tb__ "0|1|
SbS8S1S41Z0R1A2S41R1S3aR2S13PaA1M0A2A2A2S0S8S3aR3S7cR2A1A2S46S3aR3G0A2R2A2A3F_;Fk;Frho;").
Proof.
  intros rho k Hk. unfold spm, RA.spm, uval in *. rewrite U_add, U_lit. pose proof (U_range (eval rho (SVar 10))) as R. unfold M64v in *.
  set (x := bv_unsigned (eval rho (SVar 10))) in *.
  rewrite Zplus_mod_idemp_r. replace (x + - k) with (x - k) by lia. apply Z.mod_small. lia.
Qed.
Lemma baseOz_of : ltac2:(tb__ "0|0|
SbS23S9A1S92S9S12R2A1R1A3S0S22S87R2A1S24A3S89R4A1F_;F_;FF;Frho;").
Proof.
  intros rho F HF HB. unfold baseOF in HB.
  assert (G : forall p, In p base_factsO -> holds rho p).
  { intros p Hp. apply (holds_mem rho F p HF). exact (proj1 (forallb_forall _ _) HB p Hp). }
  cbn [base_factsO] in G.
  pose proof (G _ ltac:(left; reflexivity)) as F1. pose proof (G _ ltac:(do 1 right; left; reflexivity)) as F2.
  pose proof (G _ ltac:(do 2 right; left; reflexivity)) as F3. pose proof (G _ ltac:(do 3 right; left; reflexivity)) as F4.
  pose proof (G _ ltac:(do 4 right; left; reflexivity)) as F5. pose proof (G _ ltac:(do 5 right; left; reflexivity)) as F6.
  pose proof (G _ ltac:(do 6 right; left; reflexivity)) as F7. pose proof (G _ ltac:(do 7 right; left; reflexivity)) as F8.
  pose proof (G _ ltac:(do 8 right; left; reflexivity)) as F9. pose proof (G _ ltac:(do 9 right; left; reflexivity)) as F10.
  pose proof (G _ ltac:(do 10 right; left; reflexivity)) as F11. pose proof (G _ ltac:(do 11 right; left; reflexivity)) as F12.
  rewrite h_ule in F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12.
  change (uval rho (SVar 30)) with (bv_unsigned (rw rho V_TOP)) in *.
  unfold two47, RA.two47, Lib_scan_double.two47, CM in *. rewrite !uval_lit in F1, F3, F5, F6, F8, F9, F11, F12 by lia.
  pose proof (uval_range rho vVALS). pose proof (uval_range rho vDEF).
  rewrite uval_add_small in F4 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F4 by lia.
  rewrite uval_add_small in F7 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F7 by lia.
  rewrite uval_spm in F2 by lia.
  constructor; rewrite ?aceil_val; unfold CM; lia.
Qed.

Lemma P0o_now : ltac2:(tb__ "0|1|
SbS9fS6eVrho0;R1A3S77VFB;VFF;Vrho0;A3S1S78VFF;S3aR3S7dA2Z20A3S1S78VFF;S3aR3S5dA2Z30A3S1S78VFF;S3aR3S52A2S42Z4S4dA2M0A3S78VFF;S3aR3S51A2G0A3A2A2A2F_;F_;Frho;").
Proof.
  intros rho Hav (A & B & C & D). unfold uval, vV, OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.vV, vALo, vVALS, vDEF. cbn [eval].
  rewrite <- (proj1 Hav 12%positive eq_refl), <- (proj1 Hav 36%positive eq_refl), <- (proj1 Hav 33%positive eq_refl), <- (proj1 Hav 34%positive eq_refl).
  auto.
Qed.

Lemma tvz_kd : ltac2:(tb__ "0|1|
SbSaSaSa4R3S97R2R1A2A2S41S3aR4R2A2S79A2S2S0S8S3aR5R3A2Z0M0A3A1S2S0S8S3aR6R5A2G0A3A1F_;F_;F_;Fk;Fd;Frho;").
Proof.
  intros rho d k HZ HK Hk Hd. apply Forall_inv in HZ. unfold tnz, tvv in HZ. cbn [fst snd] in HZ. unfold uval in Hd, Hk, HK.
  specialize (HZ ltac:(intros H; exact (H Hd))). unfold B32 in HK.
  pose proof (uval_mul_lit rho 4 k ltac:(lia) ltac:(unfold uval; lia)) as E4. unfold uval, kb4 in E4. unfold kb4 in HZ. rewrite E4 in HZ. lia.
Qed.

Definition is_siteobj (o : sobj) : Prop := ltac2:(tb__ "0|0|
S3S1S0SaS1bVo;A1S13PaA1A3S1S0SaS1eVo;A1SdN80A1A3S1S0SaS1dVo;A1SdZ0A1A3S0S1fS1cVo;A1S19A3A2A2A2S3S0S11Vo;S60A3S0S11Vo;S5fA3A2A2").
Lemma HIN_site : ltac2:(tb__ "0|2|
S4S23S11A1SbS94S11S70S11R1R4A3S8bR2A1F_;Fo;S0SaS8eS4fR5A1P11A2S49A3S0SaS8eS4fR6A1PfA2S50A3S0SaS8eS4fR7A1PcA2S7dA3S0SaS8eS4fR8A1PeA2S5dA3S0S22S6fS9SfScS49SdS79A1A2A1SeS5R9A1A1A3S24A3S0S22S87SeS5RaA1A1A1S24A3S92S9S12R9A1SeS5RbA1A1A3S77VFB;VFF;Vrho0;A3S9fS6eVrho0;RbA3Sa4RcS97S50S49A2A2S1Sa8VCST;Vrho0;VFB;VFF;RdS26S21SaSaA2A1M0S26S21S21SaS8A2SaA2A1M1ReA8S1Sa9VCST;VXGL;Vrho0;VFB;VFF;RdG0G1S67A9S9eSa5VFB;RdG0A3Sa7VFF;RdG1A3S8dS8cRdReRcA3S4fRfA1A2A3A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;Frho;FR;FE;").
Proof.
  intros E R rho ms HR H17 H15 H12 H14 HK HB HF HP0 Hav HZ. destruct (P0o_now rho Hav HP0) as (HV & HA & HS & HD).
  pose proof (baseOz_of rho _ HF HB) as [Bsp Bv Bd _ Btop]. rewrite aceil_val in *. pose proof (T0_agreeA rho0 NF rho Hav eq_refl) as ET.
  split; [|split].
  - intros o a Ho Hr. destruct (HR o Ho) as [(H1 & H2 & H3 & H4)|[->| ->]].
    + left. destruct o as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi ob_dflt] in H1, H2, H3, H4. subst. apply range_lit' in Hr; [|lia|lia]. lia.
    + unfold O_vals in Hr. apply range_lit' in Hr; [|lia|unfold CM; lia]. eapply (infrFF_pclMA CST rho0 FF); [exact HS | unfold CM in *; lia].
    + unfold O_deflt in Hr. apply range_lit' in Hr; [|lia|unfold CM; lia]. eapply (infrFF_pclMA CST rho0 FF); [exact HD | unfold CM in *; lia].
  - intros r a Hr Ha. cbn in Hr. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; rewrite uval_lit in Ha by (unfold CM; lia); left.
    + eapply (infrFF_pclMA CST rho0 FF); [exact HV | lia].
    + eapply (infrFF_pclMA CST rho0 FF); [exact HA | lia].
    + eapply (infrFF_pclMA CST rho0 FF); [exact HS | lia].
    + eapply (infrFF_pclMA CST rho0 FF); [exact HD | lia].
  - unfold P0_vr. rewrite !rw_call'. rewrite H17, H15, H12, H14.
    split; [|split].
    + intros Hk. pose proof (holds_mem _ _ _ HF HK) as HKB. rewrite h_ule in HKB. unfold B32 in HKB. rewrite uval_lit in HKB by lia. exact (tvz_kd rho pD pK HZ HKB Hk).
    + destruct HV as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin|]. unfold uval in H1, H2. lia.
    + destruct HA as (f & sz & fl & Hin & H1 & H2). exists f, sz, fl. split; [unfold FFx; cbn; rewrite app_nil_r; exact Hin|]. unfold uval in H1, H2. lia.
Qed.

Lemma slot4_holds : ltac2:(tb__ "0|1|
SbS23S9A1SaS92S9S12R3A1R2A3S0S22S6fS9SfScS4eR2A2A1R3A3S24A3S0S22S6fS9SfScR3SdS79A1M0A2A1R4A3S24A3S0S22S6fS9SfScS4aS49A2A1R5A3S24A3S0S22S6fS9SfScS49G0A2A1R6A3S24A3S12R8S6cR6A1A2F_;F_;F_;F_;F_;Fk;FF;Frho;").
Proof.
  intros rho F k HF H1 H2 H3 H4. pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2.
  pose proof (holds_mem _ _ _ HF H3) as F3. pose proof (holds_mem _ _ _ HF H4) as F4. rewrite h_ule in F1, F2, F3, F4.
  unfold B32 in F2, F4. rewrite uval_lit in F2 by lia. rewrite uval_lit in F4 by lia. unfold pCM in F1. pose proof (uval_range rho pC) as RC. unfold CM in *.
  rewrite uval_add_small in F1 by (rewrite uval_lit by lia; lia). rewrite uval_lit in F1 by lia.
  unfold slot4_at. apply (proj2 (h_ule _ _ _)).
  assert (E1 : uval rho (SMd M_MUL pC (SLit 4)) = uval rho pC * 4) by (rewrite uval_mul_comm; rewrite uval_mul_lit by lia; lia).
  assert (E2 : uval rho (kb4 k) = 4 * uval rho k) by (unfold kb4; rewrite uval_mul_lit by lia; lia).
  unfold CM. rewrite uval_add_small by (rewrite E1, uval_lit by lia; lia). rewrite E1, E2, uval_lit by lia. lia.
Qed.

Lemma payA_same : ltac2:(tb__ "0|1|
SbOF_;S23S9A1S23S3fA1S0S22S3eR1A1S24A3Sb3S6eVrho0;R4R3SdZ0M0A1G0R2R2A8F_;Fbd;Ffacts;FP0f;").
Proof.
  intros P0f facts bd Hw. split; [exact Hw|]. split; [lia|]. intros rho HF _ _ Hn. unfold pay_sem. rewrite uval_lit by lia. split; [lia|]. split; [lia | exact Hn].
Qed.

Section X.
Variable TR : assn -> assn -> Prop.
Variable FAM : ltac2:(tb__ "0|0|
S8S23S38Q40A1A1S81F_;F_;").
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S36S4SbS23S38Q40A1A1S81S92S9S12R3A1SeS5R4A1A1A3VTR;S35S2bR6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S81S81S81S84R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S36S36S4S4S8fS23S11A1M0S23S21S4S72A2M1A1S23S21SaSaA2M2A1S81SbS23S38Q40A1A1M3G2S70G2R1R5A3S70G2R2S7RbA1A3F_;Fr;S0S2aG0A1S76RaR9R8A3S28G0R7A2A3S0S22S75RbRaR9R8S93G1S4S29S4S72A2R7A4A5S24A3SbG3VTR;S35S2bRfRdR2R1A5S73S2bS10S5RdA1A1R2R1RaA5A2Ftp1;Frho1;S23S96A1M4S94S95S37S2bR9R8R10S20G4S98R3S99R2R1A2A4A5R13RaR9R4R2A4R13S8dS8cRbRfS85R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S4S72G4S94S95SbG3G4S94S95S70G1S20S4S72RaR9A4R14A3S37S2bR12R11R19S20G4S98R9S99R8R7A2A4A5R1cR13R12RaR8A4S9fS10S5R1aA1A1S8dS8cR14R18S85R9R13RaA3A3R19A2R8A3S37S2bR9R8ReS20G4S98R7S99R6R5A2A4A5ReS8dS8cR16R1aS85RbR15RcA3A3R1bA2R15RaR9R8R6A6S1Sb1R17S85RcR16RdA3R1bR1cR1dR10R1eR19RbA9SbSa0R18S85RdR17ReA3R1cR1dS5R1eA1S5R1fA1S5R11A1R1RcA9VTR;S35S2bS74R11S8dS8cR19R1dS85ReR18RfA3A3R1eA2R18RdRcA5Sb2R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S35S2bR11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Hypothesis CVRES : ltac2:(tb__ "0|1|
S23S21S8S8A2M0A1S23S21G0S8A2A1S40SbS23S38Q40A1A1S3dZ3R3A2VTR;S35S2bS2fVAInv;VCST;VXGL;VKc;S9eR6R5A2R6R5R4S2eS7fAaS7eR3R2A5S73S2bS6eR3R2Sa6VAInv;VCST;VXGL;VKc;S9eS2eS62R6R5R4AaA5A2F_;Ftp1;Frho1;FBXc;FFFc;FFBc;").
Hypothesis REENTER : ltac2:(tb__ "0|4|
S4S2cS21S8SaA2M0SbS23S38Q40A1A1M1S8G1S70S21S21S4S2cA2M2G0A2S20G2G0S20S4S2cR7R6A4R5A4S68A3S1S41Z0S2dS20G2G0S20S4S2cR8R7A4R6A4R5A2M3A2S44G3R3A2A2VTR;S35S2bVJAv;R8A1R9R6R5A5VFAM;R4R3A2A2F_;F_;Ftp0;Fb;Ftp;Frho;Frv;Fnd;FT;").
Hypothesis POST : ltac2:(tb__ "0|1|
S4S2cSbS23S38Q40A1A1M0S8G0S70S21S4S72A2S20S4S72R6S88R5A1A4S86A3VTR;S35S2bVJAv;R6A1R7R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;Fnd;FP;").

Tactic Notation "innth" integer(n) := cbn [In cutsO exitsO Posts_op PD_op]; do n right; left; reflexivity.

Lemma meas_VB : ltac2:(tb__ "0|2|
S4S2cS8SaS8SbS41S3aR1R3A2S79A2S1S41Z0R3A2S44R3Z40M0A2A2S0S8S2dS20S21S4S2cA2S21S8SaA2S20S4S2cR8R7A4S20S8SaR6S4bR5R4A2A4A4R3A2S45S42R6S43Z2M1G0A2A2S45S42Z20S46S45S43G1Z2fA2Z1000A2S3aR3R5A2A2A2R4A2A2A3F_;F_;Frho;Fph;Fc;Frk;Fnd;FT;").
Proof. intros T nd rk c ph rho Hc Hph. unfold emeasA. cbn [eda_rank eda_var fst snd]. change (bv_unsigned (eval rho (VB c ph))) with (uval rho (VB c ph)). rewrite (VB_val rho c ph Hc Hph). unfold two47, RA.two47, Lib_scan_double.two47. reflexivity. Qed.

Lemma meas_lit : ltac2:(tb__ "0|1|
S4S2cS8S8SbS1S41Z0R2A2S44R2S43Z2Z40A2M0A2A2S0S8S2dS20S21S4S2cA2S21S8SaA2S20S4S2cR6R5A4S20S8SaR4SdR3A1A4A4R2A2S45S42R4G0A2R3A2A3F_;Frho;Fz;Frk;Fnd;FT;").
Proof. intros T nd rk z rho Hz. unfold emeasA. cbn [eda_rank eda_var fst snd]. change (bv_unsigned (eval rho (SLit z))) with (uval rho (SLit z)). rewrite uval_lit by lia. reflexivity. Qed.

Ltac meas0 := unfold z0; rewrite meas_lit by lia; lia.

Lemma X_E_L : ltac2:(tb__ "0|1|
SbS23S38Q40A1A1M0G0VTR;S35S2bVJAv;S48A1S58R3R2A5VFAM;S2dS20S21S4S2cA2S21S8SaA2S20S4S2cS58S48A4S20S8SaZ32S4bS4aZ13A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre with (P := SPA segs (JAv ndC) E_vrL rho tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_vcall rho E_vrL0 E_vrL tp w E_vrL_eq Hw). }
  apply TR_facts. intros HF.
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc HBX P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_vr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.nd0 PD_vrN NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRES eq_refl
           E_vrL (s_vr E_vrL) R_vrL Xk_op rho tp [] (tv_vec pD pK) [] (bd_op pK) [] ANone (FAM (emeasA (E_vrL0, ndC, (50, VB pC 19)) rho) tp0)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply payA_of_bud_pay. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR HM HT HTK.
    apply (HIN_site E_vrL R_vrL rho ms); [| reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact HF' | exact HP0 | exact Hav | exact HZ].
    intros o Ho. cbn in Ho. unfold is_siteobj. destruct Ho as [<-|[<-|[<-|[]]]]; cbn; auto 10.
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vrN In] in Hd.
    assert (HC : uval rho' pC = uval rho pC /\ uval rho pC <= B32).
    { split.
      - unfold uval. change (eval rho' pC) with (rw rho' 241%positive). change (eval rho pC) with (rw rho 241%positive).
        rewrite (proj1 Hag 241%positive) by (vm_compute; reflexivity). reflexivity.
      - factz HF (SPUle pC pK) H1. factz HF (SPUle pK (SLit B32)) H2. unfold B32 in *. rewrite uval_lit in H2 by lia. lia. }
    destruct HC as [HC1 HC2].
    destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.nd0 ND am_subst app].
    +   rewrite T_keepL0_eq, imp_keepL_tv, imp_keepL_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER TA_Ls ndC (50, VB pC 18) (rho_sub rho' s_keepL)); [innth 2 | assert (ES : sv_subst s_keepL pC = pC) by (vm_compute; reflexivity);
          assert (EC : uval (rho_sub rho' s_keepL) pC = uval rho pC) by (unfold uval at 1; rewrite <- eval_subst, ES; exact HC1);
          rewrite (meas_VB TA_Ls ndC 50 pC 18 (rho_sub rho' s_keepL)) by (rewrite ?EC; unfold B32 in *; lia);
          rewrite (meas_VB E_vrL0 ndC 50 pC 19 rho) by (unfold B32 in *; lia); rewrite EC; unfold B32 in *; pose proof (uval_range rho pC); lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_keepL0 T_keepL tp' w T_keepL_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_keepLs TA_Ls s_keepL (ND (tv_vec pD pK) [] (bd_op pK)) ndC);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity |].
      unfold T_keepLs, ax_add_facts. apply (SPA_refacts_JA segs _ rho' T_keepL ([slot4_at pK] ++ ss_facts (ax_S T_keepL))); [exact Hw1 | vm_compute; reflexivity |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. constructor; [|constructor]. apply (slot4_holds rho' _ pK HF2); vm_compute; reflexivity.
    +   rewrite T_failL0_eq, imp_failL_tv. change (bd_subst _ [] ++ []) with (@nil bitem).
      eapply TR_pre; [|apply (REENTER TF_L ndF (45, z0) (rho_sub rho' s_failL)); [innth 3 | unfold z0; rewrite (meas_VB E_vrL0 ndC 50 pC 19 rho) by (unfold B32 in *; lia); rewrite meas_lit by lia; pose proof (uval_range rho pC); unfold B32 in *; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_failL0 T_failL tp' w T_failL_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_failL TF_L s_failL (ND (tv_vec pD pK) [] []) ndF);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | exact Hw1].
    +   rewrite T_grownL0_eq, imp_grownL_tv, imp_grownL_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER TA_Ls ndC (50, VB pC 18) (rho_sub rho' s_grownL)); [innth 2 | assert (ES : sv_subst s_grownL pC = pC) by (vm_compute; reflexivity);
          assert (EC : uval (rho_sub rho' s_grownL) pC = uval rho pC) by (unfold uval at 1; rewrite <- eval_subst, ES; exact HC1);
          rewrite (meas_VB TA_Ls ndC 50 pC 18 (rho_sub rho' s_grownL)) by (rewrite ?EC; unfold B32 in *; lia);
          rewrite (meas_VB E_vrL0 ndC 50 pC 19 rho) by (unfold B32 in *; lia); rewrite EC; unfold B32 in *; pose proof (uval_range rho pC); lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_grownL0 T_grownL tp' w T_grownL_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_grownLs TA_Ls s_grownL (ND (tv_vec vDgL vKgL) [] (bd_op vKgL)) ndC);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity |].
      unfold T_grownLs, ax_add_facts. apply (SPA_refacts_JA segs _ rho' T_grownL ([slot4_at vKgL] ++ ss_facts (ax_S T_grownL))); [exact Hw1 | vm_compute; reflexivity |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. constructor; [|constructor]. apply (slot4_holds rho' _ vKgL HF2); vm_compute; reflexivity.
Qed.

Lemma X_E_2v : ltac2:(tb__ "0|1|
SbS23S38Q40A1A1M0G0VTR;S35S2bVJAv;S48A1S57R3R2A5VFAM;S2dS20S21S4S2cA2S21S8SaA2S20S4S2cS57S48A4S20S8SaZ23S5eA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre with (P := SPA segs (JAv ndC) E_2v rho tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_vcall rho E_2v0 E_2v tp w E_2v_eq Hw). }
  apply TR_facts. intros HF.
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc HBX P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_vr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.nd0 PD_vrN NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRES eq_refl
           E_2v (s_vr E_2v) R_2v Xk_op rho tp [] (tv_vec pD pK) [] (bd_op pK) [] ANone (FAM (emeasA (E_2v0, ndC, (35, z0)) rho) tp0)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply payA_of_bud_pay. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR HM HT HTK.
    apply (HIN_site E_2v R_2v rho ms); [| reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact HF' | exact HP0 | exact Hav | exact HZ].
    intros o Ho. cbn in Ho. unfold is_siteobj. destruct Ho as [<-|[<-|[<-|[]]]]; cbn; auto 10.
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vrN In] in Hd.
    assert (HC : uval rho' pC = uval rho pC /\ uval rho pC <= B32).
    { split.
      - unfold uval. change (eval rho' pC) with (rw rho' 241%positive). change (eval rho pC) with (rw rho 241%positive).
        rewrite (proj1 Hag 241%positive) by (vm_compute; reflexivity). reflexivity.
      - factz HF (SPUle pC pK) H1. factz HF (SPUle pK (SLit B32)) H2. unfold B32 in *. rewrite uval_lit in H2 by lia. lia. }
    destruct HC as [HC1 HC2].
    destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.nd0 ND am_subst app].
    +   rewrite T_keep2v0_eq, imp_keep2v_tv, imp_keep2v_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER (TA_2s vVALS) ndC (30, SLit (10 + 4 * CM)) (rho_sub rho' s_keep2v)); [innth 6 | unfold z0; rewrite !meas_lit by (unfold CM; lia); unfold CM; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_keep2v0 T_keep2v tp' w T_keep2v_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_keep2vs (TA_2s vVALS) s_keep2v (ND (tv_vec pD pK) [] (bd_op pK)) ndC);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity |].
      unfold T_keep2vs, ax_add_facts. apply (SPA_refacts_JA segs _ rho' T_keep2v ([slot4_at pK] ++ ss_facts (ax_S T_keep2v))); [exact Hw1 | vm_compute; reflexivity |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. constructor; [|constructor]. apply (slot4_holds rho' _ pK HF2); vm_compute; reflexivity.
    +   rewrite T_fail2v0_eq, imp_fail2v_tv. change (bd_subst _ [] ++ []) with (@nil bitem).
      eapply TR_pre; [|apply (REENTER TF_2 ndF (30, z0) (rho_sub rho' s_fail2v)); [innth 8 | unfold z0; rewrite !meas_lit by (unfold CM; lia); unfold CM; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_fail2v0 T_fail2v tp' w T_fail2v_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_fail2v TF_2 s_fail2v (ND (tv_vec pD pK) [] []) ndF);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | exact Hw1].
    +   rewrite T_grown2v0_eq, imp_grown2v_tv, imp_grown2v_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER (TA_2s vVALS) ndC (30, SLit (10 + 4 * CM)) (rho_sub rho' s_grown2v)); [innth 6 | unfold z0; rewrite !meas_lit by (unfold CM; lia); unfold CM; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_grown2v0 T_grown2v tp' w T_grown2v_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_grown2vs (TA_2s vVALS) s_grown2v (ND (tv_vec vDg2v vKg2v) [] (bd_op vKg2v)) ndC);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity |].
      unfold T_grown2vs, ax_add_facts. apply (SPA_refacts_JA segs _ rho' T_grown2v ([slot4_at vKg2v] ++ ss_facts (ax_S T_grown2v))); [exact Hw1 | vm_compute; reflexivity |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. constructor; [|constructor]. apply (slot4_holds rho' _ vKg2v HF2); vm_compute; reflexivity.
Qed.

Lemma X_E_2d : ltac2:(tb__ "0|1|
SbS23S38Q40A1A1M0G0VTR;S35S2bVJAv;S48A1S56R3R2A5VFAM;S2dS20S21S4S2cA2S21S8SaA2S20S4S2cS56S48A4S20S8SaZ23S5eA4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof.
  intros rho tp tp0.
  eapply TR_pre with (P := SPA segs (JAv ndC) E_2d rho tp).
  { intros w Hw. exact (SPA_axforms segs _ xf_vcall rho E_2d0 E_2d tp w E_2d_eq Hw). }
  apply TR_facts. intros HF.
  apply (client_callT segs AInv CST XGL ALA HCST HXGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc HBX P0_vr PTrue (fun _ H => H) (fun _ _ _ H => H)
           Pre_vr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.nd0 PD_vrN NF eq_refl eq_refl eq_refl TR TR_facts TR_ex TR_pre TR_callP CVRES eq_refl
           E_2d (s_vr E_2d) R_2d Xk_op rho tp [] (tv_vec pD pK) [] (bd_op pK) [] ANone (FAM (emeasA (E_2d0, ndC, (35, z0)) rho) tp0)).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - apply payA_of_bud_pay. vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - intros Ai ms HF' HP0 Hav HBf HFF HN HD HZ HFR HM HT HTK.
    apply (HIN_site E_2d R_2d rho ms); [| reflexivity | reflexivity | reflexivity | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | exact HF' | exact HP0 | exact Hav | exact HZ].
    intros o Ho. cbn in Ho. unfold is_siteobj. destruct Ho as [<-|[<-|[<-|[]]]]; cbn; auto 10.
  - intros [Ld ndL] rho' tp' Hd Hag. cbn [PD_vrN In] in Hd.
    assert (HC : uval rho' pC = uval rho pC /\ uval rho pC <= B32).
    { split.
      - unfold uval. change (eval rho' pC) with (rw rho' 241%positive). change (eval rho pC) with (rw rho 241%positive).
        rewrite (proj1 Hag 241%positive) by (vm_compute; reflexivity). reflexivity.
      - factz HF (SPUle pC pK) H1. factz HF (SPUle pK (SLit B32)) H2. unfold B32 in *. rewrite uval_lit in H2 by lia. lia. }
    destruct HC as [HC1 HC2].
    destruct Hd as [Hd|[Hd|[Hd|[]]]]; injection Hd as <- <-; cbn [fst snd nd_tv nd_bd nd_am OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e6.Lib_vec_reserveN.nd0 ND am_subst app].
    +   rewrite T_keep2d0_eq, imp_keep2d_tv, imp_keep2d_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER (TA_2s vDEF) ndC (30, SLit (10 + 4 * CM)) (rho_sub rho' s_keep2d)); [innth 7 | unfold z0; rewrite !meas_lit by (unfold CM; lia); unfold CM; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_keep2d0 T_keep2d tp' w T_keep2d_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_keep2ds (TA_2s vDEF) s_keep2d (ND (tv_vec pD pK) [] (bd_op pK)) ndC);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity |].
      unfold T_keep2ds, ax_add_facts. apply (SPA_refacts_JA segs _ rho' T_keep2d ([slot4_at pK] ++ ss_facts (ax_S T_keep2d))); [exact Hw1 | vm_compute; reflexivity |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. constructor; [|constructor]. apply (slot4_holds rho' _ pK HF2); vm_compute; reflexivity.
    +   rewrite T_fail2d0_eq, imp_fail2d_tv. change (bd_subst _ [] ++ []) with (@nil bitem).
      eapply TR_pre; [|apply (REENTER TF_2 ndF (30, z0) (rho_sub rho' s_fail2d)); [innth 8 | unfold z0; rewrite !meas_lit by (unfold CM; lia); unfold CM; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_fail2d0 T_fail2d tp' w T_fail2d_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_fail2d TF_2 s_fail2d (ND (tv_vec pD pK) [] []) ndF);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | exact Hw1].
    +   rewrite T_grown2d0_eq, imp_grown2d_tv, imp_grown2d_bd. rewrite app_nil_r.
      eapply TR_pre; [|apply (REENTER (TA_2s vDEF) ndC (30, SLit (10 + 4 * CM)) (rho_sub rho' s_grown2d)); [innth 7 | unfold z0; rewrite !meas_lit by (unfold CM; lia); unfold CM; lia]].
      intros w Hw. pose proof (SPA_axforms segs _ xf_vback rho' T_grown2d0 T_grown2d tp' w T_grown2d_eq Hw) as Hw1.
      apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc T_grown2ds (TA_2s vDEF) s_grown2d (ND (tv_vec vDg2d vKg2d) [] (bd_op vKg2d)) ndC);
        [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | reflexivity | vm_compute; reflexivity | reflexivity |].
      unfold T_grown2ds, ax_add_facts. apply (SPA_refacts_JA segs _ rho' T_grown2d ([slot4_at vKg2d] ++ ss_facts (ax_S T_grown2d))); [exact Hw1 | vm_compute; reflexivity |].
      intros tr md _ HF2. apply Forall_app. split; [|exact HF2]. constructor; [|constructor]. apply (slot4_holds rho' _ vKg2d HF2); vm_compute; reflexivity.
Qed.

Lemma X_Lin : ltac2:(tb__ "0|3|
S4S4S8fSbS23S38Q40A1A1M0S8G0S0S4Sa1S25S9S5cS7aA1S26S9A1A3M1R7A2R6A3S0S22S6fS9SfS1aS17S9cS15S9aS7aSdS4dA1A3S54A3A1A1SeS5R8A1A1A3S24A3S0S22S6fS9SfScS7aS7bA2A1SeS5R9A1A1A3S24A3S0S22S6fS9SfScS7bSdS79A1A2A1SeS5RaA1A1A3S24A3S0S22S87SeS5RbA1A1A1S24A3S0S22S71S9S18S10S5RcA1M2A1A1S27S9G1SeG2A1A3A3S24A3S0S22S6RcS55RbA3S24A3S0S22S90RcS6eA2S24A3S0S22Sb0S6eS10S5ReA1A1A2S24A3S0S22S30S10S5RfA1A1S4cA2S24A3S0S22Sa3RfS6dS97S50S49A2A3S24A3S0S22S3cSeS5R11A1A1S3bR10S53S49A1A2S53S7bA1A3S24A3S41S42Z33S43Z2Z40A2A2ReA2VTR;S35S2bVJAv;S4cA1R14R11R10A5VFAM;RfReA2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fs;FXf;FX;").
Proof.
  intros X Xf s rho tp b tp0 HXf Hdiv HCK HKB HB Hfb He Hid Hnf Hnb Htv Hle Hb. apply TR_facts. intros HF.
  pose proof (baseOz_of rho _ HF HB) as [_ _ _ Bvidx].
  pose proof (holds_mem _ _ _ HF Hdiv) as H1. apply (proj1 (holds_nbgeu _ _ _)) in H1. change (bv_unsigned (eval rho vVIDX)) with (uval rho vVIDX) in H1.
  change (bv_unsigned (eval rho (SMd M_DIVU vC (SLit CM)))) with (uval rho (SMd M_DIVU vC (SLit CM))) in H1. rewrite uval_divu_lit in H1 by (unfold CM; lia).
  pose proof (holds_mem _ _ _ HF HCK) as H2. pose proof (holds_mem _ _ _ HF HKB) as H3. rewrite h_ule in H2, H3. unfold B32 in H3. rewrite uval_lit in H3 by lia.
  assert (HIN : holds rho (inL_at vC)).
  { unfold inL_at. apply (proj2 (h_ule _ _ _)). rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia.
    rewrite uval_mul_lit by (unfold CM; lia). unfold CM in *. pose proof (Z.mul_div_le (uval rho vC) CM). nia. }
  eapply TR_pre; [|apply (REENTER C_L ndC (50, VB pC 20) (rho_sub rho s)); [innth 1 |]].
  - intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc Xf C_L s nd0 ndC);
      [exact He | exact Hid | exact Hnf | exact Hnb | exact Htv | reflexivity | exact Hle | reflexivity |].
    rewrite <- HXf. unfold ax_add_facts. apply (SPA_refacts_JA segs _ rho X ([inL_at vC] ++ ss_facts (ax_S X))); [exact Hw | exact Hfb | intros tr md _ HF2; apply Forall_app; split; [constructor; [exact HIN | constructor] | exact HF2]].
  - unfold emeasA. cbn [eda_rank eda_var fst snd]. pose proof (U_range (eval (rho_sub rho s) (VB pC 20))). unfold M64v in *. lia.
Qed.
Lemma X_X_Lin0 : ltac2:(tb__ "0|1|
SbS23S38Q40A1A1M0S8G0S41S42Z33S43Z2Z40A2A2R2A2VTR;S35S2bVJAv;S4cA1S65R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof. intros rho tp b tp0 Hb. apply (X_Lin X_Lin0 X_Lin0f s_Lin0); [reflexivity | vm_compute; reflexivity .. | exact Hb]. Qed.
Lemma X_X_Lin1 : ltac2:(tb__ "0|1|
SbS23S38Q40A1A1M0S8G0S41S42Z33S43Z2Z40A2A2R2A2VTR;S35S2bVJAv;S4cA1S66R5R4A5VFAM;R3R2A2A2F_;Ftp0;Fb;Ftp;Frho;").
Proof. intros rho tp b tp0 Hb. apply (X_Lin X_Lin1 X_Lin1f s_Lin1); [reflexivity | vm_compute; reflexivity .. | exact Hb]. Qed.

Lemma X_back : ltac2:(tb__ "0|5|
S4S4S8fSbS23S38Q40A1A1M0S8G0S0S4Sa1S25S9S5cS4eA1S26S9A1A3M1R7A2R6A3S0S22S6fS9SfS17S9dS15S9aS4eSdS4dA1A3S54A3A1SeS5R8A1A1A3S24A3S0S22S6fS9SfScS4eS49A2A1SeS5R9A1A1A3S24A3S0S22S6fS9SfScS49SdS79A1A2A1SeS5RaA1A1A3S24A3S0S22S6fS9SfScS4aS49A2A1SeS5RbA1A1A3S24A3S0S22S87SeS5RcA1A1A1S24A3S0S22S71S9S18S10S5RdA1M2A1A1S27S9G1SeG2A1A3A3S24A3S0S22S6RdS55RcA3S24A3S0S22S90RdS6eA2S24A3S0S22Sb0S6eS10S5RfA1A1A2S24A3S0S22S30S10S5R10A1A1S48A2S24A3S0S22Sa3R10S97S50S49A2M3G3A3S24A3S0S22S3cSeS5R12A1A1S3bR11S53S49A1M4A2G4A3S24A3S0SaS91R12S4aA2S4eA3S41S2dS20S21S4S2cA2S21S8SaA2S20S4S2cR15S48A4S20S8SaZ32S4bS4aZ0A2A4A4R12A2R10A2VTR;S35S2bVJAv;S48A1R16R13R12A5VFAM;R11R10A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftp0;Fb;Ftp;Frho;Fs;FXf;FX;").
Proof.
  intros X Xf s rho tp b tp0 HXf Hdiv HCK HKB HCK0 HB Hfb He Hid Hnf Hnb Htv Hle Hs Hb. apply TR_facts. intros HF.
  pose proof (baseOz_of rho _ HF HB) as [_ _ _ Bvidx].
  pose proof (holds_mem _ _ _ HF Hdiv) as H1. apply (proj1 (holds_bltu _ _ _)) in H1. change (bv_unsigned (eval rho vVIDX)) with (uval rho vVIDX) in H1.
  change (bv_unsigned (eval rho (SMd M_DIVU pCM (SLit CM)))) with (uval rho (SMd M_DIVU pCM (SLit CM))) in H1. rewrite uval_divu_lit in H1 by (unfold CM; lia).
  pose proof (holds_mem _ _ _ HF HCK) as H2. pose proof (holds_mem _ _ _ HF HKB) as H3. pose proof (holds_mem _ _ _ HF HCK0) as H4.
  rewrite h_ule in H2, H3, H4. unfold B32 in H3. rewrite uval_lit in H3 by lia.
  pose proof (uval_range rho pC) as RC.
  assert (ECM : uval rho pCM = uval rho pC + CM).
  { unfold pCM, CM in *. rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia. reflexivity. }
  assert (HIN : holds rho (inL_at pCM)).
  { unfold inL_at. apply (proj2 (h_ule _ _ _)). rewrite uval_add_small by (rewrite uval_lit by lia; lia). rewrite uval_lit by lia.
    rewrite uval_mul_lit by (unfold CM; lia). unfold CM in *. pose proof (Z.mul_div_le (uval rho pCM) CM). nia. }
  eapply TR_pre; [|apply (REENTER C_L ndC (50, VB pC 20) (rho_sub rho s)); [innth 1 |]].
  - intros w Hw. apply (SPA_entails_JA segs AInv CST XGL ALA NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc Xf C_L s ndC ndC);
      [exact He | exact Hid | exact Hnf | exact Hnb | exact Htv | reflexivity | exact Hle | reflexivity |].
    rewrite <- HXf. unfold ax_add_facts. apply (SPA_refacts_JA segs _ rho X ([inL_at pCM] ++ ss_facts (ax_S X))); [exact Hw | exact Hfb | intros tr md _ HF2; apply Forall_app; split; [constructor; [exact HIN | constructor] | exact HF2]].
  - rewrite (meas_VB X ndC 50 pC 0 rho) in Hb by (unfold B32 in *; lia).
    assert (EC : uval (rho_sub rho s) pC = uval rho pCM).
    { unfold uval. rewrite <- eval_subst, Hs. reflexivity. }
    rewrite (meas_VB C_L ndC 50 pC 20 (rho_sub rho s)) by (rewrite ?EC; unfold B32 in *; lia). rewrite EC, ECM. unfold CM in *. lia.
Qed.
Lemma X_X_back0 : ltac2:(tb__ "0|1|
SbS23S38Q40A1A1M0G0VTR;S35S2bVJAv;S48A1S5aR3R2A5VFAM;S2dS20S21S4S2cA2S21S8SaA2S20S4S2cS5aS48A4S20S8SaZ32S4bS4aZ0A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0. apply (X_back X_back0 X_back0f s_back0); [reflexivity | vm_compute; reflexivity .. | lia]. Qed.
Lemma X_X_back1 : ltac2:(tb__ "0|1|
SbS23S38Q40A1A1M0G0VTR;S35S2bVJAv;S48A1S5bR3R2A5VFAM;S2dS20S21S4S2cA2S21S8SaA2S20S4S2cS5bS48A4S20S8SaZ32S4bS4aZ0A2A4A4R3A2R1A2A2Ftp0;Ftp;Frho;").
Proof. intros rho tp tp0. apply (X_back X_back1 X_back1f s_back1); [reflexivity | vm_compute; reflexivity .. | lia]. Qed.

Lemma exits_okT : ltac2:(tb__ "0|3|
S4S2cS21S8SaA2M0SbS23S38Q40A1A1M1G1S70S21S21S4S2cA2M2G0A2S20G2G0S20S4S2cR6R5A4R4A4S69A3VTR;S35S2bVJAv;R6A1R7R4R3A5VFAM;S2dS20G2G0S20S4S2cR7R6A4R5A4R4A2R2A2A2F_;Ftp0;Ftp;Frho;FrvX;FndX;FX;").
Proof.
  intros X ndX rvX rho tp tp0 Hin. cbn [In exitsO] in Hin.
  destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]; injection H as <- <- <-.
  - apply X_X_Lin0. meas0.
  - apply X_X_Lin1. meas0.
  - apply X_E_L.
  - apply X_X_back0.
  - apply X_X_back1.
  - apply X_E_2v.
  - apply X_E_2d.
  - apply POST. left. reflexivity.
  - apply POST. right. left. reflexivity.
Qed.
End X.

Section Safety.
Variable ok : world -> Prop.
Hypothesis Hok : ltac2:(tb__ "0|0|
S34S2bVKc;Vok;A3").
Hypothesis AC : ltac2:(tb__ "0|0|
SacS2bSabVAInv;VCST;VXGL;A5").

Theorem opt_push3_sum : ltac2:(tb__ "0|0|
S23S38Q40A1A1S83S2bVok;S35S2bS2fVAInv;VCST;VXGL;VKc;S77VFB;VFF;A2VFB;VFF;VBX;S2eS4cAaS59Vrho0;R1A5S73S2bS6eVrho0;R1S86A5A4Ftp0;").
Proof.
  intros tp0.
  eapply triple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_sound_JA segs AInv CST XGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc ALA FUEL_op cutpcs_all 100
                (map edropA cutsO) (map edropA exitsO) ok (Q tp0) Hok (ejcertA_jcertA segs NF _ _ _ _ _ ejcertO_ok))
         with (ndT := nd0); [|left; reflexivity].
       intros X ndX rho tp Hin. apply in_map_iff in Hin as ([[X' nd'] rv] & E0' & Hin). cbn in E0'. injection E0' as <- <-.
       apply (exits_okT (triple segs ok) (fun _ _ w => SPfamGTA segs (map nI (map edropA cutsO)) w \/ Q tp0 w)
                (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (call_soundPA3 segs ok))
         with (rvX := rv) (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HBXc. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Lib_vec_reserveN_pf.vec_reserveN_sum AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HBXc rho1 ok Hok AC tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT _. apply (reenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue ok (map edropA cutsO) T nd).
         apply in_map_iff. exists (T, nd, rv'). auto.
       - intros P nd rho1 tp1 b tp2 HinP. apply (exit_postGA segs AInv CST XGL NF Kc (P0_op FB FF) FB FF BX PTrue ok rho0 tp0 nd Posts_op P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Safety.

Section Existence.
Hypothesis ACX : ltac2:(tb__ "0|0|
SadS2bSabVAInv;VCST;VXGL;A5").

Theorem opt_push3_sum_ex : ltac2:(tb__ "0|0|
S23S38Q40A1A1S82S2bS35S2bS2fVAInv;VCST;VXGL;VKc;S77VFB;VFF;A2VFB;VFF;VBX;S2eS4cAaS59Vrho0;R1A5S73S2bS6eVrho0;R1S86A5A3Ftp0;").
Proof.
  intros tp0.
  eapply etriple_conseq; [ | intros w Hw; exact Hw | ].
  2: { apply (cfg_complete_JA segs AInv CST XGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue HKc ALA FUEL_op cutpcs_all 100 cutsO exitsO (Q tp0) ejcertO_ok)
         with (ndT := nd0) (rv := (100, z0)); [|left; reflexivity].
       intros X ndX rv rho tp Hin.
       apply (exits_okT (etriple segs) (fun b _ w => SPfamETA segs (map (enodeIA AInv CST XGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue) cutsO) b w \/ Q tp0 w)
                (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (call_completePA3 segs)) with (tp0 := tp0).
       - intros FBc FFc BXc rho1 tp1 HBXc. apply (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ec.Lib_vec_reserveN_pf.vec_reserveN_sum_ex AInv CST XGL ALA HCST HXGL Kc HKc FBc FFc BXc HBXc rho1 ACX tp1).
       - intros T nd rv' rho1 tp1 b tp2 HinT Hm. apply (ereenter_cutJA segs AInv CST XGL NF Kc rho0 (P0_op FB FF) FB FF BX PTrue cutsO T nd rv'); [exact HinT | exact Hm].
       - intros P nd rho1 tp1 b tp2 HinP. apply (eexit_postGA segs AInv CST XGL NF Kc (P0_op FB FF) FB FF BX PTrue rho0 tp0 nd Posts_op P). exact HinP.
       - exact Hin. }
  intros w Hw. apply JA_pre_intro. exact Hw.
Qed.
End Existence.
End Sum.
End Lib_opt_push3_pf.

