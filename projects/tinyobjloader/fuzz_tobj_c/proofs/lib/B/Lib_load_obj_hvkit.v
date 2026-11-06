(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "nat"; "pair"; "prod"; "bool"; "list"; "true"; "cons"; "nil"; "option"; "snd"; "andb"; "app"; "fst"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "rw"; "sprop"; "sv_eqb"; "SLit"; "holds"; "ob_base"; "ob_lo"; "obj_range"; "ss_objs"; "@Stdlib.ZArith.BinInt.Z"; "lt"; "le"; "pow"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "TPA"; "frinA"; "tvinA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_hvkit"; "VLAi"; "robjs_chkR"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "RL"; "VLA"; "z0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "seq"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLC"; "pI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efmeasA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "robj_ent"; "robjs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "V_B"; "V_L"; "extraLO"; "tblB"; "tblL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "FBx"; "T0"; "T_ok"; "tvd"; "tvz"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "pclMA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR"; "robjs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "robj_image"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@Stdlib.Lists.List"; "In"; "combine"; "existsb"; "filter"; "find"; "forallb"].
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Code Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud Lib_load_obj_armkit Lib_load_obj_armkit2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import LOAddr LOLAddr.

Definition VLAi (ph a : Z) : sv := ltac2:(tb__ "0|0|
S2cVph;S17Va;A1A2").
Lemma VLAi_z0 : ltac2:(tb__ "0|0|
S0S21S12S2cR1S2dA2S29R1Z0A2A3Fph;"). Proof. reflexivity. Qed.

Lemma VLA_lt2 : ltac2:(tb__ "0|a|
S13S13S0S0S0S0S23S23S25S25S2S2S21S2fQ40A1M0S14RbP1ccM1A2S14RcG1A2A3S21G0S14RcP1d3M2A2S14RdG2A2A3S1dS2eReS34A2S2eReS33A2A2S1eS2eRfS33A2S1fZ2M3Z1aA2A2S20S1eZ0M4RbA2S1dRbS1fG3Z1bA2M5A2A2S20S1eG4RdA2S1dRdG5A2A2S1eG4RfA2S1dR11Z40A2S22S1dR11R12A2S20S21S0R11R12A3S1dRfR10A2A2A2S20S1eG4S35S3S4S4S23S25A2M6S2A2M7S4S0S12A2M8S3G6S2S3S23S25ReRcA4RaA4S3S0S12S2bS29R12R10A2A4A4R14A2M9A2S1dG9S35S3G7G8S3G6S2S3S23S25RfRdA4RbA4S3S0S12S2bS29R13R11A2A4A4R15A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Fk';Fk;Fnd';Fnd;FX';FX;Fa';Fa;Fph';Fph;Frho';Frho;").
Proof.
  intros rho rho' ph ph' a a' X X' nd nd' k k' E460 E467 Hi Hc Ha' Ha Hph' Hph Hlt.
  assert (EI : uval rho' pI = uval rho pI) by (unfold uval, pI; cbn [eval]; rewrite E460; reflexivity).
  assert (EC : uval rho' xLC = uval rho xLC) by (unfold uval, xLC; cbn [eval]; rewrite E467; reflexivity).
  unfold VLAi. rewrite !efmeasA_VLA.
  rewrite (VLA_val rho' ph' (SLit a')); [| lia | rewrite EI, EC; exact Hi | rewrite EC; exact Hc | rewrite uval_lit by lia; lia].
  rewrite (VLA_val rho ph (SLit a)); [| lia | exact Hi | exact Hc | rewrite uval_lit by lia; lia].
  rewrite !uval_lit by lia. rewrite EI, EC. pose proof (uval_range rho pI). unfold Mline, RL.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 37) with 137438953472. change (2 ^ 27) with 134217728 in *. change (2 ^ 26) with 67108864 in *. lia.
Qed.

Definition oidx (b lo : sv) (T : axst) : nat := ltac2:(tb__ "0|3|
SaS4S2S11A2M0A1S2Lx;S51G0G0ScS16S19SbS2S11R1A3M1A1Vb;A2S16S1aG1A1Vlo;A2A2Lp;S4eS2S11S30U0SfS11S1cS24VT;A1A1M2A2A2G2A4A3G0G0S2Lp;R1S2S11R2Ls;Li;X4x1Lp;U3e7Xax2").
Definition spA : sv := SVar 10.
Definition s1A : sv := SAlu ALU_ADD spA (SLit (-640)).

Definition sel_front (sel : list nat) (n : nat) : axform := ltac2:(tb__ "0|0|
S44SdS2Vsel;S50S2S2S10S4fS2S4cR1A1Vsel;A3A1Li;S30U0Vn;A2A3A3A1").

Definition robjs_chkR (facts : list sprop) (tv : list (sv * sv)) (fr : list (sv * Z * sv)) (extra : sobj -> bool) (R : list sobj) : bool := ltac2:(tb__ "0|0|
S52S11S11S5S5L_;S48R1A1S7S39Vfacts;Vtv;Vfr;Vextra;S8S11R1S9S11A1A3A5X5x2Lo;VR;A3").

Section SiteR.
Variable AInv : ltac2:(tb__ "0|0|
S36S13S6S2fQ40A1A1S32OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S4aS37VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S4bVCST;R1A2S20S1eZ0R2A2S1dR2S49A2A2F_;Fa;").
Variable rho0 : valuation.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S6S4S4S0S0A2S0A2A1").

Lemma robjs_chkR_sound : ltac2:(tb__ "0|1|
S36S13S6S15A1S6S4S12S12A2A1S6S4S4S12S0A2S12A2A1S11S5F_;S6S11A1S13S6S2fQ40A1A1S32VAInv;RaR3R2R1A4S31S15S18RaA1R9A3S26Vrho0;RcA2S41RcS40Vrho0;A1A2S28VFB;ReRdRbA4S42ReRcA2S43RfRdA2S27VFF;R11R10RdA4S21S5S2aR10RfReRdRcA5S7A3S11S0S4dS11R2RfA3S21S5R11R3A1S7A3S20S1eSeS0S0S1bR16R4A2M0A3R3A2S1dR3SbS0S0G0A3A2A2S46VCST;Vrho0;S3fVFB;R17R15A3S45VFF;R17R14A3R4A5F_;F_;F_;Fa;Fo;S47VCST;Vrho0;VFB;VFF;R13R11R10ReA8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fextra;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho facts tv fr extra R rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR Hchk Hextra o a Ho Hr.
  unfold robjs_chkR in Hchk. pose proof (proj1 (forallb_forall _ _) Hchk o Ho) as Hc. cbv beta in Hc.
  apply lazy_orb_prop in Hc as [Hc|Hc].
  - right. unfold TobjJAS.robj_image in Hc. destruct (ob_base o) as [b0| | | | | | |] eqn:Eb; try discriminate. destruct b0; try discriminate.
    destruct (ob_lo o) as [lo| | | | | | |] eqn:El; try discriminate. destruct (ob_hi o) as [hi| | | | | | |] eqn:Eh; try discriminate.
    apply lazy_andb_prop in Hc as [H1 Hc]. apply lazy_andb_prop in Hc as [H2 H3]. apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Eb, El, Eh in Hr. cbn [eval fst snd] in Hr. unfold IMG_HI in *.
    rewrite (u64_lit 0), !soff_lit_small in Hr by lia. lia.
  - left. apply (robjs_chkC_sound AInv CST ALA HCST rho0 FB FF Ai rho facts tv fr extra [o] rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR Hc) with (o := o); [| left; reflexivity | exact Hr].
    intros o' a' [<-|[]] HE Hr'. exact (Hextra o a' Ho HE Hr').
Qed.
End SiteR.

Definition PhisH : list (list positive * (valuation -> Prop)) := ltac2:(tb__ "0|3|
S8S4S6S1A1M0S13OFrho;M1A2M2S3G0G1S3bS3eA4S8G2S3G0G1S3aS3dA4S9G2A1A3A3").
Definition mH (ph a : Z) : Z * sv := ltac2:(tb__ "0|0|
S3S0S12S2bS29Vph;Va;A2A4").
Definition extra_hv (o : sobj) : bool := ltac2:(tb__ "0|0|
S5S5L_;S3cVo;A1S7S38Vo;A1X5x2").
