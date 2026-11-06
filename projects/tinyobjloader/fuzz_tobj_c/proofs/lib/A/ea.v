(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require IfaceS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj e4.

(* [comment removed for export] *)
Module DrvBox.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "length"; "true"; "app"; "nil"; "pair"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "ss_facts"; "valuation"; "SLit"; "sprop"; "holds"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "bxt"; "bsumV"; "BXok_d"; "LARGE_MIN"; "SECCAP"; "bud_pay"; "bxN"; "bd_wpos"; "bxK"; "bxS"; "bxV"; "BXnn"; "TVMAX"; "bd_below"; "bd_nn"; "bsumK"; "mkBX"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "mul"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "NDA"; "ANone"; "JA"; "amode"; "ndesc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.DrvBox"; "BXnn9"; "box_back"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "PRIM_LIVE_MAX"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "payA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "alloc_lawsA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymEntail SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface IfaceEx IfaceS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA SummaryA3 TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAM.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition box_back (BX BX' : bxt) (brest : list bitem) (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S22S26S1aVBX';A1S1aVBX;A1A2S22S26S25S1bVBX;A1S12Vbrest;Vrho;A2A2S1bVBX';A1A2S22S26S25S19VBX;A1S20Vbrest;Vrho;A2A2S19VBX';A1A2S22S1fVbrest;Vrho;A2S22S23S2S18Vbrest;A1S4A3S23S8S17VBX';A1S17VBX;A1A3A2A2A2A2A2").

Definition BXnn9 (BX : bxt) : Prop := ltac2:(tb__ "0|1|
S22S1cVBX;A1S22S26Z0S17VBX;A1M0A2S26S25G0S28S1dZ9A2A2S3cA2A2A2").

Section WithSegs.
Variable segs : list Segment.
Variable AInv : ltac2:(tb__ "0|0|
S3bScS0S35Q40A1A1S3dOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S40Vsegs;VAInv;VCST;A3").
Section Box.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S0S1S1S8S8A2S8A2A1").
Variable PA : AA -> Prop.
Let JA : ltac2:(tb__ "0|0|
S11S3bOF_;S30S2bFnd;FPA;FBX;") := ltac2:(tb__ "0|0|
S2eVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;A9").

Lemma box_open_w : ltac2:(tb__ "0|3|
S11S0S1SaSaA2M0A1S0S1S1SaS8A2SaA2A1S0S10A1M1G1G1S32ScS0S35Q40A1A1S36S33RaA1S23S2S16SbS31R5A1A1SdZ0M2A1G2R8S5S10R7R6A3A5S4A3S3aSeSfR5A1SbS31R6A1A1A3S26S25S28S14S25S27S3S1S8S8A2VFB;A2A1S27S3G0RcA2A1A2A2S29S12RaR6A2S12R8R6A2A2A2S15A2S2aVsegs;VJA;ReVPA;S2cRdRcRbS2dA4A3R8R7R6R5A6S24S11S11S22S22S13Z9R1A2S34R10R1RbR9A4A2S2aVsegs;VJA;R1VPA;S2cRfReRcS2dA4A3RaR9R8R7A6A2LBX';A2F_;F_;F_;F_;F_;Fw;Ftp;Frho;FC;Fbrest;Fbdc;Fbd;Ffr;Ftv;FBX;").
Proof using ALA.
  intros BX tv fr bd bdc brest C rho tp w [[HV0 HK0] [HN0 HN9]] Hpay HF Hcap [Hsm (Ai & kc & HJ)].
  pose proof (JAi_large_live_le0 segs AInv CST XGL ALA NP Kc rho0 P0f FB FF BX PA tv fr bd Ai kc rho tp (w_tr w) (cfg_model (w_cfg w)) HJ) as LL.
  destruct (JAi_proj_BUD AInv CST XGL NP Kc rho0 P0f FB FF BX PA _ Ai kc rho tp _ _ HJ) as (HBU & HCK & Hkc).
  cbn [nd_bd nd_am] in HBU. pose proof HBU as (A1 & A2 & A3 & A4 & A5 & Hw & Hnn & B1 & B2).
  destruct (bud_pay_sound _ _ _ _ _ rho HF Hnn Hpay) as (P1 & P2 & _ & _ & _ & P6 & P7 & _).
  rewrite bsumV_app in P1. rewrite bsumK_app in P2. pose proof (uval_range rho (SLit 0)) as U0.
  assert (Hwc : bd_wpos bdc = true /\ bd_wpos brest = true).
  { unfold bd_wpos in *. rewrite forallb_app in P7. apply andb_prop in P7. exact P7. }
  assert (Hnc : bd_nn bdc rho /\ bd_nn brest rho) by (unfold bd_nn in *; apply Forall_app in P6; exact P6).
  destruct (bsum_nonneg bdc rho (proj1 Hwc) (proj1 Hnc)) as [S1 S2]. destruct (bsum_nonneg brest rho (proj2 Hwc) (proj2 Hnc)) as [S3 S4].
  pose proof (apot_range ANone rho) as [[R1 _] [R2 _]].
  unfold bxa in A1, A2, B1, B2. cbn [fst snd] in A1, A2, B1, B2. unfold bxV, bxK in HV0, HK0.
  set (BX' := mkBX (VMAX - aa_V Ai - bsumV bdc rho - fst (apot ANone rho), snd (bx2 BX) + bsumK brest rho) (LARGE_MIN * large_live Ai - aa_V Ai) (bxN BX)).
  assert (LM : LARGE_MIN * large_live Ai <= LARGE_MIN * (Z.of_nat (length FB) + Z.of_nat (length tv))) by (apply Z.mul_le_mono_nonneg_l; [unfold LARGE_MIN; lia | exact LL]).
  assert (EP : fst (apot ANone rho) = 0) by reflexivity.
  exists BX'. split; [split|].
  -   unfold BXok_d, BXok, BXnn, bxV, bxK, BX'. cbn [bx2 bxS bxN fst snd]. split; [split; [split; lia|lia]|]. split; [exact HN0|]. split; [lia | exact HN9].
  -   unfold box_back, bxV, bxK, BX', capK in *. cbn [bx2 bxS bxN fst snd]. repeat split; try lia; [exact (proj2 Hnc) | exact (proj2 Hwc)].
  - split; [exact Hsm|]. exists Ai, kc.
    apply (JAi_rebx AInv CST XGL NP Kc rho0 P0f FB FF BX BX' PA (NDA tv fr bd ANone) bdc Ai kc rho tp _ _); [|unfold BX'; cbn [bxN]; lia|exact HJ].
    intros _ _ _. cbn [nd_bd nd_am]. split.
    + unfold BUD, bxa, BX'. cbn [bx2 fst snd]. repeat split; try assumption; try lia; [exact (proj1 Hwc) | exact (proj1 Hnc)].
    + unfold capK, BX'. cbn [bxS]. lia.
Qed.

Lemma box_close : ltac2:(tb__ "0|1|
S11S11S0S10A1M0S0S1SaSaA2A1S0S1S1SaS8A2SaA2A1G0S2fS9S32ScScS0S35Q40A1A1S36S33RdA1S34ReRdRcR5A4S3eR8R6R5A3S23S2S1eR9ReA2S4A3S2aVsegs;VJA;R10VPA;S2cReRdRcRbA4A3R9R7R6R5A6S2aVsegs;VJA;R12VPA;S2cRfReS5S10RdR10A3RcA4A3RaR8R7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Frho';Frho;FC;Fn;Fam;Fbdp;Ffr;Ftv;Fbrest;FBX';FBX;").
Proof using .
  intros BX BX' brest tv fr bdp am n C rho rho' tp w [[HV0 HK0] _] (K1 & K2 & K3 & K4 & K5 & K6) Hag Hb [Hsm (Ai & kc & HJ)].
  split; [exact Hsm|]. exists Ai, kc.
  apply (JAi_rebx AInv CST XGL NP Kc rho0 P0f FB FF BX' BX PA (NDA tv fr bdp am) (bdp ++ brest) Ai kc rho' tp _ _); [|lia|exact HJ].
  cbn [nd_bd nd_am]. intros HBU HCK Hkc. pose proof HBU as (A1 & A2 & A3 & A4 & A5 & Hw & Hnn & B1 & B2).
  pose proof (apot_range am rho') as [[R1 _] [R2 _]].
  rewrite <- (bsumV_agree n rho rho' brest Hag Hb) in K2. rewrite <- (bsumK_agree n rho rho' brest Hag Hb) in K3.
  pose proof (bd_nn_agree n brest rho rho' Hag Hb K4) as K4'.
  unfold bxa, bxV, bxK, capK in *. cbn [fst snd] in *. split; [|lia].
  unfold BUD. cbn [fst snd]. rewrite bsumV_app, bsumK_app.
  split; [lia|]. split; [lia|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
  split; [unfold bd_wpos in *; rewrite forallb_app, Hw, K5; reflexivity|].
  split; [unfold bd_nn in *; apply Forall_app; split; assumption|]. lia.
Qed.

Lemma box_open_T : ltac2:(tb__ "0|3|
S36OF_;S11S0S1SaSaA2M0A1S0S1S1SaS8A2SaA2A1S0S10A1M1G1G1S32ScS0S35Q40A1A1S39S33RaA1S23S2S16SbS31R5A1A1SdZ0M2A1G2R8S5S10R7R6A3A5S4A3S3aSeSfR5A1SbS31R6A1A1A3S26S25S28S14S25S27S3S1S8S8A2VFB;A2A1S27S3G0RcA2A1A2A2S29S12RaR6A2S12R8R6A2A2A2S15A2F_;S11S13Z9R1A2S34RfR2RaR8A4S38Vsegs;R11S2aVsegs;VJA;R3VPA;S2cRfReRcS2dA4A3RaR9R8A5R7A4F_;F_;FBX';S38Vsegs;RfS2aVsegs;VJA;ReVPA;S2cRdRcRbS2dA4A3R8R7R6A5R5A4F_;F_;F_;F_;FQ;Ftp;Frho;FC;Fbrest;Fbdc;Fbd;Ffr;Ftv;FBX;Fok;").
Proof using ALA.
  intros ok BX tv fr bd bdc brest C rho tp Q HBX Hpay Hcap HT. apply triple_factsA. intros HF.
  eapply (triple_conseq (P := fun w => exists BX', (BXok_d 9 BX' /\ box_back BX BX' brest rho) /\ SPA segs (JA BX' PA (NDA tv fr bdc ANone)) C rho tp w));
    [intros w HS; exact (box_open_w BX tv fr bd bdc brest C rho tp w HBX Hpay HF (Hcap HF) HS) | intros w' Hw'; exact Hw' |].
  apply triple_ex. intros BX'. apply triple_pure. intros [H1 H2]. exact (HT BX' H1 H2).
Qed.
Lemma box_open_Te : ltac2:(tb__ "0|3|
S11S0S1SaSaA2M0A1S0S1S1SaS8A2SaA2A1S0S10A1M1G1G1S32ScS0S35Q40A1A1S36OF_;S33RaA1S23S2S16SbS31R5A1A1SdZ0M2A1G2R8S5S10R7R6A3A5S4A3S3aSeSfR5A1SbS31R6A1A1A3S26S25S28S14S25S27S3S1S8S8A2VFB;A2A1S27S3G0RcA2A1A2A2S29S12RaR6A2S12R8R6A2A2A2S15A2F_;S11S13Z9R1A2S34RfR2RaR8A4S37Vsegs;S2aVsegs;VJA;R3VPA;S2cRfReRcS2dA4A3RaR9R8A5R7A3F_;F_;FBX';S37Vsegs;S2aVsegs;VJA;ReVPA;S2cRdRcRbS2dA4A3R8R7R6A5R5A3F_;F_;F_;F_;FQ;Ftp;Frho;FC;Fbrest;Fbdc;Fbd;Ffr;Ftv;FBX;").
Proof using ALA.
  intros BX tv fr bd bdc brest C rho tp Q HBX Hpay Hcap HT. apply etriple_factsA. intros HF.
  eapply (etriple_conseq (P := fun w => exists BX', (BXok_d 9 BX' /\ box_back BX BX' brest rho) /\ SPA segs (JA BX' PA (NDA tv fr bdc ANone)) C rho tp w));
    [intros w HS; exact (box_open_w BX tv fr bd bdc brest C rho tp w HBX Hpay HF (Hcap HF) HS) | intros w' Hw'; exact Hw' |].
  apply etriple_ex. intros BX'. apply etriple_pure. intros [H1 H2]. exact (HT BX' H1 H2).
Qed.

Lemma payA_self : ltac2:(tb__ "0|1|
S0SeA1S0S10A1S23S2S18R1A1S4A3S3fVNP;Vrho0;VP0f;R3SdZ0M0A1G0R2S5S10R2S6S10A1A3A8F_;Fbdc;Ffacts;").
Proof using .
  intros facts bdc Hw. unfold payA, pay_okF. rewrite app_nil_r. split; [exact Hw|]. split; [lia|].
  intros rho _ _ _ Hn. unfold pay_sem. pose proof (uval_range rho (SLit 0)) as U0.
  assert (E0 : uval rho (SLit 0) = 0) by reflexivity. rewrite E0. repeat split; try lia. exact Hn.
Qed.
End Box.
End WithSegs.

Lemma BXnn_mk00 : ltac2:(tb__ "0|1|
S8S33S21S7S8S8Z0M0G0A4R1G0A3A1FS;").
Proof. intros S. unfold BXnn9, BXnn, bxV, bxK, TVMAX, PRIM_LIVE_MAX. cbn [bx2 bxN fst snd]. lia. Qed.
End DrvBox.

(* [comment removed for export] *)
Module DrvSiteS.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "true"; "list"; "cons"; "prod"; "length"; "nil"; "None"; "Some"; "option"; "pair"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "rho_absorb"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "of_nat"; "lt"; "pow"; "mul"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_next"; "sv"; "valuation"; "SVar"; "sobj"; "ss_facts"; "sv_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "PRIM_LIVE_MAX"; "SEC_SLACK"; "aa_Kf"; "aa_Km"; "aa_V"; "cls_keptA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "Pre_malloc"; "L_malloc_ok"; "V_RES"; "malloc_shape"; "ulink"; "unwind_stopJ"; "ustop"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "uval"; "KU"; "BUD"; "bitem"; "bd_below"; "bx2"; "bxN"; "bsumK"; "bsumV"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "nd_am"; "nd_tv"; "nd_bd"; "JA"; "ndesc"; "ANone"; "NDA"; "amode"; "apot"; "bxa"; "nd_below"; "nd_fr"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "pos_add_nat"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkPA"; "entails_frA"; "import_subA"; "@stdpp.bitvector.definitions"; "bv"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "etriple"; "triple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM"; "T_afterA"; "call_checkTA"; "payA"; "site_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.IfaceS"; "alloc_roomA"; "malloc_contractA_strong"; "malloc_contractA_strong_ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget"; "KMAX"; "VMAX"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymSummary SymEntail SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA SummaryA GlueA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface IfaceEx IfaceS.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA SummaryA3 TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAM.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM.

Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma call_checkPA_drop1 : ltac2:(tb__ "0|1|
S15S15S11S5S20A1S15S15S1S3S4bR6R5R4R3S6S15R2S6S15R1S9S15A1M0A3A3A5S4A3S1S3S4bR7R6R5R4S6S15R2G0A3A5S4A3F_;FP2;FP1;FR;Fs;FPre;FC;").
Proof.
  intros C Pre s R P1 P2 H. unfold call_checkPA, call_checkP in *. cbn [map forallb] in *.
  rewrite !Bool.andb_true_iff in H. rewrite !Bool.andb_true_iff. tauto.
Qed.

Lemma BUD_room : ltac2:(tb__ "0|3|
S5S35A1S7S0S0A2S0S0S0S1eS34R6R5R4R3R2R1A6S2S16Z0M0SeS0S0R6A3M1A2S2S16G0SfS0S0R6A3M2A2S2S16S17S17R5S3aR7R2A2A2G1A2S60A2S16S17S17S1bS33S17R4R3A2A2S39R7R2A2A2G2A2S1bS33S5fA2A2A2A2A2F_;Frho;FKf;FKm;FV;FP2;Fb;").
Proof. intros b P2 V Km Kf rho (A1 & A2 & _ & _ & _ & _ & _ & B1 & B2). repeat split; assumption. Qed.

Section WithSegs.
Variable segs : list Segment.
Variable E : aentry.
Variable AInv : ltac2:(tb__ "0|0|
S23S1eS5S4eQ40A1A1S5eOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S31Vsegs;VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S5cVCST;R1A2S2S16Z0R2A2S19R2S58A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S5cVXGL;R1A2S2S16Z0R2A2S19R2S58A2A2F_;Fa;").
Section Sum.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S5S7S7S0S0A2S0A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.
Let JA : ltac2:(tb__ "0|0|
S3fS4aFnd;") := ltac2:(tb__ "0|0|
S3eVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").

Theorem malloc_callA_S : ltac2:(tb__ "0|8|
S23OF_;S53OF_;S5S2eA1S30S15S11S5S20A1M0S1eS5S4eQ40A1A1M1S3fS5S35A1S50S2dRaR9A2S47Vsegs;VKc;RcA3S5aVsegs;VE;VAInv;VCST;VXGL;A5S1ScG0A1S4cRbS2aVE;RdRcA3RaA3SbG0R9A2A3S1S3S4bRcS2aVE;ReRdA3RbRaS6S15S2bVE;ReRdA3S9S15A1A3A5S4A3S1S3S55VNP;RcA2S4A3S1S3S5dVNP;S1cS14ReA1A1A2S4A3S1S3S45S1cS14RfA1A1RaA2S4A3S1S3S36S1cS14R10A1A1RaA2S4A3S1S3S22S1cS14R11A1A1S10R10PcM2A2A2S4A3S1S1dS10S4dR11S2aVE;R14R13A3S2bVE;R14R13A3R12A4S2cA2S1fS48S1cS14R12A1A1UaM3A2A1A3S56VNP;Vrho0;VP0f;S21S14R13A1A1S10R12G2A2S33S3dReA1RdA8S23S23VPA;R2A1M4S29R3R2S32R14S10R16G2A2A2A3R1cR3A1F_;F_;FA';FA;S23S0G4S16Z0R2A2S34S3dR14A1S44S37VBX;A1S43S3bR14A1R16A2R3A3S28R4A1S27R4A1S26R4A1R16A6S59R5S32R17S10R19G2A2A2A2F_;F_;F_;Fkc;FA;S1S42S3bR11A1S40A3S16S17S17S18S8S7S0S0A2VFB;A2A1S18S8S7S1dS1dA2M5S3cR12A1A2A1A2S25A2S1aZ2M6Z14A2A2S16S17S38VBX;A1S18S8G5S3cR13A1A2A1A2S24A2S57VAInv;VCST;VXGL;VNP;Vrho0;VP0f;VFB;VFF;R19R18R17R16R14SaS0A1S23S4fS2S2S16Z1S32R18S10R1aG2A2A2M7A2S19G7S1aG6Z27A2A2A2S2fR1dR1cS13S12R18R19R1A3R1aA2A3A2Lms;LAi;AfS1eG1S52Vsegs;R1fS49Vsegs;S3eVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;R20S41S6G5SdS1dS1dS1fS48S1cS14R1cA1A1G3A2A1S10R1bG2A2A4S3cR17A1A3S46R17A1R16S3bR17A1A4AcS54S2aVE;R1eR1dA3R1cR1bR1aS2bVE;R1eR1dA3A5R2R1A5R15A4Ftp';Frho';S52Vsegs;R1eS49Vsegs;VJA;R16A1R1bR18R17A5R14A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;Fok;FPA';").
Proof using ALA HCST HXGL HKc.
  intros PA' ok W st Cl s R rho tp nd bd' Q HW Hok MS He Hchk Htp Hnf Hnb Hbb Hs12 Hres HPAY HPAK HROOM Ham Hfew Hprim HSITE Tok.
  apply (malloc_callT_gen_sec segs E AInv CST XGL ALA HCST HXGL NP Kc rho0 P0f FB FF BX PA HKc (triple segs ok) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok)
           (call_soundPA3 segs ok) false true (fun A r => alloc_roomA A (bv_unsigned (rw r 12%positive))) PA' W st Cl s R rho tp nd bd' Q); try assumption.
  - intros Ai rho1 tp1.
    apply (TRs_pureP segs ok _ (alloc_roomA Ai (bv_unsigned (rw rho1 12%positive)))); [intros w [_ [_ H]]; exact H|]. intros Hroom.
    apply (TRs_pre segs ok (SPA segs (J_alloc_pre AInv W st Ai Kc (SVar 12)) (Pre_malloc E W st) rho1 tp1)); [intros w [Hsm [HJ _]]; exact (conj Hsm HJ)|].
    apply (MS W st ok Ai Kc rho1 tp1 HW HKc (proj1 Hok) (proj2 Hok)). intros tr md _. exact Hroom.
  - intros A ms kc HP Hkc HB. cbn beta. rewrite rw_call'. exact (HROOM A kc HP Hkc HB).
  -   intros Ai kc tr md HJ. destruct nd as [tv fr bd am]. cbn [nd_am nd_tv] in Ham, Hfew. subst am.
    pose proof (JAi_large_live_le0 segs AInv CST XGL ALA NP Kc rho0 P0f FB FF BX PA tv fr bd Ai kc rho tp tr md HJ) as LL. unfold sec_room. lia.
  -   intros Ai kc tr md HJ.
    pose proof (JAi_small_live_le AInv CST XGL NP Kc rho0 P0f FB FF BX PA nd Ai kc rho tp tr md HJ) as SL. unfold prim_room. lia.
  - intros E0. discriminate E0.
  - intros _. exact Tok.
Qed.

Theorem malloc_callA_ex_S : ltac2:(tb__ "0|8|
S23OF_;S5S2eA1S30S15S11S5S20A1M0S1eS5S4eQ40A1A1M1S3fS5S35A1S50S2dRaR9A2S5bVsegs;VE;VAInv;VCST;VXGL;A5S1ScG0A1S4cRaS2aVE;RcRbA3R9A3SbG0R8A2A3S1S3S4bRbS2aVE;RdRcA3RaR9S6S15S2bVE;RdRcA3S9S15A1A3A5S4A3S1S3S55VNP;RbA2S4A3S1S3S5dVNP;S1cS14RdA1A1A2S4A3S1S3S45S1cS14ReA1A1R9A2S4A3S1S3S36S1cS14RfA1A1R9A2S4A3S1S3S22S1cS14R10A1A1S10RfPcM2A2A2S4A3S1S1dS10S4dR10S2aVE;R13R12A3S2bVE;R13R12A3R11A4S2cA2S1fS48S1cS14R11A1A1UaM3A2A1A3S56VNP;Vrho0;VP0f;S21S14R12A1A1S10R11G2A2S33S3dRdA1RcA8S23S23VPA;R2A1M4S29R3R2S32R13S10R15G2A2A2A3R1aR3A1F_;F_;FA';FA;S23S0G4S16Z0R2A2S34S3dR13A1S44S37VBX;A1S43S3bR13A1R15A2R3A3S28R4A1S27R4A1S26R4A1R15A6S59R5S32R16S10R18G2A2A2A2F_;F_;F_;Fkc;FA;S1S42S3bR10A1S40A3S16S17S17S18S8S7S0S0A2VFB;A2A1S18S8S7S1dS1dA2M5S3cR11A1A2A1A2S25A2S1aZ2M6Z14A2A2S16S17S38VBX;A1S18S8G5S3cR12A1A2A1A2S24A2S57VAInv;VCST;VXGL;VNP;Vrho0;VP0f;VFB;VFF;R18R17R16R15R13SaS0A1S23S4fS2S2S16Z1S32R17S10R19G2A2A2M7A2S19G7S1aG6Z27A2A2A2S2fR1cR1bS13S12R17R18R1A3R19A2A3A2Lms;LAi;AfS1eG1S51Vsegs;S49Vsegs;S3eVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;R1eS41S6G5SdS1dS1dS1fS48S1cS14R1bA1A1G3A2A1S10R1aG2A2A4S3cR16A1A3S46R16A1R15S3bR16A1A4AcS54S2aVE;R1dR1cA3R1bR1aR19S2bVE;R1dR1cA3A5R2R1A5R14A3Ftp';Frho';S51Vsegs;S49Vsegs;VJA;R15A1R1aR17R16A5R13A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;FPA';").
Proof using ALA HCST HXGL HKc.
  intros PA' W st Cl s R rho tp nd bd' Q HW MSX He Hchk Htp Hnf Hnb Hbb Hs12 Hres HPAY HPAK HROOM Ham Hfew Hprim HSITE Tok.
  apply (malloc_callT_gen_sec segs E AInv CST XGL ALA HCST HXGL NP Kc rho0 P0f FB FF BX PA HKc (etriple segs) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs)
           (call_completePA3 segs) false true (fun A r => alloc_roomA A (bv_unsigned (rw r 12%positive))) PA' W st Cl s R rho tp nd bd' Q); try assumption.
  - intros Ai rho1 tp1.
    apply (TRe_pureP segs _ (alloc_roomA Ai (bv_unsigned (rw rho1 12%positive)))); [intros w [_ [_ H]]; exact H|]. intros Hroom.
    apply (TRe_pre segs (SPA segs (J_alloc_pre AInv W st Ai Kc (SVar 12)) (Pre_malloc E W st) rho1 tp1)); [intros w [Hsm [HJ _]]; exact (conj Hsm HJ)|].
    apply (MSX W st Ai Kc rho1 tp1 HW HKc). intros tr md _. exact Hroom.
  - intros A ms kc HP Hkc HB. cbn beta. rewrite rw_call'. exact (HROOM A kc HP Hkc HB).
  -   intros Ai kc tr md HJ. destruct nd as [tv fr bd am]. cbn [nd_am nd_tv] in Ham, Hfew. subst am.
    pose proof (JAi_large_live_le0 segs AInv CST XGL ALA NP Kc rho0 P0f FB FF BX PA tv fr bd Ai kc rho tp tr md HJ) as LL. unfold sec_room. lia.
  -   intros Ai kc tr md HJ.
    pose proof (JAi_small_live_le AInv CST XGL NP Kc rho0 P0f FB FF BX PA nd Ai kc rho tp tr md HJ) as SL. unfold prim_room. lia.
  - intros E0. discriminate E0.
  - intros _. exact Tok.
Qed.
End Sum.
End WithSegs.
End DrvSiteS.

(* [comment removed for export] *)
Module Icpt_memcpy_hdr.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "true"; "bool"; "prod"; "app"; "Some"; "list"; "option"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "SLit"; "cell"; "mkCell"; "sobj"; "sprop"; "mkObj"; "DUnknown"; "SPUle"; "SAlu"; "SPAlign"; "sprop_below"; "FcsrFrm0"; "mkSS"; "ss_next"; "DImage"; "SPBranch"; "SPNot"; "SExt"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_hdr"; "tv"; "dst"; "src"; "E_dst"; "E_real"; "E_src"; "FT"; "R_dst"; "R_src"; "s_dst"; "s_src"; "vBd"; "vBs"; "P_icpt"; "R_real"; "X_mc"; "mid_state"; "s_real"; "vLd"; "vLs"; "E_dst_hi"; "E_dst_lo"; "E_src_hi"; "E_src_lo"; "FUELM"; "O_cstk"; "O_frame"; "O_real"; "O_rtc3"; "O_src"; "Pre_mc0"; "Pre_mc1"; "Pre_mc2"; "T1"; "T2"; "T3"; "base_mc"; "cutpcs_mc"; "hi_fact"; "lo_fact"; "objs_mc"; "opnd_facts"; "spm"; "vH"; "xor_facts"; "O_dst"; "O_dstH"; "T1r"; "T2r"; "T3r"; "cuts_mc"; "exits_mc"; "frame_cells"; "mid_regs"; "objs_mcH"; "ord1"; "ord2"; "vcuts_mc"; "vexits_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "vN"; "add"; "O_rtc2"; "P_ret"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "la_state"; "ax_S"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "ax_add_facts"; "check_cfgA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_XOR"; "BC_LTU"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full"; "Pre_rip"; "Pre_rip_lo"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "pre_regs"; "NPOST"; "post_regs"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "A_globals"; "segs"; "ACEIL"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_hdr.MCAddr"; "musl_memcpy"; "mc_entry"; "mc_ret"; "ra_dst"; "ra_real"; "ra_src"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.RegionAddr"; "rip_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "Pre_mhA"; "Posts_mhA"; "liftA"; "memcpy_entryA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpyHdr"; "P_mh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv MuslMemcpy MuslMemcpyHdr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import RegionAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module MCAddr.
  Definition mc_entry : Z := 0x5d6d8.
  Definition mc_ret : Z := 0x5d808.
  Definition ra_src : Z := 0x5da88.
  Definition ra_dst : Z := 0x5db84.
  Definition ra_real : Z := 0x5d7d8.
  Definition ls_head : Z := 0x5da58.
  Definition ld_head : Z := 0x5db58.
  Definition musl_memcpy : Z := 0xddf74.
End MCAddr.
Import MCAddr.

Definition vBd := SVar 15. Definition vLd := SVar 16. Definition vOd := SVar 17.
Definition vBs := SVar 19. Definition vLs := SVar 52. Definition vOs := SVar 53.
Definition dst : sv := vBd.
Definition src : sv := vBs.
Definition vH : sv := SVar 54.
Definition lasts : sv := ltac2:(tb__ "0|0|
S5fS5fS25S5eA2SfN1A1A2").
Definition lastd : sv := ltac2:(tb__ "0|0|
S5fS5fS24S5eA2SfN1A1A2").
Definition X_mc : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6SdSdA2M0S1SdSdS2eS35A4S0G0S1SdSdS2fS36A4S3G0A1A3A3").

Definition O_rtc3 : sobj := ltac2:(tb__ "0|3|
S14SfZ0A1SfZf20d8A1M0SfZf20daA1S0S10S11G0Z1M1SfG1A1M2A3S0S10S11SfZf20d9A1G1G2A3S3S10A1A3A3S15A5").
Definition O_real : sobj := ltac2:(tb__ "0|1|
S14SfZ0A1SfZe9ae8A1M0SfZe9af0A1S0S10S11G0Z8SfS86A1A3S3S10A1A3S15A5").

Definition frame_cells : list cell := ltac2:(tb__ "0|1|
S0S10S11SfN50A1Z8M0SeP2cA1A3S0S10S11SfN48A1G0SeP2bA1A3S0S10S11SfN40A1G0SeP2aA1A3S0S10S11SfN38A1G0SeP29A1A3S0S10S11SfN30A1G0SeP28A1A3S0S10S11SfN28A1G0SeP27A1A3S0S10S11SfN20A1G0SeP26A1A3S0S10S11SfN18A1G0SeP1dA1A3S0S10S11SfN10A1G0SeP1cA1A3S0S10S11SfN8A1G0SePbA1A3S3S10A1A3A3A3A3A3A3A3A3A3A3").
Definition O_frame (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S14SePaA1SfN870A1SfZ0A1Vcs;S15A5").
Definition spm : sv := add (SVar 10) (SLit (-2160)).
Definition O_cstk : sobj := ltac2:(tb__ "0|0|
S14S4dSfN50A1SfZ0A1S3S10A1S15A5").
Definition O_dst : sobj := ltac2:(tb__ "0|0|
S14S24SfZ0A1S5eS3S10A1S15A5").
Definition O_src : sobj := ltac2:(tb__ "0|1|
S14S25SfZ0A1M0S5eS0S10S11G0Z4S4eA3S3S10A1A3S15A5").
Definition O_dstH : sobj := ltac2:(tb__ "0|1|
S14S24SfZ0A1M0S5eS0S10S11G0Z4S20S4Q20S4eA3A3S3S10A1A3S15A5").
Definition objs_mc (fr : list cell) : list sobj := ltac2:(tb__ "0|0|
S7S12S0S12S3dVfr;A1S0S12S3cS0S12S50S0S12S40S0S12S3fS0S12S60S0S12S3eS3S12A1A3A3A3A3A3A3A3S82A3").
Definition objs_mcH : list sobj := ltac2:(tb__ "0|0|
S7S12S0S12S3dS3S10A1A1S0S12S3cS0S12S51S0S12S40S0S12S3fS0S12S60S0S12S3eS3S12A1A3A3A3A3A3A3A3S82A3").

Definition opnd_facts (vB vL : sv) (b : positive) : list sprop := ltac2:(tb__ "0|2|
S0S13S16S5eVvL;A2S0S13S16VvL;SfS70Z2M0Z28A2A1A2S0S13S16SfZ1000A1VvB;A2S0S13S16S5fVvB;VvL;A2SfS72S70G0Z2fA2Z8A2A1M1A2S0S13S16VvB;G1A2S0S13S18Vb;Z3A2S0S13S18Vb;G0A2S3S13A1A3A3A3A3A3A3A3").
Definition hi_fact (vB : sv) : sprop := SPUle (SLit HSE) vB.
Definition lo_fact (vB vL : sv) : sprop := ltac2:(tb__ "0|0|
S16S5fVvB;VvL;A2SfS72S85Z8A2A1A2").
Definition base_mc : list sprop := ltac2:(tb__ "0|4|
S7S13S4cS2eS35PfA3S7S13S4cS2fS36P13A3S0S13S16SfZ41A1S5eA2S0S13S16S5eSfS70Z2M0Z28A2A1A2S0S13S18P12Z4M1A2S0S13S18PaM2G1A2S0S13S16SfS71S84Z1000A2A1SeG2A1M3A2S0S13S16G3SfS70G0Z3fA2A1A2S3S13A1A3A3A3A3A3A3A3A3").

Definition xor_facts : list sprop := ltac2:(tb__ "0|1|
S0S13S1fS1eS6fS17S6eS25SfZffffffffffffffffA1M0A3S5eA3A1S0S13S1fS1eS6fS17S6eS24G0A3S5eA3A1S3S13A1A3A3").
Definition ord1 : sprop := ltac2:(tb__ "0|0|
S16S5fS24S5eA2S25A2").
Definition ord2 : sprop := ltac2:(tb__ "0|0|
S16S5fS25S5eA2S24A2").
Definition FT : list sprop := xor_facts ++ base_mc.

Definition Pre_mc0 : axst := ltac2:(tb__ "0|1|
S81S1bS87S7cS7dS0S6S2SdA2M0S1S2SdUaS24A4S0G0S1S2SdUbS25A4S0G0S1S2SdUcS5eA4S3G0A1A3A3A3A2S7bS1aSbSdA1S4bS3S10A1A1S47S7aScA9S32A2").
Definition Pre_mc1 : axst := ltac2:(tb__ "0|0|
S6bS0S13S5aS4fA3S41A2").
Definition Pre_mc2 : axst := ltac2:(tb__ "0|0|
S6bS0S13S5bS4fA3S41A2").

Definition P_icpt : axst := ltac2:(tb__ "0|1|
S81S1bS88S7cS7fS7aA1S0S6S2SdA2M0S1S2SdUaS24A4S3G0A1A3A2S7bS1aSbSdA1S59S47S7eScA9S32A2").
Definition Posts_mc : list leafA := ltac2:(tb__ "0|0|
S0S65S68S30S91A2S3S65A1A3").

Definition tv (k : nat) : sv := SVar (Pos.of_nat (150 + k)).
Definition mid_regs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|19|
S7cS7dS7S6S2SdA2M0S0G0S1S2SdU1M1S23G1A1A4S0G0S1S2SdU2S4dA4S0G0S1S2SdU5M2S23G2A1A4S0G0S1S2SdU6M3S23G3A1A4S0G0S1S2SdU7M4S23G4A1A4S0G0S1S2SdU8SePaA1M5A4S0G0S1S2SdU9M6S23G6A1A4S0G0S1S2SdUaM7S23G7A1A4S0G0S1S2SdUbM8S23G8A1A4S0G0S1S2SdUcM9S23G9A1A4S0G0S1S2SdUdMaS23GaA1A4S0G0S1S2SdUeMbS23GbA1A4S0G0S1S2SdUfMcS23GcA1A4S0G0S1S2SdU10MdS23GdA1A4S0G0S1S2SdU11MeS23GeA1A4S0G0S1S2SdU12MfS23GfA1A4S0G0S1S2SdU13M10S23G10A1A4S0G0S1S2SdU14M11S23G11A1A4S0G0S1S2SdU15S5fG5SfN868A1A2A4S0G0S1S2SdU16M12S23G12A1A4S0G0S1S2SdU17M13S23G13A1A4S0G0S1S2SdU18M14S23G14A1A4S0G0S1S2SdU1cM15S23G15A1A4S0G0S1S2SdU1dM16S23G16A1A4S0G0S1S2SdU1eM17S23G17A1A4S0G0S1S2SdU1fM18S23G18A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").
Definition mid_state (pc : Z) (l : list (nat * sv)) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
S81S1bVpc;S58Vl;A1S7bS1aSbSdA1S4bS57A1S7S13Vfacts;S29A3PbeScA9S32A2").

Definition E_src : axst := ltac2:(tb__ "0|1|
S33S8cS0S6S2SdA2M0S1S2SdU1SfS8bA1A4S0G0S1S2SdUaS25A4S0G0S1S2SdUbS5eA4S0G0S1S2SdU9S5eA4S0G0S1S2SdU14S5fS24S5eA2A4S0G0S1S2SdU16S5fS5eSfN41A1A2A4S0G0S1S2SdU17S24A4S0G0S1S2SdU18S25A4S3G0A1A3A3A3A3A3A3A3A3S3S13A1A3").

Definition E_dst : axst := ltac2:(tb__ "0|1|
S33S8cS0S6S2SdA2M0S1S2SdU1SfS89A1A4S0G0S1S2SdUaS24A4S0G0S1S2SdUbS5eA4S0G0S1S2SdU9S24A4S0G0S1S2SdU16S25A4S0G0S1S2SdU12S5eA4S3G0A1A3A3A3A3A3A3S3S13A1A3").

Definition E_src_hi : axst := ltac2:(tb__ "0|0|
S6bS0S13S49S2fA1S3S13A1A3S28A2").
Definition E_src_lo : axst := ltac2:(tb__ "0|0|
S6bS0S13S4aS2fS36A2S3S13A1A3S28A2").
Definition E_dst_hi : axst := ltac2:(tb__ "0|0|
S6bS0S13S49S2eA1S3S13A1A3S26A2").
Definition E_dst_lo : axst := ltac2:(tb__ "0|0|
S6bS0S13S4aS2eS35A2S3S13A1A3S26A2").

Definition E_real : axst := ltac2:(tb__ "0|1|
S33S86S0S6S2SdA2M0S1S2SdU1SfS8aA1A4S0G0S1S2SdUaS24A4S0G0S1S2SdUbS25A4S0G0S1S2SdUcS5eA4S3G0A1A3A3A3A3S3S13A1A3").

Definition s_src : wsub := ltac:(let x := eval vm_compute in ((15%positive, vBs) :: (17%positive, SLit 0) :: (16%positive, vLs) :: infer_sub 1 (ax_S E_src) (ax_S Pre_rip)) in exact x).
Definition s_dst : wsub := ltac:(let x := eval vm_compute in ((15%positive, vBd) :: (17%positive, SLit 0) :: (16%positive, vLd) :: infer_sub 1 (ax_S E_dst) (ax_S Pre_rip)) in exact x).
Definition s_real : wsub := ltac:(let x := eval vm_compute in ((16%positive, vH) :: infer_sub 1 (ax_S E_real) (ax_S Pre_mhA)) in exact x).
Definition R_src : list sobj := ltac:(let x := eval vm_compute in (match entails_frA E_src_hi Pre_rip s_src with Some R => R | None => [] end) in exact x).
Definition R_dst : list sobj := ltac:(let x := eval vm_compute in (match entails_frA E_dst_hi Pre_rip s_dst with Some R => R | None => [] end) in exact x).
Definition R_real : list sobj := ltac:(let x := eval vm_compute in (match entails_frA E_real Pre_mhA s_real with Some R => R | None => [] end) in exact x).

Lemma fr_src_hi : ltac2:(tb__ "0|1|
S62SaS9S12A1M0A1S77S39S73S2dA3S8G0S2bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_src_lo : ltac2:(tb__ "0|1|
S62SaS9S12A1M0A1S77S3aS74S2dA3S8G0S2bA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_dst_hi : ltac2:(tb__ "0|1|
S62SaS9S12A1M0A1S77S37S73S2cA3S8G0S2aA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_dst_lo : ltac2:(tb__ "0|1|
S62SaS9S12A1M0A1S77S38S74S2cA3S8G0S2aA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_real : ltac2:(tb__ "0|1|
S62SaS9S12A1M0A1S77S27S8dS34A3S8G0S31A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_src_hi : ltac2:(tb__ "0|0|
S62S5S76S39S73S2dS2bS75S65S64S66S79A4A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_src_lo : ltac2:(tb__ "0|0|
S62S5S76S3aS74S2dS2bS75S65S64S66S79A4A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_dst_hi : ltac2:(tb__ "0|0|
S62S5S76S37S73S2cS2aS75S65S64S66S79A4A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_dst_lo : ltac2:(tb__ "0|0|
S62S5S76S38S74S2cS2aS75S65S64S66S79A4A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_real : ltac2:(tb__ "0|0|
S62S5S76S27S8dS34S31S75S65S64S66S8eA4A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition T1r : axst := ltac2:(tb__ "0|0|
S78S2dS73S61S28S2bA5").
Definition T2r : axst := ltac2:(tb__ "0|0|
S78S2cS73S61S26S2aA5").
Definition T3r : axst := ltac2:(tb__ "0|0|
S78S34S8dS8fS92S90A1A1S27S31A5").
Definition T1 : axst := ax_add_facts FT T1r.
Definition T2 : axst := ax_add_facts FT T2r.
Definition T3 : axst := ax_add_facts FT T3r.

Definition cuts_mc : list axst := ltac2:(tb__ "0|0|
S0S64S42S0S64S43S0S64S44S0S64S45S0S64S46S3S64A1A3A3A3A3A3").
Definition exits_mc : list axst := ltac2:(tb__ "0|0|
S0S64S30S0S64S28S0S64S26S0S64S27S3S64A1A3A3A3A3").
Definition cutpcs_mc : list Z := ltac2:(tb__ "0|0|
S0S22S8cS0S22S86S3S22A1A3A3").
Definition FUELM : nat := 800%nat.

Definition vcuts_mc : list vnodeA := ltac2:(tb__ "0|4|
S0S69S6aS42Zc8M0SfZ0A1M1A3S0S69S6aS43G0G1A3S0S69S6aS44Z77SfS70Z2M2Z3dA2A1A3S0S69S6aS45Z4fSfS70G2Z3fA2M3A1A3S0S69S6aS46Z27SfS71G3Z8A2A1A3S3S69A1A3A3A3A3A3").
Definition vexits_mc : list vnodeA := ltac2:(tb__ "0|2|
S0S69S6aS30Z0SfS72S70Z2M0Z40A2Z1A2A1A3S0S69S6aS28Z78SfS70G0Z3dA2A1A3S0S69S6aS26Z50SfS70G0Z3fA2M1A1A3S0S69S6aS27Z28SfS71G1Z8A2A1A3S3S69A1A3A3A3A3").

Lemma echeck_mc : ltac2:(tb__ "0|0|
S62S5S93S83S3bS48S7aS5cS5dA6S4A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma check_mc : ltac2:(tb__ "0|0|
S62S5S6cS83S3bS48S7aS55S56A6S4A3").
Proof. exact (check_cfgA_of_ecfgIA segs FUELM cutpcs_mc NF vcuts_mc vexits_mc cuts_mc exits_mc eq_refl eq_refl echeck_mc). Qed.

Lemma FT_below_E : ltac2:(tb__ "0|0|
S62S5S80S13S19P64A1S29A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FT_below_T : ltac2:(tb__ "0|0|
S63S62S5S80S13S19S1cS67S52A1A1A1S29A3S4A3S63S62S5S80S13S19S1cS67S53A1A1A1S29A3S4A3S62S5S80S13S19S1cS67S54A1A1A1S29A3S4A3A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Icpt_memcpy_hdr.

(* [comment removed for export] *)
Module Icpt_memcpy.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "bool"; "true"; "prod"; "app"; "Some"; "list"; "option"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "SLit"; "cell"; "sprop"; "mkCell"; "sobj"; "mkObj"; "DUnknown"; "SAlu"; "SPUle"; "sprop_below"; "SPBranch"; "ss_next"; "SPNot"; "FcsrFrm0"; "mkSS"; "DImage"; "SPAlign"; "SPEq"; "SPUlt"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "vN"; "add"; "shp"; "P_ret"; "g8"; "shpk"; "O_rtc2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy"; "tv"; "dst"; "cur"; "src"; "gl"; "mid_state"; "gs"; "vBd"; "vBs"; "E_real"; "FT"; "F_L"; "vLd"; "vLs"; "E_dst"; "E_src"; "F8of"; "R_dst"; "R_src"; "s_dst"; "s_src"; "CLd_0"; "CLs_0"; "R_real"; "lastd"; "lasts"; "s_real"; "E_Ld_bk"; "E_Ld_in"; "E_Ls_bk"; "E_Ls_in"; "P_icpt"; "X_mc"; "ld_regs"; "ls_regs"; "objs_mc"; "CLd"; "CLs"; "E_dst_hi"; "E_dst_lo"; "E_src_hi"; "E_src_lo"; "FUELM"; "Pre_mc0"; "Pre_mc1"; "Pre_mc2"; "T1"; "T2"; "T3a"; "T3b"; "base_mc"; "cutpcs_mc"; "hi_fact"; "lo_fact"; "opnd_facts"; "s_Ld_bk"; "s_Ld_in"; "s_Ls_bk"; "s_Ls_in"; "spm"; "xor_facts"; "O_cstk"; "O_dst"; "O_frame"; "O_real"; "O_rtc3"; "O_src"; "T1r"; "T2r"; "T3ar"; "T3br"; "cuts_mc"; "exits_mc"; "frame_cells"; "mid_regs"; "ord1"; "ord2"; "vOd"; "vOs"; "vcuts_mc"; "vexits_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "la_state"; "entailsA"; "mkLeafA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_XOR"; "BC_GEU"; "BC_LTU"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "ax_add_facts"; "check_cfgA"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "pre_regs"; "NPOST"; "post_regs"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full"; "Pre_rip"; "Pre_rip_lo"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy.MCAddr"; "ld_head"; "ls_head"; "musl_memcpy"; "mc_entry"; "mc_ret"; "ra_dst"; "ra_real"; "ra_src"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "Pre_memcpyA"; "liftA"; "memcpy_entryA"; "Posts_memcpyA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "segs"; "ACEIL"; "A_globals"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.RegionAddr"; "rip_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslMemcpy"; "P_retA"; "P_retB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv MuslMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import RegionAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module MCAddr.
  Definition mc_entry : Z := 0x5d6d8.
  Definition mc_ret : Z := 0x5d808.
  Definition ra_src : Z := 0x5da88.
  Definition ra_dst : Z := 0x5db84.
  Definition ra_real : Z := 0x5d7d8.
  Definition ls_head : Z := 0x5da58.
  Definition ld_head : Z := 0x5db58.
  Definition musl_memcpy : Z := 0xddf74.
End MCAddr.
Import MCAddr.

Definition vBd := SVar 15. Definition vLd := SVar 16. Definition vOd := SVar 17.
Definition vBs := SVar 19. Definition vLs := SVar 52. Definition vOs := SVar 53.
Definition dst : sv := add vBd vOd.
Definition src : sv := add vBs vOs.
Definition lasts : sv := ltac2:(tb__ "0|0|
S27S27S30S26A2SfN1A1A2").
Definition lastd : sv := ltac2:(tb__ "0|0|
S27S27S2eS26A2SfN1A1A2").
Definition X_mc : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6SdSdA2M0S1SdSdS34S39A4S0G0S1SdSdS35S3aA4S3G0A1A3A3").

Definition O_rtc3 : sobj := ltac2:(tb__ "0|3|
S14SfZ0A1SfZf20d8A1M0SfZf20daA1S0S10S12G0Z1M1SfG1A1M2A3S0S10S12SfZf20d9A1G1G2A3S3S10A1A3A3S15A5").
Definition O_real : sobj := ltac2:(tb__ "0|1|
S14SfZ0A1SfZe9ae8A1M0SfZe9af0A1S0S10S12G0Z8SfS9fA1A3S3S10A1A3S15A5").

Definition frame_cells : list cell := ltac2:(tb__ "0|1|
S0S10S12SfN50A1Z8M0SeP2cA1A3S0S10S12SfN48A1G0SeP2bA1A3S0S10S12SfN40A1G0SeP2aA1A3S0S10S12SfN38A1G0SeP29A1A3S0S10S12SfN30A1G0SeP28A1A3S0S10S12SfN28A1G0SeP27A1A3S0S10S12SfN20A1G0SeP26A1A3S0S10S12SfN18A1G0SeP1dA1A3S0S10S12SfN10A1G0SeP1cA1A3S0S10S12SfN8A1G0SePbA1A3S3S10A1A3A3A3A3A3A3A3A3A3A3").
Definition O_frame (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S14SePaA1SfN870A1SfZ0A1Vcs;S15A5").
Definition spm : sv := add (SVar 10) (SLit (-2160)).
Definition O_cstk : sobj := ltac2:(tb__ "0|0|
S14S68SfN50A1SfZ0A1S3S10A1S15A5").
Definition O_dst : sobj := ltac2:(tb__ "0|0|
S14S2eSfZ0A1S26S3S10A1S15A5").
Definition O_src : sobj := ltac2:(tb__ "0|0|
S14S30SfZ0A1S26S3S10A1S15A5").
Definition objs_mc (fr : list cell) : list sobj := ltac2:(tb__ "0|0|
S7S13S0S13S6cVfr;A1S0S13S6aS0S13S6bS0S13S6fS0S13S6eS0S13S2cS0S13S6dS3S13A1A3A3A3A3A3A3A3SaeA3").

Definition opnd_facts (vB vL vO : sv) (b : positive) : list sprop := ltac2:(tb__ "0|2|
S0S11S17S27VvO;S26A2VvL;A2S0S11S17VvO;VvL;A2S0S11S17S26VvL;A2S0S11S17VvL;SfS8dZ2M0Z28A2A1A2S0S11S17SfZ1000A1VvB;A2S0S11S17S27VvB;VvL;A2SfS8eS8dG0Z2fA2Z8A2A1M1A2S0S11S17VvB;G1A2S0S11S1fVb;Z3A2S3S11A1A3A3A3A3A3A3A3A3").
Definition hi_fact (vB : sv) : sprop := SPUle (SLit HSE) vB.
Definition lo_fact (vB vL : sv) : sprop := ltac2:(tb__ "0|0|
S17S27VvB;VvL;A2SfS8eSafZ8A2A1A2").
Definition base_mc : list sprop := ltac2:(tb__ "0|3|
S7S11S63S34S39S7aPfA4S7S11S63S35S3aS7bP13A4S0S11S17SfZ1A1S26A2S0S11S17S26SfS8dZ2M0Z28A2A1A2S0S11S1fPaM1Z4A2S0S11S17SfS8fSadZ1000A2A1SeG1A1M2A2S0S11S17G2SfS8dG0Z3fA2A1A2S3S11A1A3A3A3A3A3A3A3").

Definition xor_facts : list sprop := ltac2:(tb__ "0|1|
S0S11S1bS19S87S16S85S30SfZffffffffffffffffA1M0A3S26A3A1S0S11S1bS19S87S16S85S2eG0A3S26A3A1S3S11A1A3A3").
Definition ord1 : sprop := ltac2:(tb__ "0|0|
S17S27S2eS26A2S30A2").
Definition ord2 : sprop := ltac2:(tb__ "0|0|
S17S27S30S26A2S2eA2").
Definition FT : list sprop := xor_facts ++ base_mc.

Definition Pre_mc0 : axst := ltac2:(tb__ "0|1|
SabS1dSa0S92S93S0S6S2SdA2M0S1S2SdUaS2eA4S0G0S1S2SdUbS30A4S0G0S1S2SdUcS26A4S3G0A1A3A3A3A2S91S1cSbSdA1S50S3S10A1A1S5fS90ScA9S4dA2").
Definition Pre_mc1 : axst := ltac2:(tb__ "0|0|
S8bS0S11S78S69A3S58A2").
Definition Pre_mc2 : axst := ltac2:(tb__ "0|0|
S8bS0S11S79S69A3S58A2").

Definition P_icpt : axst := ltac2:(tb__ "0|1|
SabS1dSa1S92S95S90A1S0S6S2SdA2M0S1S2SdUaS2eA4S3G0A1A3A2S91S1cSbSdA1S50S3S10A1A1S5fS94ScA9S4dA2").
Definition Posts_mc : list leafA := ltac2:(tb__ "0|0|
S0S7fS83S4cSb1A2S3S7fA1A3").

Definition tv (k : nat) : sv := SVar (Pos.of_nat (150 + k)).
Definition mid_regs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|19|
S92S93S7S6S2SdA2M0S0G0S1S2SdU1M1S2dG1A1A4S0G0S1S2SdU2S68A4S0G0S1S2SdU5M2S2dG2A1A4S0G0S1S2SdU6M3S2dG3A1A4S0G0S1S2SdU7M4S2dG4A1A4S0G0S1S2SdU8SePaA1M5A4S0G0S1S2SdU9M6S2dG6A1A4S0G0S1S2SdUaM7S2dG7A1A4S0G0S1S2SdUbM8S2dG8A1A4S0G0S1S2SdUcM9S2dG9A1A4S0G0S1S2SdUdMaS2dGaA1A4S0G0S1S2SdUeMbS2dGbA1A4S0G0S1S2SdUfMcS2dGcA1A4S0G0S1S2SdU10MdS2dGdA1A4S0G0S1S2SdU11MeS2dGeA1A4S0G0S1S2SdU12MfS2dGfA1A4S0G0S1S2SdU13M10S2dG10A1A4S0G0S1S2SdU14M11S2dG11A1A4S0G0S1S2SdU15S27G5SfN868A1A2A4S0G0S1S2SdU16M12S2dG12A1A4S0G0S1S2SdU17M13S2dG13A1A4S0G0S1S2SdU18M14S2dG14A1A4S0G0S1S2SdU1cM15S2dG15A1A4S0G0S1S2SdU1dM16S2dG16A1A4S0G0S1S2SdU1eM17S2dG17A1A4S0G0S1S2SdU1fM18S2dG18A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").
Definition mid_state (pc : Z) (l : list (nat * sv)) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
SabS1dVpc;S77Vl;A1S91S1cSbSdA1S50S76A1S7S11Vfacts;S37A3PbeScA9S4dA2").

Definition E_src : axst := ltac2:(tb__ "0|1|
S32Sb0S0S6S2SdA2M0S1S2SdU1SfSa4A1A4S0G0S1S2SdUaS30A4S0G0S1S2SdUbS26A4S0G0S1S2SdU9S26A4S0G0S1S2SdU14S27S2eS26A2A4S0G0S1S2SdU16S27S26SfN41A1A2A4S0G0S1S2SdU17S2eA4S0G0S1S2SdU18S30A4S3G0A1A3A3A3A3A3A3A3A3S3S11A1A3").

Definition E_dst : axst := ltac2:(tb__ "0|1|
S32Sb0S0S6S2SdA2M0S1S2SdU1SfSa2A1A4S0G0S1S2SdUaS2eA4S0G0S1S2SdUbS26A4S0G0S1S2SdU9S2eA4S0G0S1S2SdU16S30A4S0G0S1S2SdU12S26A4S3G0A1A3A3A3A3A3A3S3S11A1A3").

Definition E_src_hi : axst := ltac2:(tb__ "0|0|
S8bS0S11S61S35A1S3S11A1A3S3cA2").
Definition E_src_lo : axst := ltac2:(tb__ "0|0|
S8bS0S11S62S35S3aA2S3S11A1A3S3cA2").
Definition E_dst_hi : axst := ltac2:(tb__ "0|0|
S8bS0S11S61S34A1S3S11A1A3S3bA2").
Definition E_dst_lo : axst := ltac2:(tb__ "0|0|
S8bS0S11S62S34S39A2S3S11A1A3S3bA2").

Definition E_real : axst := ltac2:(tb__ "0|1|
S32S9fS0S6S2SdA2M0S1S2SdU1SfSa3A1A4S0G0S1S2SdUaS2eA4S0G0S1S2SdUbS30A4S0G0S1S2SdUcS26A4S3G0A1A3A3A3A3S3S11A1A3").

Definition cur : sv := SVar 140. Definition gl : sv := SVar 141. Definition gs : sv := SVar 142.
Definition F8of (g : sv) (gi : positive) (e : sv) : list sprop := ltac2:(tb__ "0|1|
S0S11S17S2aVg;A1M0Ve;A2S0S11S17Ve;S27G0SfZ7A1A2A2S0S11S17Vg;SfS8eS8dZ2Z3dA2Z1A2A1A2S3S11A1A3A3A3").

Definition F_L (vB vL last : sv) : list sprop := ltac2:(tb__ "0|1|
S7S11S0S11S17VvB;S2aS2fA1M0A2S0S11S17S27G0SfZ8A1A2S27VvB;VvL;A2A2S0S11S20G0G0A2S0S11S17S2fSfS8eS8dZ2Z3dA2Z1A2A1A2S0S11S21S2fS31A2S3S11A1A3A3A3A3A3S3dS31P8dVlast;A3A3").

Definition ls_regs (a3 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S6S2SdA2M0S1S2SdUaS2eA4S0G0S1S2SdUbS30A4S0G0S1S2SdUcS26A4S0G0S1S2SdUdVa3;A4S0G0S1S2SdUeS28S31A1A4S0G0S1S2SdU14S27S2eS26A2A4S0G0S1S2SdU16S27S26SfN41A1A2A4S3G0A1A3A3A3A3A3A3A3").
Definition CLs_0 : axst := ltac2:(tb__ "0|0|
S32S9eS4fS28S2fA1A1S3S11A1A3").
Definition CLs : axst := ltac2:(tb__ "0|0|
S8bS38S35S3aS46A3S43A2").
Definition E_Ls_in : axst := ltac2:(tb__ "0|1|
S32S9eS4fS28S33A1M0A1S7S11S3dS33P8eS30A3S7S11S3dS31P8dS46A3S0S11S1bS19S86G0S28S31A1A3A1S3S11A1A3A3A3A3").
Definition E_Ls_bk : axst := ltac2:(tb__ "0|1|
S32S9eS4fS2bS2fZ1A2M0A1S7S11S38S35S3aS46A3S0S11S19S88G0S28S31A1A3S3S11A1A3A3A3").

Definition ld_regs (a3 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S6S2SdA2M0S1S2SdUaS2eA4S0G0S1S2SdUbS30A4S0G0S1S2SdUcS26A4S0G0S1S2SdUdVa3;A4S0G0S1S2SdUeS28S31A1A4S3G0A1A3A3A3A3A3").
Definition CLd_0 : axst := ltac2:(tb__ "0|0|
S32S9dS4eS28S2fA1A1S3S11A1A3").
Definition CLd : axst := ltac2:(tb__ "0|0|
S8bS38S34S39S45A3S42A2").
Definition E_Ld_in : axst := ltac2:(tb__ "0|1|
S32S9dS4eS28S33A1M0A1S7S11S3dS33P8eS2eA3S7S11S3dS31P8dS45A3S0S11S1bS19S86G0S28S31A1A3A1S3S11A1A3A3A3A3").
Definition E_Ld_bk : axst := ltac2:(tb__ "0|1|
S32S9dS4eS2bS2fZ1A2M0A1S7S11S38S34S39S45A3S0S11S19S88G0S28S31A1A3S3S11A1A3A3A3").

Definition s_src : wsub := ltac:(let x := eval vm_compute in ((16%positive, vLs) :: infer_sub 1 (ax_S E_src) (ax_S Pre_rip)) in exact x).
Definition s_dst : wsub := ltac:(let x := eval vm_compute in ((16%positive, vLd) :: infer_sub 1 (ax_S E_dst) (ax_S Pre_rip)) in exact x).
Definition s_real : wsub := ltac:(let x := eval vm_compute in (infer_sub 1 (ax_S E_real) (ax_S Pre_memcpyA)) in exact x).
Definition R_src : list sobj := ltac:(let x := eval vm_compute in (match entails_frA E_src_hi Pre_rip s_src with Some R => R | None => [] end) in exact x).
Definition R_dst : list sobj := ltac:(let x := eval vm_compute in (match entails_frA E_dst_hi Pre_rip s_dst with Some R => R | None => [] end) in exact x).
Definition R_real : list sobj := ltac:(let x := eval vm_compute in (match entails_frA E_real Pre_memcpyA s_real with Some R => R | None => [] end) in exact x).

Lemma fr_src_hi : ltac2:(tb__ "0|1|
S24SaS9S13A1M0A1S9bS55S97S41A3S8G0S3fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_src_lo : ltac2:(tb__ "0|1|
S24SaS9S13A1M0A1S9bS56S98S41A3S8G0S3fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_dst_hi : ltac2:(tb__ "0|1|
S24SaS9S13A1M0A1S9bS53S97S40A3S8G0S3eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_dst_lo : ltac2:(tb__ "0|1|
S24SaS9S13A1M0A1S9bS54S98S40A3S8G0S3eA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_real : ltac2:(tb__ "0|1|
S24SaS9S13A1M0A1S9bS36Sa6S47A3S8G0S44A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_src_hi : ltac2:(tb__ "0|0|
S24S4S9aS55S97S41S3fS99S7fS7eS81Sa5A4A5S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_src_lo : ltac2:(tb__ "0|0|
S24S4S9aS56S98S41S3fS99S7fS7eS81Sa5A4A5S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_dst_hi : ltac2:(tb__ "0|0|
S24S4S9aS53S97S40S3eS99S7fS7eS81Sa5A4A5S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_dst_lo : ltac2:(tb__ "0|0|
S24S4S9aS54S98S40S3eS99S7fS7eS81Sa5A4A5S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_real : ltac2:(tb__ "0|0|
S24S4S9aS36Sa6S47S44S99S7fS7eS81Sa9A4A5S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition T1r : axst := ltac2:(tb__ "0|0|
S9cS41S97S29S3cS3fA5").
Definition T2r : axst := ltac2:(tb__ "0|0|
S9cS40S97S29S3bS3eA5").
Definition T3ar : axst := ltac2:(tb__ "0|0|
S9cS47Sa6Sa7Sb2Sa8A1A1S36S44A5").
Definition T3br : axst := ltac2:(tb__ "0|0|
S9cS47Sa6Sa7Sb3Sa8A1A1S36S44A5").
Definition T1 : axst := ax_add_facts FT T1r.
Definition T2 : axst := ax_add_facts FT T2r.
Definition T3a : axst := ax_add_facts FT T3ar.
Definition T3b : axst := ax_add_facts FT T3br.

Definition cuts_mc : list axst := ltac2:(tb__ "0|0|
S0S7eS59S0S7eS5aS0S7eS5bS0S7eS5cS0S7eS5dS0S7eS5eS0S7eS52S0S7eS51S3S7eA1A3A3A3A3A3A3A3A3").
Definition exits_mc : list axst := ltac2:(tb__ "0|0|
S0S7eS4cS0S7eS3cS0S7eS3bS0S7eS36S0S7eS4bS0S7eS4aS0S7eS49S0S7eS48S3S7eA1A3A3A3A3A3A3A3A3").
Definition cutpcs_mc : list Z := ltac2:(tb__ "0|0|
S0S23Sb0S0S23S9fS0S23S9eS0S23S9dS3S23A1A3A3A3A3").
Definition FUELM : nat := 800%nat.

Definition vcuts_mc : list vnodeA := ltac2:(tb__ "0|6|
S0S89S8aS59Zc8M0SfZ0A1M1A3S0S89S8aS5aG0G1A3S0S89S8aS5bZ77SfS8dZ2M2Z3dA2A1A3S0S89S8aS5cZ4fSfS8dG2Z3fA2M3A1A3S0S89S8aS5dZ27M4SfS8fG3Z8A2A1M5A3S0S89S8aS5eG4G5A3S0S89S8aS52Z96S2fA3S0S89S8aS51Z64S27S2fSfS8dG2Z3eA2A1A2A3S3S89A1A3A3A3A3A3A3A3A3").
Definition vexits_mc : list vnodeA := ltac2:(tb__ "0|6|
S0S89S8aS4cZ0SfS8eS8dZ2M0Z40A2Z1M1A2A1A3S0S89S8aS3cZ78SfS8dG0Z3dA2A1A3S0S89S8aS3bZ50SfS8dG0Z3fA2M2A1A3S0S89S8aS36Z28SfS8fG2Z8A2A1A3S0S89S8aS4bZ97M3S33A3S0S89S8aS4aG3S27S2fSfG1A1A2A3S0S89S8aS49Z65M4S27S33SfS8dG0Z3eA2M5A1A2A3S0S89S8aS48G4S27S2fSfS8fG5G1A2A1A2A3S3S89A1A3A3A3A3A3A3A3A3").

Lemma echeck_mc : ltac2:(tb__ "0|0|
S24S4Sb4SacS57S60S90S7cS7dA6S5A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma check_mc : ltac2:(tb__ "0|0|
S24S4S8cSacS57S60S90S74S75A6S5A3").
Proof. exact (check_cfgA_of_ecfgIA segs FUELM cutpcs_mc NF vcuts_mc vexits_mc cuts_mc exits_mc eq_refl eq_refl echeck_mc). Qed.

Definition s_Ls_in : wsub := ltac2:(tb__ "0|1|
S0S6S22SdA2M0S1S22SdP8cS33A4S3G0A1A3").
Definition s_Ls_bk : wsub := ltac2:(tb__ "0|1|
S0S6S22SdA2M0S1S22SdP8cS27S2fSfZ1A1A2A4S3G0A1A3").
Definition s_Ld_in : wsub := ltac2:(tb__ "0|1|
S0S6S22SdA2M0S1S22SdP8cS33A4S3G0A1A3").
Definition s_Ld_bk : wsub := ltac2:(tb__ "0|1|
S0S6S22SdA2M0S1S22SdP8cS27S2fSfZ1A1A2A4S3G0A1A3").
Lemma ent_Ls_in : ltac2:(tb__ "0|0|
S24S4S82S4bS43S67A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Ls_bk : ltac2:(tb__ "0|0|
S24S4S82S4aS43S66A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Ld_in : ltac2:(tb__ "0|0|
S24S4S82S49S42S65A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Ld_bk : ltac2:(tb__ "0|0|
S24S4S82S48S42S64A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ids_mc : ltac2:(tb__ "0|0|
S25S24S4SaaS67S90A2S5A3S25S24S4SaaS66S90A2S5A3S25S24S4SaaS65S90A2S5A3S24S4SaaS64S90A2S5A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma FLs_below : ltac2:(tb__ "0|0|
S24S4S96S11S18S1aS80S43A1A1A1S38S35S3aS46A3A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FLd_below : ltac2:(tb__ "0|0|
S24S4S96S11S18S1aS80S42A1A1A1S38S34S39S45A3A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma FT_below_E : ltac2:(tb__ "0|0|
S24S4S96S11S18P64A1S37A3S5A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FT_below_T : ltac2:(tb__ "0|0|
S25S24S4S96S11S18S1aS80S70A1A1A1S37A3S5A3S25S24S4S96S11S18S1aS80S71A1A1A1S37A3S5A3S25S24S4S96S11S18S1aS80S72A1A1A1S37A3S5A3S24S4S96S11S18S1aS80S73A1A1A1S37A3S5A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Icpt_memcpy.

(* [comment removed for export] *)
Module Icpt_memcpy_rs.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "cons"; "pair"; "nat"; "nil"; "true"; "bool"; "prod"; "app"; "Some"; "list"; "option"; "None"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SVar"; "SLit"; "cell"; "sprop"; "mkCell"; "sobj"; "mkObj"; "DUnknown"; "SAlu"; "SPUle"; "sprop_below"; "SPBranch"; "ss_next"; "SPNot"; "FcsrFrm0"; "SPAlign"; "mkSS"; "DImage"; "SExt"; "SPEq"; "SPUlt"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region"; "vN"; "add"; "shp"; "O_rtc2"; "P_ret"; "g8"; "shpk"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_rs"; "tv"; "dst"; "cur"; "src"; "gl"; "mid_state"; "gs"; "vBd"; "vBs"; "E_real"; "FT"; "F_L"; "vLd"; "vLs"; "E_dst"; "E_src"; "F8of"; "R_dst"; "R_src"; "s_dst"; "s_src"; "CLd_0"; "CLs_0"; "R_real"; "lastd"; "lasts"; "s_real"; "E_Ld_bk"; "E_Ld_in"; "E_Ls_bk"; "E_Ls_in"; "P_icpt"; "X_mc"; "ld_regs"; "ls_regs"; "CLd"; "CLs"; "E_dst_hi"; "E_dst_lo"; "E_src_hi"; "E_src_lo"; "FUELM"; "O_cstk"; "O_frame"; "O_real"; "O_rtc3"; "O_src"; "Pre_mc0"; "Pre_mc1"; "Pre_mc2"; "T1"; "T2"; "T3a"; "T3b"; "base_mc"; "cutpcs_mc"; "hi_fact"; "lo_fact"; "objs_mc"; "opnd_facts"; "s_Ld_bk"; "s_Ld_in"; "s_Ls_bk"; "s_Ls_in"; "spm"; "vH"; "xor_facts"; "O_dst"; "O_dstH"; "T1r"; "T2r"; "T3ar"; "T3br"; "cuts_mc"; "exits_mc"; "frame_cells"; "mid_regs"; "objs_mcH"; "ord1"; "ord2"; "vOd"; "vOs"; "vcuts_mc"; "vexits_mc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "la_state"; "entailsA"; "mkLeafA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_XOR"; "BC_GEU"; "BC_LTU"; "BC_NE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "vnodeA"; "mkVNA"; "ax_add_facts"; "check_cfgA"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "sub"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "pre_fregs"; "setregs"; "pre_regs"; "NPOST"; "post_regs"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full"; "Pre_rip"; "Pre_rip_lo"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.ea.Icpt_memcpy_rs.MCAddr"; "ld_head"; "ls_head"; "musl_memcpy"; "mc_entry"; "mc_ret"; "ra_dst"; "ra_real"; "ra_src"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof"; "Posts_rip"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memcpyAH"; "Pre_ahA"; "P_ah1"; "P_ah2"; "Posts_ahA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code"; "mkA"; "A_globals"; "segs"; "ACEIL"; "SHB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region.RegionAddr"; "rip_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy"; "liftA"; "memcpy_entryA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsSymJump"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGlueA"; "check_ecfgIA"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundR SymComplete SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv MuslMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGlueA CfgEdgesA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fh.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fi.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require fj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require e4.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fh.Icpt_region OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fi.Icpt_region_proof OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.fj.Icpt_region_full OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.e4.Str_memcpyAH.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Import RegionAddr.
Close Scope bv_scope.
Open Scope Z_scope.

Module MCAddr.
  Definition mc_entry : Z := 0x5d6d8.
  Definition mc_ret : Z := 0x5d808.
  Definition ra_src : Z := 0x5da88.
  Definition ra_dst : Z := 0x5db84.
  Definition ra_real : Z := 0x5d7d8.
  Definition ls_head : Z := 0x5da58.
  Definition ld_head : Z := 0x5db58.
  Definition musl_memcpy : Z := 0xddf74.
End MCAddr.
Import MCAddr.

Definition vBd := SVar 15. Definition vLd := SVar 16. Definition vOd := SVar 17.
Definition vBs := SVar 19. Definition vLs := SVar 52. Definition vOs := SVar 53.
Definition vH := SVar 54.
Definition dst : sv := add vBd vOd.
Definition src : sv := add vBs vOs.
Definition lasts : sv := ltac2:(tb__ "0|0|
S28S28S31S27A2SfN1A1A2").
Definition lastd : sv := ltac2:(tb__ "0|0|
S28S28S2fS27A2SfN1A1A2").
Definition X_mc : list (sv * sv) := ltac2:(tb__ "0|1|
S0S6SdSdA2M0S1SdSdS35S3aA4S0G0S1SdSdS36S3bA4S3G0A1A3A3").

Definition O_rtc3 : sobj := ltac2:(tb__ "0|3|
S14SfZ0A1SfZf20d8A1M0SfZf20daA1S0S10S12G0Z1M1SfG1A1M2A3S0S10S12SfZf20d9A1G1G2A3S3S10A1A3A3S15A5").
Definition O_real : sobj := ltac2:(tb__ "0|1|
S14SfZ0A1SfZe9ae8A1M0SfZe9af0A1S0S10S12G0Z8SfSa3A1A3S3S10A1A3S15A5").

Definition frame_cells : list cell := ltac2:(tb__ "0|1|
S0S10S12SfN50A1Z8M0SeP2cA1A3S0S10S12SfN48A1G0SeP2bA1A3S0S10S12SfN40A1G0SeP2aA1A3S0S10S12SfN38A1G0SeP29A1A3S0S10S12SfN30A1G0SeP28A1A3S0S10S12SfN28A1G0SeP27A1A3S0S10S12SfN20A1G0SeP26A1A3S0S10S12SfN18A1G0SeP1dA1A3S0S10S12SfN10A1G0SeP1cA1A3S0S10S12SfN8A1G0SePbA1A3S3S10A1A3A3A3A3A3A3A3A3A3A3").
Definition O_frame (cs : list cell) : sobj := ltac2:(tb__ "0|0|
S14SePaA1SfN870A1SfZ0A1Vcs;S15A5").
Definition spm : sv := add (SVar 10) (SLit (-2160)).
Definition O_cstk : sobj := ltac2:(tb__ "0|0|
S14S6eSfN50A1SfZ0A1S3S10A1S15A5").
Definition O_dst : sobj := ltac2:(tb__ "0|0|
S14S2fSfZ0A1S27S3S10A1S15A5").
Definition O_src : sobj := ltac2:(tb__ "0|1|
S14S31SfZ0A1M0S27S0S10S12G0Z4S6fA3S3S10A1A3S15A5").
Definition O_dstH : sobj := ltac2:(tb__ "0|1|
S14S2fSfZ0A1M0S27S0S10S12G0Z4S20S4Q20S6fA3A3S3S10A1A3S15A5").
Definition objs_mc (fr : list cell) : list sobj := ltac2:(tb__ "0|0|
S7S13S0S13S59Vfr;A1S0S13S58S0S13S71S0S13S5cS0S13S5bS0S13S2aS0S13S5aS3S13A1A3A3A3A3A3A3A3Sb0A3").
Definition objs_mcH : list sobj := ltac2:(tb__ "0|0|
S7S13S0S13S59S3S10A1A1S0S13S58S0S13S72S0S13S5cS0S13S5bS0S13S2aS0S13S5aS3S13A1A3A3A3A3A3A3A3Sb0A3").

Definition opnd_facts (vB vL vO : sv) (b o : positive) : list sprop := ltac2:(tb__ "0|2|
S0S11S17S28VvO;S27A2VvL;A2S0S11S17VvO;VvL;A2S0S11S17S27VvL;A2S0S11S17VvL;SfS91Z2M0Z28A2A1A2S0S11S17SfZ1000A1VvB;A2S0S11S17S28VvB;VvL;A2SfS92S91G0Z2fA2Z8A2A1M1A2S0S11S17VvB;G1A2S0S11S1dVb;Z3A2S0S11S1dVo;G0A2S3S11A1A3A3A3A3A3A3A3A3A3").
Definition hi_fact (vB : sv) : sprop := SPUle (SLit HSE) vB.
Definition lo_fact (vB vL : sv) : sprop := ltac2:(tb__ "0|0|
S17S28VvB;VvL;A2SfS92Sb3Z8A2A1A2").
Definition base_mc : list sprop := ltac2:(tb__ "0|4|
S7S11S69S35S3aS7ePfP11A5S7S11S69S36S3bS7fP13P35A5S0S11S17SfZ4M0A1S27A2S0S11S17S27SfS91Z2M1Z28A2A1A2S0S11S1dPaM2G0A2S0S11S17SfS93Sb2Z1000A2A1SeG2A1M3A2S0S11S17G3SfS91G1Z3fA2A1A2S3S11A1A3A3A3A3A3A3A3").

Definition xor_facts : list sprop := ltac2:(tb__ "0|1|
S0S11S1bS19S8bS16S89S31SfZffffffffffffffffA1M0A3S27A3A1S0S11S1bS19S8bS16S89S2fG0A3S27A3A1S3S11A1A3A3").
Definition ord1 : sprop := ltac2:(tb__ "0|0|
S17S28S2fS27A2S31A2").
Definition ord2 : sprop := ltac2:(tb__ "0|0|
S17S28S31S27A2S2fA2").
Definition FT : list sprop := xor_facts ++ base_mc.

Definition Pre_mc0 : axst := ltac2:(tb__ "0|1|
SafS1eSa4S96S97S0S6S2SdA2M0S1S2SdUaS2fA4S0G0S1S2SdUbS31A4S0G0S1S2SdUcS27A4S3G0A1A3A3A3A2S95S1cSbSdA1S68S3S10A1A1S64S94ScA9S4eA2").
Definition Pre_mc1 : axst := ltac2:(tb__ "0|0|
S8fS0S11S7cS70A3S5dA2").
Definition Pre_mc2 : axst := ltac2:(tb__ "0|0|
S8fS0S11S7dS70A3S5dA2").

Definition P_icpt : axst := ltac2:(tb__ "0|1|
SafS1eSa5S96S99S94A1S0S6S2SdA2M0S1S2SdUaS2fA4S3G0A1A3A2S95S1cSbSdA1S7bS64S98ScA9S4eA2").
Definition Posts_mc : list leafA := ltac2:(tb__ "0|0|
S0S83S87S4dSb7A2S3S83A1A3").

Definition tv (k : nat) : sv := SVar (Pos.of_nat (150 + k)).
Definition mid_regs (l : list (nat * sv)) : list sv := ltac2:(tb__ "0|19|
S96S97S7S6S2SdA2M0S0G0S1S2SdU1M1S2eG1A1A4S0G0S1S2SdU2S6eA4S0G0S1S2SdU5M2S2eG2A1A4S0G0S1S2SdU6M3S2eG3A1A4S0G0S1S2SdU7M4S2eG4A1A4S0G0S1S2SdU8SePaA1M5A4S0G0S1S2SdU9M6S2eG6A1A4S0G0S1S2SdUaM7S2eG7A1A4S0G0S1S2SdUbM8S2eG8A1A4S0G0S1S2SdUcM9S2eG9A1A4S0G0S1S2SdUdMaS2eGaA1A4S0G0S1S2SdUeMbS2eGbA1A4S0G0S1S2SdUfMcS2eGcA1A4S0G0S1S2SdU10MdS2eGdA1A4S0G0S1S2SdU11MeS2eGeA1A4S0G0S1S2SdU12MfS2eGfA1A4S0G0S1S2SdU13M10S2eG10A1A4S0G0S1S2SdU14M11S2eG11A1A4S0G0S1S2SdU15S28G5SfN868A1A2A4S0G0S1S2SdU16M12S2eG12A1A4S0G0S1S2SdU17M13S2eG13A1A4S0G0S1S2SdU18M14S2eG14A1A4S0G0S1S2SdU1cM15S2eG15A1A4S0G0S1S2SdU1dM16S2eG16A1A4S0G0S1S2SdU1eM17S2eG17A1A4S0G0S1S2SdU1fM18S2eG18A1A4S3G0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3Vl;A3A2").
Definition mid_state (pc : Z) (l : list (nat * sv)) (facts : list sprop) : axst := ltac2:(tb__ "0|0|
SafS1eVpc;S7aVl;A1S95S1cSbSdA1S68S79A1S7S11Vfacts;S38A3PbeScA9S4eA2").

Definition E_src : axst := ltac2:(tb__ "0|1|
S33Sb4S0S6S2SdA2M0S1S2SdU1SfSa8A1A4S0G0S1S2SdUaS31A4S0G0S1S2SdUbS27A4S0G0S1S2SdU9S27A4S0G0S1S2SdU14S28S2fS27A2A4S0G0S1S2SdU16S28S27SfN41A1A2A4S0G0S1S2SdU17S2fA4S0G0S1S2SdU18S31A4S3G0A1A3A3A3A3A3A3A3A3S3S11A1A3").

Definition E_dst : axst := ltac2:(tb__ "0|1|
S33Sb4S0S6S2SdA2M0S1S2SdU1SfSa6A1A4S0G0S1S2SdUaS2fA4S0G0S1S2SdUbS27A4S0G0S1S2SdU9S2fA4S0G0S1S2SdU16S31A4S0G0S1S2SdU12S27A4S3G0A1A3A3A3A3A3A3S3S11A1A3").

Definition E_src_hi : axst := ltac2:(tb__ "0|0|
S8fS0S11S66S36A1S3S11A1A3S3dA2").
Definition E_src_lo : axst := ltac2:(tb__ "0|0|
S8fS0S11S67S36S3bA2S3S11A1A3S3dA2").
Definition E_dst_hi : axst := ltac2:(tb__ "0|0|
S8fS0S11S66S35A1S3S11A1A3S3cA2").
Definition E_dst_lo : axst := ltac2:(tb__ "0|0|
S8fS0S11S67S35S3aA2S3S11A1A3S3cA2").

Definition E_real : axst := ltac2:(tb__ "0|1|
S33Sa3S0S6S2SdA2M0S1S2SdU1SfSa7A1A4S0G0S1S2SdUaS2fA4S0G0S1S2SdUbS31A4S0G0S1S2SdUcS27A4S3G0A1A3A3A3A3S3S11A1A3").

Definition cur : sv := SVar 140. Definition gl : sv := SVar 141. Definition gs : sv := SVar 142.
Definition F8of (g : sv) (gi : positive) (e : sv) : list sprop := ltac2:(tb__ "0|1|
S0S11S17S2cVg;A1M0Ve;A2S0S11S17Ve;S28G0SfZ7A1A2A2S0S11S17Vg;SfS92S91Z2Z3dA2Z1A2A1A2S3S11A1A3A3A3").

Definition F_L (vB vL last : sv) : list sprop := ltac2:(tb__ "0|1|
S7S11S0S11S17VvB;S2cS30A1M0A2S0S11S17S28G0SfZ8A1A2S28VvB;VvL;A2A2S0S11S21G0G0A2S0S11S17S30SfS92S91Z2Z3dA2Z1A2A1A2S0S11S22S30S32A2S3S11A1A3A3A3A3A3S3eS32P8dVlast;A3A3").

Definition ls_regs (a3 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S6S2SdA2M0S1S2SdUaS2fA4S0G0S1S2SdUbS31A4S0G0S1S2SdUcS27A4S0G0S1S2SdUdVa3;A4S0G0S1S2SdUeS29S32A1A4S0G0S1S2SdU14S28S2fS27A2A4S0G0S1S2SdU16S28S27SfN41A1A2A4S3G0A1A3A3A3A3A3A3A3").
Definition CLs_0 : axst := ltac2:(tb__ "0|0|
S33Sa2S50S29S30A1A1S3S11A1A3").
Definition CLs : axst := ltac2:(tb__ "0|0|
S8fS39S36S3bS47A3S44A2").
Definition E_Ls_in : axst := ltac2:(tb__ "0|1|
S33Sa2S50S29S34A1M0A1S7S11S3eS34P8eS31A3S7S11S3eS32P8dS47A3S0S11S1bS19S8aG0S29S32A1A3A1S3S11A1A3A3A3A3").
Definition E_Ls_bk : axst := ltac2:(tb__ "0|1|
S33Sa2S50S2dS30Z1A2M0A1S7S11S39S36S3bS47A3S0S11S19S8cG0S29S32A1A3S3S11A1A3A3A3").

Definition ld_regs (a3 : sv) : list (nat * sv) := ltac2:(tb__ "0|1|
S0S6S2SdA2M0S1S2SdUaS2fA4S0G0S1S2SdUbS31A4S0G0S1S2SdUcS27A4S0G0S1S2SdUdVa3;A4S0G0S1S2SdUeS29S32A1A4S3G0A1A3A3A3A3A3").
Definition CLd_0 : axst := ltac2:(tb__ "0|0|
S33Sa1S4fS29S30A1A1S3S11A1A3").
Definition CLd : axst := ltac2:(tb__ "0|0|
S8fS39S35S3aS46A3S43A2").
Definition E_Ld_in : axst := ltac2:(tb__ "0|1|
S33Sa1S4fS29S34A1M0A1S7S11S3eS34P8eS2fA3S7S11S3eS32P8dS46A3S0S11S1bS19S8aG0S29S32A1A3A1S3S11A1A3A3A3A3").
Definition E_Ld_bk : axst := ltac2:(tb__ "0|1|
S33Sa1S4fS2dS30Z1A2M0A1S7S11S39S35S3aS46A3S0S11S19S8cG0S29S32A1A3S3S11A1A3A3A3").

Definition s_src : wsub := ltac:(let x := eval vm_compute in ((16%positive, vLs) :: infer_sub 1 (ax_S E_src) (ax_S Pre_rip)) in exact x).
Definition s_dst : wsub := ltac:(let x := eval vm_compute in ((16%positive, vLd) :: infer_sub 1 (ax_S E_dst) (ax_S Pre_rip)) in exact x).
Definition s_real : wsub := ltac:(let x := eval vm_compute in ((16%positive, vH) :: infer_sub 1 (ax_S E_real) (ax_S Pre_ahA)) in exact x).
Definition R_src : list sobj := ltac:(let x := eval vm_compute in (match entails_frA E_src_hi Pre_rip s_src with Some R => R | None => [] end) in exact x).
Definition R_dst : list sobj := ltac:(let x := eval vm_compute in (match entails_frA E_dst_hi Pre_rip s_dst with Some R => R | None => [] end) in exact x).
Definition R_real : list sobj := ltac:(let x := eval vm_compute in (match entails_frA E_real Pre_ahA s_real with Some R => R | None => [] end) in exact x).

Lemma fr_src_hi : ltac2:(tb__ "0|1|
S25SaS9S13A1M0A1S9fS55S9bS42A3S8G0S40A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_src_lo : ltac2:(tb__ "0|1|
S25SaS9S13A1M0A1S9fS56S9cS42A3S8G0S40A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_dst_hi : ltac2:(tb__ "0|1|
S25SaS9S13A1M0A1S9fS53S9bS41A3S8G0S3fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_dst_lo : ltac2:(tb__ "0|1|
S25SaS9S13A1M0A1S9fS54S9cS41A3S8G0S3fA2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma fr_real : ltac2:(tb__ "0|1|
S25SaS9S13A1M0A1S9fS37SaaS48A3S8G0S45A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_src_hi : ltac2:(tb__ "0|0|
S25S5S9eS55S9bS42S40S9dS83S82S85Sa9A4A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_src_lo : ltac2:(tb__ "0|0|
S25S5S9eS56S9cS42S40S9dS83S82S85Sa9A4A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_dst_hi : ltac2:(tb__ "0|0|
S25S5S9eS53S9bS41S3fS9dS83S82S85Sa9A4A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_dst_lo : ltac2:(tb__ "0|0|
S25S5S9eS54S9cS41S3fS9dS83S82S85Sa9A4A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma cc_real : ltac2:(tb__ "0|0|
S25S5S9eS37SaaS48S45S9dS83S82S85SadA4A5S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition T1r : axst := ltac2:(tb__ "0|0|
Sa0S42S9bS2bS3dS40A5").
Definition T2r : axst := ltac2:(tb__ "0|0|
Sa0S41S9bS2bS3cS3fA5").
Definition T3ar : axst := ltac2:(tb__ "0|0|
Sa0S48SaaSb5SabSb6A1A1S37S45A5").
Definition T3br : axst := ltac2:(tb__ "0|0|
Sa0S48SaaSb5SacSb6A1A1S37S45A5").
Definition T1 : axst := ax_add_facts FT T1r.
Definition T2 : axst := ax_add_facts FT T2r.
Definition T3a : axst := ax_add_facts FT T3ar.
Definition T3b : axst := ax_add_facts FT T3br.

Definition cuts_mc : list axst := ltac2:(tb__ "0|0|
S0S82S5eS0S82S5fS0S82S60S0S82S61S0S82S62S0S82S63S0S82S52S0S82S51S3S82A1A3A3A3A3A3A3A3A3").
Definition exits_mc : list axst := ltac2:(tb__ "0|0|
S0S82S4dS0S82S3dS0S82S3cS0S82S37S0S82S4cS0S82S4bS0S82S4aS0S82S49S3S82A1A3A3A3A3A3A3A3A3").
Definition cutpcs_mc : list Z := ltac2:(tb__ "0|0|
S0S24Sb4S0S24Sa3S0S24Sa2S0S24Sa1S3S24A1A3A3A3A3").
Definition FUELM : nat := 800%nat.

Definition vcuts_mc : list vnodeA := ltac2:(tb__ "0|6|
S0S8dS8eS5eZc8M0SfZ0A1M1A3S0S8dS8eS5fG0G1A3S0S8dS8eS60Z77SfS91Z2M2Z3dA2A1A3S0S8dS8eS61Z4fSfS91G2Z3fA2M3A1A3S0S8dS8eS62Z27M4SfS93G3Z8A2A1M5A3S0S8dS8eS63G4G5A3S0S8dS8eS52Z96S30A3S0S8dS8eS51Z64S28S30SfS91G2Z3eA2A1A2A3S3S8dA1A3A3A3A3A3A3A3A3").
Definition vexits_mc : list vnodeA := ltac2:(tb__ "0|6|
S0S8dS8eS4dZ0SfS92S91Z2M0Z40A2Z1M1A2A1A3S0S8dS8eS3dZ78SfS91G0Z3dA2A1A3S0S8dS8eS3cZ50SfS91G0Z3fA2M2A1A3S0S8dS8eS37Z28SfS93G2Z8A2A1A3S0S8dS8eS4cZ97M3S34A3S0S8dS8eS4bG3S28S30SfG1A1A2A3S0S8dS8eS4aZ65M4S28S34SfS91G0Z3eA2M5A1A2A3S0S8dS8eS49G4S28S30SfS93G5G1A2A1A2A3S3S8dA1A3A3A3A3A3A3A3A3").

Lemma echeck_mc : ltac2:(tb__ "0|0|
S25S5Sb8Sb1S57S65S94S80S81A6S4A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma check_mc : ltac2:(tb__ "0|0|
S25S5S90Sb1S57S65S94S77S78A6S4A3").
Proof. exact (check_cfgA_of_ecfgIA segs FUELM cutpcs_mc NF vcuts_mc vexits_mc cuts_mc exits_mc eq_refl eq_refl echeck_mc). Qed.

Definition s_Ls_in : wsub := ltac2:(tb__ "0|1|
S0S6S23SdA2M0S1S23SdP8cS34A4S3G0A1A3").
Definition s_Ls_bk : wsub := ltac2:(tb__ "0|1|
S0S6S23SdA2M0S1S23SdP8cS28S30SfZ1A1A2A4S3G0A1A3").
Definition s_Ld_in : wsub := ltac2:(tb__ "0|1|
S0S6S23SdA2M0S1S23SdP8cS34A4S3G0A1A3").
Definition s_Ld_bk : wsub := ltac2:(tb__ "0|1|
S0S6S23SdA2M0S1S23SdP8cS28S30SfZ1A1A2A4S3G0A1A3").
Lemma ent_Ls_in : ltac2:(tb__ "0|0|
S25S5S86S4cS44S6dA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Ls_bk : ltac2:(tb__ "0|0|
S25S5S86S4bS44S6cA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Ld_in : ltac2:(tb__ "0|0|
S25S5S86S4aS43S6bA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ent_Ld_bk : ltac2:(tb__ "0|0|
S25S5S86S49S43S6aA3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma ids_mc : ltac2:(tb__ "0|0|
S26S25S5SaeS6dS94A2S4A3S26S25S5SaeS6cS94A2S4A3S26S25S5SaeS6bS94A2S4A3S25S5SaeS6aS94A2S4A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma FLs_below : ltac2:(tb__ "0|0|
S25S5S9aS11S18S1aS84S44A1A1A1S39S36S3bS47A3A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FLd_below : ltac2:(tb__ "0|0|
S25S5S9aS11S18S1aS84S43A1A1A1S39S35S3aS46A3A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma FT_below_E : ltac2:(tb__ "0|0|
S25S5S9aS11S18P64A1S38A3S4A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma FT_below_T : ltac2:(tb__ "0|0|
S26S25S5S9aS11S18S1aS84S73A1A1A1S38A3S4A3S26S25S5S9aS11S18S1aS84S74A1A1A1S38A3S4A3S26S25S5S9aS11S18S1aS84S75A1A1A1S38A3S4A3S25S5S9aS11S18S1aS84S76A1A1A1S38A3S4A3A2A2A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
End Icpt_memcpy_rs.

