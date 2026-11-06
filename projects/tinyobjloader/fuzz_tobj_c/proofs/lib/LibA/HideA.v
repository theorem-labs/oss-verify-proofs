(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "list"; "prod"; "pair"; "nat"; "bool"; "fst"; "andb"; "negb"; "snd"; "true"; "nil"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sprop"; "valuation"; "sv"; "holds"; "sprop_below"; "SPNot"; "smatch"; "ss_facts"; "sstate"; "swf"; "mkSS"; "sprop_eqb"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_next"; "ss_objs"; "ss_pc"; "ss_regs"; "ss_resv"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_X"; "ax_base"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ndesc"; "edescA"; "edropA"; "emeasA"; "JA"; "ejcertA"; "enodeIA"; "nodeIA"; "ok_frameKA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF"; "efnode"; "fnode"; "efdrop"; "efmeasA"; "JAF"; "ejcertAF"; "enodeIAF"; "phiK"; "nodeIAF"; "phi_reads"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@Corelib.Init.Logic"; "eq"; "or"; "iff"; "not"; "@Stdlib.Lists.List"; "In"; "forallb"; "filter"; "existsb"; "@stdpp.bitvector.definitions"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "enodeA"; "jnodeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA"; "SPfamETA"; "SPfamGTA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.HideA"; "hideN"; "memf"; "hideE"; "hidef"; "hideA"; "hideFN"; "hideP"; "hideS"; "is_align"; "enode_facts"; "fnode_facts"; "node_facts"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "alloc_lawsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Stdlib.ZArith.BinInt.Z"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundR SymFrame SymEntail SymCFG SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA TobjJA TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h3.TobjJAFb.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition hidef (H : list sprop) (p : sprop) : sprop := ltac2:(tb__ "0|0|
S4SbL_;S46SbS16Vp;A1VH;A3S10S10Vp;A1A1Vp;X4x2").
Definition hideS (H : list sprop) (S : sstate) : sstate := ltac2:(tb__ "0|0|
S15S1cVS;A1S1dVS;A1S18VS;A1S17VS;A1S1eVS;A1S1bVS;A1S1fSbSbS52VH;A1S12VS;A1A4S1aVS;A1S19VS;A1A9").
Definition hideA (H : list sprop) (A : axst) : axst := ltac2:(tb__ "0|0|
S25S56VH;S22VA;A1A2S23VA;A1S24VA;A1A3").

Definition hideFN (H : list sprop) (n : fnode) : fnode := ltac2:(tb__ "0|2|
S2S1S21S26A2M0S3S2S21S26S53VH;S5S21S26S5G0S3Vn;A3M1A3A2S8S21S26G1A3A4S8G0S3Vn;A3A4").
Definition hideN (H : list sprop) (n : efnode) : efnode := ltac2:(tb__ "0|2|
S2S30S1S39SdA2M0S54VH;S5S1S1S21S26A2S3A2M1G0Vn;A3A2S8G1G0Vn;A3A4").

Definition hideP (H : list sprop) (n : axst * ndesc) : axst * ndesc := ltac2:(tb__ "0|0|
S2S21S26S53VH;S5S21S26Vn;A3A2S8S21S26Vn;A3A4").
Definition hideE (H : list sprop) (n : edescA) : edescA := ltac2:(tb__ "0|2|
S2S1S21S26A2M0S1S39SdA2M1S55VH;S5G0G1Vn;A3A2S8G0G1Vn;A3A4").

Definition memf (l : list sprop) (p : sprop) : bool := existsb (sprop_eqb p) l.
Definition is_align (p : sprop) : bool := match p with SPAlign _ _ => true | _ => false end.
Definition node_facts (n : efnode) : list sprop := ss_facts (ax_S (ef_state n)).
Definition hide_set (keep : list sprop) (nodes : list efnode) : list sprop := ltac2:(tb__ "0|1|
S0S2fA1M0S0SbA1Lnodes;Vnodes;SaSbA1S2fG0S45SbSbS6S6S7S57R1A1A1S7S50Vkeep;R1A2A1A2S44S2fS2fS50S5aR1A1R2A2Ln;R2A3A2Lp;S5aR2A1A3Lrest;Ln0;X0x2").

Definition enode_facts (n : edescA) : list sprop := ss_facts (ax_S (eda_state n)).
Definition hide_setE (keep : list sprop) (nodes : list edescA) : list sprop := ltac2:(tb__ "0|1|
S0S27A1M0S0SbA1Lnodes;Vnodes;SaSbA1S27G0S45SbSbS6S6S7S57R1A1A1S7S50Vkeep;R1A2A1A2S44S27S27S50S58R1A1R2A2Ln;R2A3A2Lp;S58R2A1A3Lrest;Ln0;X0x2").

Definition fnode_facts (n : fnode) : list sprop := ltac2:(tb__ "0|0|
S12S22S5S21S26S5S1S21S26A2S3Vn;A3A3A1A1").
Definition hide_setF (keep : list sprop) (nodes : list fnode) : list sprop := ltac2:(tb__ "0|1|
S0S30A1M0S0SbA1Lnodes;Vnodes;SaSbA1S30G0S45SbSbS6S6S7S57R1A1A1S7S50Vkeep;R1A2A1A2S44S30S30S50S59R1A1R2A2Ln;R2A3A2Lp;S59R2A1A3Lrest;Ln0;X0x2").

Lemma holds_dec : ltac2:(tb__ "0|1|
ScSbS40SeR2R1A2M0S42G0A1A2Fp;Frho;").
Proof.
  intros rho p. induction p; cbn.
  - destruct (branch_taken c (eval rho a) (eval rho b)); [left; reflexivity | right; discriminate].
  - tauto.
  - destruct (Z_lt_dec (bv_unsigned (eval rho a)) (bv_unsigned (eval rho b))); tauto.
  - destruct (Z_le_dec (bv_unsigned (eval rho a)) (bv_unsigned (eval rho b))); tauto.
  - destruct (decide (eval rho a = eval rho b)); tauto.
  - tauto.
  - destruct (Z_le_dec 0 a); [|tauto]. destruct (Z.eq_dec (bv_unsigned (rw rho i) mod 2 ^ a) 0); tauto.
Qed.

Lemma holds_hidef : ltac2:(tb__ "0|0|
ScS0SbA1SbS41SeR3S52R2R1A2A2SeR3R1A2A2Fp;FH;Frho;").
Proof.
  intros rho H p. unfold hidef. destruct (existsb (sprop_eqb p) H); [|tauto]. cbn. destruct (holds_dec rho p); tauto.
Qed.

Lemma Forall_holds_hide : ltac2:(tb__ "0|2|
ScS0SbA1M0G0S41S20SbSeR3A1M1S1fSbSbS52R2A1R1A4A3S20SbG1R1A3A2Fl;FH;Frho;").
Proof.
  intros rho H l. induction l as [|p l IH]; cbn [map].
  - split; intros; constructor.
  - split; intros X; inversion X; subst; constructor; try tauto; apply (holds_hidef rho H p); assumption.
Qed.

Lemma sprop_below_hidef : ltac2:(tb__ "0|0|
S3aS0SbA1SbS3fS4SfR3S52R2R1A2A2SfR3R1A2A3Fp;FH;Fn;").
Proof. intros n H p. unfold hidef. destruct (existsb (sprop_eqb p) H); reflexivity. Qed.

Lemma forallb_below_hide : ltac2:(tb__ "0|2|
S3aS0SbA1M0G0S3fS4S44SbSfR3A1M1S1fSbSbS52R2A1R1A4A3S44SbG1R1A3A3Fl;FH;Fn;").
Proof. intros n H l. induction l as [|p l IH]; [reflexivity|]. cbn [map forallb]. rewrite sprop_below_hidef, IH. reflexivity. Qed.

Lemma swf_hideS : ltac2:(tb__ "0|0|
S0SbA1S13S3fS4S14S56R2R1A2A1S14R1A1A3FS;FH;").
Proof. intros H S. unfold swf. cbn [hideS ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts]. rewrite forallb_below_hide. reflexivity. Qed.

Section WithSegs0.
Variable segs : list Segment.

Lemma smatch_hideS : ltac2:(tb__ "0|0|
ScS0SbA1S13S1S0S5dA1S5bA2S41S11Vsegs;R4S56R3R2A2R1A4S11Vsegs;R4R2R1A4A2Fw;FS;FH;Frho;").
Proof.
  intros rho H S w. unfold smatch. rewrite swf_hideS. cbn [hideS ss_pc ss_fcsr ss_resv ss_objs ss_facts].
  rewrite (Forall_holds_hide rho H (ss_facts S)). tauto.
Qed.

Lemma smatchA_hideA : ltac2:(tb__ "0|0|
ScS0S47Q40A1A1S0SbA1S21S1S0S5dA1S5bA2S41S4bVsegs;R5R4S53R3R2A2R1A5S4bVsegs;R5R4R2R1A5A2Fw;FA;FH;Ftp;Frho;").
Proof.
  intros rho tp H [S X b] w. unfold smatchA, hideA. cbn [ax_S ax_X ax_base].
  rewrite (smatch_hideS rho H S).
  assert (E1 : axwf (mkAX (hideS H S) X b) = axwf (mkAX S X b)) by reflexivity. rewrite E1.
  assert (E2 : shadow_ok rho (mkAX (hideS H S) X b) <-> shadow_ok rho (mkAX S X b)) by (unfold shadow_ok; cbn [ax_S ax_X ax_base hideS ss_objs]; tauto).
  rewrite E2. tauto.
Qed.

Lemma SPA_hideA : ltac2:(tb__ "0|0|
S4cS0SbA1S21ScS0S47Q40A1A1S3bS41S4aVsegs;R6S53R5R4A2R3R2R1A6S4aVsegs;R6R4R3R2R1A6A2Fw;Ftp;Frho;FA;FH;FJ;").
Proof. intros J H A rho tp w. unfold SPA. rewrite (smatchA_hideA rho tp H A w). tauto. Qed.
End WithSegs0.

Section WithSegs.
Variable segs : list Segment.
Variable AInv : ltac2:(tb__ "0|0|
S5fScS0S47Q40A1A1S5cOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S5eVsegs;VAInv;VCST;A3").
Section Sum.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S0S1S1S39S39A2S39A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.
Variable Phis : ltac2:(tb__ "0|0|
S0S1S0S3aA1ScOF_;A2A1").
Hypothesis HPhis : ltac2:(tb__ "0|3|
S20S1S0S3aA1M0ScOF_;M1A2M2G2S38S5G0G1R1A3S8G0G1R1A3A2Lp;VPhis;A3").

Local Notation enodeIAF := (enodeIAF AInv CST XGL NP Kc rho0 P0f FB FF BX PA Phis).
Local Notation nodeIAF := (nodeIAF AInv CST XGL NP Kc rho0 P0f FB FF BX PA Phis).
Local Notation JAF := (JAF AInv CST XGL NP Kc rho0 P0f FB FF BX PA).
Local Notation phiK := (phiK Phis).
Local Notation ejcertAF := (ejcertAF segs NP Phis).
Local Notation jcertAF := (jcertAF segs NP Phis).

Lemma map_efdrop_hideN : ltac2:(tb__ "0|0|
S0SbA1S0S2fA1S3fS0S30A1S1fS2fS30S31S1fS2fS2fS4fR2A1R1A4A4S1fS30S30S54R2A1S1fS2fS30S31R1A4A4A3Fl;FH;").
Proof. intros H l. rewrite !map_map. apply map_ext. intros [[[A nd] k] rv]. reflexivity. Qed.

Lemma efmeasA_hideN : ltac2:(tb__ "0|0|
S0SbA1S2fScS3fS39S32S4fR3R2A2R1A2S32R2R1A2A3Frho;Fn;FH;").
Proof. intros H [[[A nd] k] [r v]] rho. reflexivity. Qed.

Lemma SPfamGTA_hide : ltac2:(tb__ "0|1|
S0SbA1S0S30A1S3bS4eVsegs;S1fS30S49S37VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;VPhis;AcM0R2A4R1A3S4eVsegs;S1fS30S49G0S1fS30S30S54R4A1R3A4A4R2A3F_;Fw;Fcuts;FH;").
Proof using .
  intros H cuts w (T & J & rho & tp & Hin & HS). apply in_map_iff in Hin as ([[A nd] k] & E & Hin). cbn in E. injection E as <- <-.
  exists (hideA H A), (JAF (phiK k) nd), rho, tp. split.
  - apply in_map_iff. exists (hideA H A, nd, k). split; [reflexivity|]. apply in_map_iff. exists (A, nd, k). split; [reflexivity | exact Hin].
  - apply (SPA_hideA segs). exact HS.
Qed.

Lemma SPfamETA_hide : ltac2:(tb__ "0|1|
S0SbA1S0S2fA1S39S3bS4dVsegs;S1fS2fS48S35VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;VPhis;AcM0R3A4R2R1A4S4dVsegs;S1fS2fS48G0S1fS2fS2fS4fR5A1R4A4A4R3R2A4F_;Fw;Fb;Fcuts;FH;").
Proof using .
  intros H cuts b w (n & rho & tp & Hin & HS & Hm). apply in_map_iff in Hin as (d & <- & Hin).
  exists (enodeIAF (hideN H d)), rho, tp. split; [|split].
  - apply in_map_iff. exists (hideN H d). split; [reflexivity|]. apply in_map_iff. exists d. split; [reflexivity | exact Hin].
  - destruct d as [[[A nd] k] rv]. cbn [TobjJAF.enodeIAF ena_state ena_pred hideN hideFN fst snd ef_state ef_nd ef_k] in *.
    apply (SPA_hideA segs). exact HS.
  - destruct d as [[[A nd] k] [r v]]. exact Hm.
Qed.

Theorem cfg_sound_JAF_h : ltac2:(tb__ "0|7|
S0SbA1S3S0S39A1S3aS0S2fA1M0G0S3bOF_;S3eS2eVsegs;VKc;R2A3S3fS4S34Vsegs;VNP;VPhis;R8R7R6S1fS2fS2fS4fR9A1M1R5A4S1fS2fS2fG1R4A4A8S9A3S21S26S3ScS0S47Q40A1A1M2S43S1S1S21S26A2M3S3A2M4S2G3S3S2S21S26R5R4A4R3A4M5S1fS2fS30S31RaA4A3S3dVsegs;RaS4aVsegs;S33VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S36VPhis;R4A2R5AdR6R3R2A5M6S3bS40S4eVsegs;S1fS30S49S37VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;VPhis;AcS1fS2fS30S31RdA4A4R1A3RaR1A1A2Lw;A4F_;Ftp;Frho;FkX;FndX;FX;S21S26S3ScG2S43G4G5S1fS2fS30S31RcA4A3S3dVsegs;RbG6RaA4F_;Ftp;Frho;FkT;FndT;FT;F_;F_;F_;FQ;Fok;FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;FH;").
Proof using ALA HKc HPhis.
  intros H fuel cutpcs g cutsE exitsE ok Q Hok Hc Hexits T ndT kT rho tp HinT.
  pose proof (ejcertAF_jcertAF segs NP Phis fuel cutpcs g _ _ Hc) as Hj.
  rewrite !map_efdrop_hideN in Hj.
  eapply triple_conseq; [intros w Hw; exact (proj2 (SPA_hideA segs (JAF (phiK kT) ndT) H T rho tp w) Hw) | intros w Hw; exact Hw |].
  apply (cfg_sound_JAF segs AInv CST XGL ALA NP Kc rho0 P0f FB FF BX PA HKc Phis HPhis fuel cutpcs g
           (map (hideFN H) (map efdrop cutsE)) (map (hideFN H) (map efdrop exitsE)) ok Q Hok Hj).
  - intros X ndX kX rho' tp' HinX. apply in_map_iff in HinX as ([[X0 nd0] k0] & E & HinX0). cbn in E. injection E as <- <- <-.
    eapply triple_conseq; [| | exact (Hexits X0 nd0 k0 rho' tp' HinX0)].
    + intros w Hw. exact (proj1 (SPA_hideA segs (JAF (phiK k0) nd0) H X0 rho' tp' w) Hw).
    + intros w [Hf|Hq]; [left; apply SPfamGTA_hide; exact Hf | right; exact Hq].
  - apply in_map_iff. exists (T, ndT, kT). split; [reflexivity | exact HinT].
Qed.

Theorem cfg_complete_JAF_bh : ltac2:(tb__ "0|a|
S0SbA1S3S0S39A1S3aS0S2fA1M0G0S39S3bOF_;F_;S39S39S3bS60R3R2A2R5R4R2A2R6R4R3A2F_;F_;Fw;Fb';Fb;S3fS4S34Vsegs;VNP;VPhis;R7R6R5S1fS2fS2fS4fR8A1M1R4A4S1fS2fS2fG1R3A4A8S9A3S21S26S3S1S39SdA2M2ScS0S47Q40A1A1M3S43S1S1S1S21S26A2M4S3A2M5G2A2M6S2G5G2S2G4S3S2S21S26R6R5A4R4A4R3A4M7RaA3S3cVsegs;S4aVsegs;S33VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S36VPhis;R5A2R6AdR7R3R2A5M8S3bS40S4dVsegs;S1fS2fS48S35VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;VPhis;AcRdA4S32S2G5G2S2G4S3S2S21S26R8R7A4R6A4R5A4R4A2M9R1A4RbG9R1A2A2Lw;A3F_;Ftp;Frho;Frv;FkX;FndX;FX;S21S26S3G2ScG3S43G6G7RcA3S3cVsegs;G8RbS32S2G5G2S2G4S3S2S21S26R7R6A4R5A4R4A4R3A2A1A3F_;Ftp;Frho;Frv;FkT;FndT;FT;F_;F_;F_;FQ;FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;FH;").
Proof using ALA HKc HPhis.
  intros H fuel cutpcs g cutsE exitsE Q HQ Hc Hexits T ndT kT rv rho tp HinT.
  eapply etriple_conseq; [intros w Hw; exact (proj2 (SPA_hideA segs (JAF (phiK kT) ndT) H T rho tp w) Hw) | intros w Hw; exact Hw |].
  rewrite <- (efmeasA_hideN H (T, ndT, kT, rv) rho).
  refine (cfg_complete_JAF_b segs AInv CST XGL ALA NP Kc rho0 P0f FB FF BX PA HKc Phis HPhis fuel cutpcs g
            (map (hideN H) cutsE) (map (hideN H) exitsE) Q HQ Hc _ (hideA H T) ndT kT rv rho tp _).
  - intros X ndX kX rvX rho' tp' HinX. apply in_map_iff in HinX as ([[[X0 nd0] k0] rv0] & E & HinX0). cbn in E. injection E as <- <- <- <-.
    eapply etriple_conseq; [| | exact (Hexits X0 nd0 k0 rv0 rho' tp' HinX0)].
    + intros w Hw. exact (proj1 (SPA_hideA segs (JAF (phiK k0) nd0) H X0 rho' tp' w) Hw).
    + intros w [Hf|Hq]; [left | right; exact Hq]. apply SPfamETA_hide. exact Hf.
  - apply in_map_iff. exists (T, ndT, kT, rv). split; [reflexivity | exact HinT].
Qed.

Theorem cfg_complete_JAF_h : ltac2:(tb__ "0|9|
S0SbA1S3S0S39A1S3aS0S2fA1M0G0S3bOF_;S3fS4S34Vsegs;VNP;VPhis;R6R5R4S1fS2fS2fS4fR7A1M1R3A4S1fS2fS2fG1R2A4A8S9A3S21S26S3S1S39SdA2M2ScS0S47Q40A1A1M3S43S1S1S1S21S26A2M4S3A2M5G2A2M6S2G5G2S2G4S3S2S21S26R6R5A4R4A4R3A4M7R9A3S3cVsegs;S4aVsegs;S33VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S36VPhis;R5A2R6AdR7R3R2A5M8S3bS40S4dVsegs;S1fS2fS48S35VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;VPhis;AcRcA4S32S2G5G2S2G4S3S2S21S26R8R7A4R6A4R5A4R4A2R1A4RaR1A1A2Lw;A3F_;Ftp;Frho;Frv;FkX;FndX;FX;S21S26S3G2ScG3S43G6G7RbA3S3cVsegs;G8RaA3F_;Ftp;Frho;Frv;FkT;FndT;FT;F_;F_;FQ;FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;FH;").
Proof using ALA HKc HPhis.
  intros H fuel cutpcs g cutsE exitsE Q Hc Hexits T ndT kT rv rho tp HinT.
  exact (cfg_complete_JAF_bh H fuel cutpcs g cutsE exitsE (fun _ w => Q w) (fun b b' w _ Hq => Hq) Hc Hexits T ndT kT rv rho tp HinT).
Qed.
End Sum.
End WithSegs.

Section JAh.
Variable segs : list Segment.
Variable AInv : ltac2:(tb__ "0|0|
S5fScS0S47Q40A1A1S5cOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S0S1S1S39S39A2S39A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.
Hypothesis ALA : ltac2:(tb__ "0|0|
S5eVsegs;VAInv;VCST;A3").

Local Notation JA := (JA AInv CST XGL NP Kc rho0 P0f FB FF BX PA).
Local Notation nodeIA := (nodeIA AInv CST XGL NP Kc rho0 P0f FB FF BX PA).
Local Notation enodeIA := (enodeIA AInv CST XGL NP Kc rho0 P0f FB FF BX PA).
Local Notation ejcertA := (ejcertA segs NP).
Local Notation jcertA := (jcertA segs NP).

Lemma map_edropA_hideE : ltac2:(tb__ "0|1|
S0SbA1S0S27A1S3fS0S1S21S26A2M0A1S1fS27G0S28S1fS27S27S51R2A1R1A4A4S1fG0G0S55R2A1S1fS27G0S28R1A4A4A3Fl;FH;").
Proof. intros H l. rewrite !map_map. apply map_ext. intros [[A nd] rv]. reflexivity. Qed.

Lemma emeasA_hideE : ltac2:(tb__ "0|0|
S0SbA1S27ScS3fS39S29S51R3R2A2R1A2S29R2R1A2A3Frho;Fn;FH;").
Proof. intros H [[A nd] [r v]] rho. reflexivity. Qed.

Lemma SPfamGTA_hideP : ltac2:(tb__ "0|2|
S0SbA1S0S1S21S26A2M0A1S3bS4eVsegs;S1fG0S49S2dVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;AbM1R2A4R1A3S4eVsegs;S1fG0S49G1S1fG0G0S55R4A1R3A4A4R2A3F_;Fw;Fcuts;FH;").
Proof using .
  intros H cuts w (T & J & rho & tp & Hin & HS). apply in_map_iff in Hin as ([A nd] & E & Hin). cbn in E. injection E as <- <-.
  exists (hideA H A), (JA nd), rho, tp. split.
  - apply in_map_iff. exists (hideA H A, nd). split; [reflexivity|]. apply in_map_iff. exists (A, nd). split; [reflexivity | exact Hin].
  - apply (SPA_hideA segs). exact HS.
Qed.

Lemma SPfamETA_hideE : ltac2:(tb__ "0|1|
S0SbA1S0S27A1S39S3bS4dVsegs;S1fS27S48S2cVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;AbM0R3A4R2R1A4S4dVsegs;S1fS27S48G0S1fS27S27S51R5A1R4A4A4R3R2A4F_;Fw;Fb;Fcuts;FH;").
Proof using .
  intros H cuts b w (n & rho & tp & Hin & HS & Hm). apply in_map_iff in Hin as (d & <- & Hin).
  exists (enodeIA (hideE H d)), rho, tp. split; [|split].
  - apply in_map_iff. exists (hideE H d). split; [reflexivity|]. apply in_map_iff. exists d. split; [reflexivity | exact Hin].
  - destruct d as [[A nd] rv]. cbn [TobjJA.enodeIA ena_state ena_pred hideE hideP fst snd eda_state eda_nd] in *.
    apply (SPA_hideA segs). exact HS.
  - destruct d as [[A nd] [r v]]. exact Hm.
Qed.

Theorem cfg_sound_JA_h : ltac2:(tb__ "0|6|
S0SbA1S3S0S39A1S3aS0S27A1M0G0S3bOF_;S3eS2eVsegs;VKc;R2A3S3fS4S2bVsegs;VNP;R8R7R6S1fS27S27S51R9A1M1R5A4S1fS27S27G1R4A4A7S9A3S21S26ScS0S47Q40A1A1M2S43S1S21S26A2M3S2S21S26R4R3A4M4S1fS27G3S28R9A4A3S3dVsegs;R9S4aVsegs;S2aVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;R4AcR5R3R2A5M5S3bS40S4eVsegs;S1fG3S49S2dVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;AbS1fS27G3S28RcA4A4R1A3R9R1A1A2Lw;A4F_;Ftp;Frho;FndX;FX;S21S26ScG2S43G3G4S1fS27G3S28RbA4A3S3dVsegs;RaG5R9A4F_;Ftp;Frho;FndT;FT;F_;F_;F_;FQ;Fok;FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;FH;").
Proof using ALA HKc.
  intros H fuel cutpcs g cutsE exitsE ok Q Hok Hc Hexits T ndT rho tp HinT.
  pose proof (ejcertA_jcertA segs NP fuel cutpcs g _ _ Hc) as Hj.
  rewrite !map_edropA_hideE in Hj.
  eapply triple_conseq; [intros w Hw; exact (proj2 (SPA_hideA segs (JA ndT) H T rho tp w) Hw) | intros w Hw; exact Hw |].
  apply (cfg_sound_JA segs AInv CST XGL NP Kc rho0 P0f FB FF BX PA HKc ALA fuel cutpcs g
           (map (hideP H) (map edropA cutsE)) (map (hideP H) (map edropA exitsE)) ok Q Hok Hj).
  - intros X ndX rho' tp' HinX. apply in_map_iff in HinX as ([X0 nd0] & E & HinX0). cbn in E. injection E as <- <-.
    eapply triple_conseq; [| | exact (Hexits X0 nd0 rho' tp' HinX0)].
    + intros w Hw. exact (proj1 (SPA_hideA segs (JA nd0) H X0 rho' tp' w) Hw).
    + intros w [Hf|Hq]; [left; apply SPfamGTA_hideP; exact Hf | right; exact Hq].
  - apply in_map_iff. exists (T, ndT). split; [reflexivity | exact HinT].
Qed.

Theorem cfg_complete_JA_h : ltac2:(tb__ "0|8|
S0SbA1S3S0S39A1S3aS0S27A1M0G0S3bOF_;S3fS4S2bVsegs;VNP;R6R5R4S1fS27S27S51R7A1M1R3A4S1fS27S27G1R2A4A7S9A3S21S26S1S39SdA2M2ScS0S47Q40A1A1M3S43S1S1S21S26A2M4G2A2M5S2G4G2S2S21S26R5R4A4R3A4M6R8A3S3cVsegs;S4aVsegs;S2aVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;R5AcR6R3R2A5M7S3bS40S4dVsegs;S1fS27S48S2cVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;AbRbA4S29S2G4G2S2S21S26R7R6A4R5A4R4A2R1A4R9R1A1A2Lw;A3F_;Ftp;Frho;Frv;FndX;FX;S21S26G2ScG3S43G5G6RaA3S3cVsegs;G7R9A3F_;Ftp;Frho;Frv;FndT;FT;F_;F_;FQ;FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;FH;").
Proof using ALA HKc.
  intros H fuel cutpcs g cutsE exitsE Q Hc Hexits T ndT rv rho tp HinT.
  eapply etriple_conseq; [intros w Hw; exact (proj2 (SPA_hideA segs (JA ndT) H T rho tp w) Hw) | intros w Hw; exact Hw |].
  refine (cfg_complete_JA segs AInv CST XGL NP Kc rho0 P0f FB FF BX PA HKc ALA fuel cutpcs g
            (map (hideE H) cutsE) (map (hideE H) exitsE) Q Hc _ (hideA H T) ndT rv rho tp _).
  - intros X ndX rvX rho' tp' HinX. apply in_map_iff in HinX as ([[X0 nd0] rv0] & E & HinX0). cbn in E. injection E as <- <- <-.
    eapply etriple_conseq; [| | exact (Hexits X0 nd0 rv0 rho' tp' HinX0)].
    + intros w Hw. exact (proj1 (SPA_hideA segs (JA nd0) H X0 rho' tp' w) Hw).
    + intros w [Hf|Hq]; [left | right; exact Hq]. apply SPfamETA_hideE. exact Hf.
  - apply in_map_iff. exists (T, ndT, rv). split; [reflexivity | exact HinT].
Qed.
End JAh.
