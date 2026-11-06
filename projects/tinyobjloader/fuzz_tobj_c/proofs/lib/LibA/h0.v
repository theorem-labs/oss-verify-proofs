(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJA.
From Stdlib Require FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require AxXform.

(* [comment removed for export] *)
Module JcertCutA.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "nat"; "andb"; "option"; "app"; "false"; "negb"; "S"; "Some"; "cons"; "nil"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "axwf"; "leafA"; "sym_runA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "edgeA"; "cuts_edgesA"; "leaves_edgesA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "edescA"; "eda_state"; "eda_nd"; "eda_var"; "eecheckJA"; "ejcertA"; "nd_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.JcertCutA.C"; "cuts_okE"; "cut_okE"; "ejcert_hdr"; "etargets"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Lists.ListDef"; "map"; "@Stdlib.Lists.List"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "ss_lenient"; "ss_next"; "sv_below"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import TobjJA.
Import ListNotations.
Open Scope Z_scope.

Section C.
Variable segs : list Segment.
Variable NP : positive.

Definition cut_okE (fuel : nat) (cutpcs : list Z) (g : positive) (P : edgeA -> bool) (i : nat) (T : axst) (targets : list axst) : bool := ltac2:(tb__ "0|3|
S4S4S4S2aVg;S28S11VT;A1M0A1A2S8S27G0A1A1A2S12VT;A1A2S5S1S13A1M1A1S0Lx;S14Vsegs;Vfuel;Vcutpcs;VT;S2A5G1S5S1S15A1M2A1S0Lx;S17Vg;Vi;R1Vtargets;A4G2S26S15VP;R1A3Les;S7X5x2Lleaves;S7X5x2A2").

Fixpoint cuts_okE (fuel : nat) (cutpcs : list Z) (g : positive) (P : edgeA -> bool) (i : nat) (cuts targets : list axst) : bool :=
  match cuts with
  | [] => true
  | T :: rest => cut_okE fuel cutpcs g P i T targets && cuts_okE fuel cutpcs g P (S i) rest targets
  end.

Lemma cuts_okE_sound : ltac2:(tb__ "0|2|
S3S1S23A1S24S15S0F_;S1S10A1M0S3G0SdS0S1fR7R6R5R4R2R3R1A7S2A3SfS1S15A1M1G1SeSdS5G1A1S16Vsegs;R9R8R7R4R5R3A7SaG1R1A2A3SdS0S26S15R6R1A3S2A3A2Les;A2F_;Ftargets;Fi;Fcuts;FP;Fg;Fcutpcs;Ffuel;").
Proof.
  intros fuel cutpcs g P cuts. induction cuts as [|T rest IH]; intros i targets H.
  - exists []. split; reflexivity.
  - cbn [cuts_okE] in H. apply andb_prop in H as [HT Hrest]. unfold cut_okE in HT. apply andb_prop in HT as [Hwf HT].
    destruct (IH (S i) targets Hrest) as (es' & Hes' & HP').
    cbn [cuts_edgesA]. rewrite Hwf. cbn [negb].
    destruct (sym_runA segs fuel cutpcs T true) as [leaves|]; [|discriminate].
    destruct (leaves_edgesA g i leaves targets) as [es|]; [|discriminate].
    rewrite Hes'. exists (es ++ es'). split; [reflexivity|]. rewrite forallb_app, HT, HP'. reflexivity.
Qed.

Definition ejcert_hdr (cutsE : list edescA) : bool := ltac2:(tb__ "0|2|
S26S18S18S4S4S4S8S27S11S19R1A1A1M0A1A1S1eS28G0A1M1S1aR1A1A2A2S2aVNP;G1A2A2S29G1S1bR1A1A2A2Ln;VcutsE;A3").

Definition etargets (cutsE exitsE : list edescA) : list axst := ltac2:(tb__ "0|0|
S6S10S25S18S10S19VcutsE;A4S25S18S10S19VexitsE;A4A3").

Theorem ejcertA_of_cuts : ltac2:(tb__ "0|1|
S3S1S23A1S24S1S18A1M0G0SdS0S21R2A1S2A3SdS0S1fR6R5R4S1cVNP;S6S18R3R2A3A2U0S25S18S10S19R3A4S22R3R2A2A7S2A3SdS0S1dVsegs;VNP;R7R6R5R4R3A7S2A3F_;F_;FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;").
Proof.
  intros fuel cutpcs g cutsE exitsE Hh Hc. rewrite ejcertA_ref_eq. unfold ejcertA_ref. unfold ejcert_hdr in Hh. rewrite Hh. cbn [andb].
  unfold cfg_edgesA. destruct (cuts_okE_sound _ _ _ _ _ _ _ Hc) as (es & Hes & HP). unfold etargets in Hes. rewrite Hes. exact HP.
Qed.

Lemma cuts_okE_cons : ltac2:(tb__ "0|1|
S3S1S23A1S24S15S0F_;S3S10S1S10A1M0G0SdS0S20R8R7R6R5R4R3R1A7S2A3SdS0S1fR9R8R7R6S9R5A1R3R2A7S2A3SdS0S1fRaR9R8R7R6SbS10R5R4A3R3A7S2A3F_;F_;Ftargets;Frest;FT;Fi;FP;Fg;Fcutpcs;Ffuel;").
Proof. intros. cbn [cuts_okE]. rewrite H, H0. reflexivity. Qed.
Lemma cuts_okE_nil : ltac2:(tb__ "0|0|
S3S1S23A1S24S15S0F_;S3S1S10A1SdS0S1fR6R5R4R3R2ScS10A1R1A7S2A3Ftargets;Fi;FP;Fg;Fcutpcs;Ffuel;").
Proof. reflexivity. Qed.
End C.
End JcertCutA.

(* [comment removed for export] *)
Module TobjJAX.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "eval"; "sobj"; "sprop"; "ss_facts"; "holds"; "cell"; "ob_base"; "ob_dflt"; "obj_hi_of"; "obj_lo_of"; "ss_next"; "DUnknown"; "SLit"; "SPBranch"; "dflt_writable"; "ob_cells"; "obj_wf"; "odefault"; "sprop_eqb"; "ss_objs"; "@Corelib.Init.Datatypes"; "list"; "prod"; "Some"; "nat"; "option"; "snd"; "bool"; "fst"; "true"; "nil"; "@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "or"; "and"; "not"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "ND"; "ndesc"; "JA"; "JAi"; "nd_tv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Stdlib.Lists.List"; "nth_error"; "In"; "Forall2"; "existsb"; "forallb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "xr_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tnz"; "remove_nth"; "tvv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "@LinuxProcessSemantics.Riscv.Instr"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjUnbase"; "reshape_obj_at"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymObj SymEntail SymCFG SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import BudA CfgGenTA TobjJA AxXform.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.
Variable AInv : ltac2:(tb__ "0|0|
S42S1S16S32Q40A1A1S3dOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Section Sum.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S16S17S17S20S20A2S20A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.

Let JAi : ltac2:(tb__ "0|0|
S27S42S20S2cFkc;FAi;Fnd;") := ltac2:(tb__ "0|0|
S29VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JA : ltac2:(tb__ "0|0|
S27S2cFnd;") := ltac2:(tb__ "0|0|
S28VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").

Lemma In_remove_nth_or {T} : ltac2:(tb__ "0|0|
S16VT;A1S19VT;S2eVT;R1R3A3S22S21S1aVT;A1S2dVT;R4R3A3S18VT;R2A2A3S2eVT;R2S3aVT;R3R4A3A3A2F_;Fx;Fi;Fl;").
Proof using . clear. induction l as [|h r IH]; intros [|i] x H; cbn in *; try contradiction.
  - destruct H as [->|H]; [left; reflexivity | right; exact H].
  - destruct H as [->|H]; [right; left; reflexivity|]. destruct (IH i x H) as [E|E]; [left; exact E | right; right; exact E].
Qed.
Lemma JAi_drop_tv : ltac2:(tb__ "0|1|
S16S17S0S0A2M0A1S16S17S17S0S20A2S0A2A1S16S3cA1S19S42S20S1S16S32Q40A1A1S16S3eA1S3dG0S21S1aG0A1S2dG0RbR8A3S18G0R1A2A3S22S24S39R6R2A2A1S21S20S1bS20S20S3bR6R2A2A3Z0A3A2F_;Ft;VJAi;S26RbRaR9A3R7R6R5R4R3R2A7VJAi;S26S3aG0R9RcA3RbRaA3R8R7R6R5R4R3A7F_;F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fi;Fbd;Ffr;Ftv;").
Proof using .
  intros tv fr bd i Ai kc rho tp tr md HNULL0 (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCK & HCN).
  cbn [nd_tv nd_fr nd_bd nd_am ND] in *.
  assert (HNULL : forall t, nth_error tv i = Some t -> ~ tnz rho t).
  { intros t Ht Hnz. destruct (HNULL0 t Ht) as [H|H]; [exact (H Hnz)|].
    destruct (proj1 (Forall_forall _ _) HN t (nth_error_In _ _ Ht) Hnz) as (Hpos & _). lia. }
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [|split; [exact HFR|split; [exact HK0|split; [exact HP0|split; [|split; [exact HBU|split; [exact HPA|split; [exact HCK|
      unfold capN in *; cbn [nd_tv ND]; rewrite (cntS_remove_nth_null rho tv i HNULL); exact HCN]]]]]]]].
  - split; [|split].
    + unfold tvinA in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HN). eapply remove_nth_In. exact Ht.
    + apply tvd_remove. exact HD.
    + unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). eapply remove_nth_In. exact Ht.
  - unfold XA in *. destruct HXA as [HX0 HC]. split; [exact HX0|].
    intros bn H1 H2 H3 H4. apply (HC bn H1 H2 H3). intros v Hv Hnz. unfold tvals in Hv. apply in_map_iff in Hv as (t & <- & Ht).
    destruct (In_remove_nth_or tv i t Ht) as [E|E]; [exfalso; exact (HNULL t E Hnz)|].
    apply H4; [unfold tvals; apply in_map; exact E | exact Hnz].
Qed.
Lemma JA_drop_tv : ltac2:(tb__ "0|1|
S16S17S0S0A2M0A1S16S17S17S0S20A2S0A2A1S16S3cA1S19S1S16S32Q40A1A1S16S3eA1S3dG0S21S1aG0A1S2dG0R9R6A3S18G0R1A2A3S22S24S39R6R2A2A1S21S20S1bS20S20S3bR6R2A2A3Z0A3A2F_;Ft;VJA;S26R9R8R7A3R5R4R3R2A5VJA;S26S3aG0R7RaA3R9R8A3R6R5R4R3A5F_;F_;Fmd;Ftr;Ftp;Frho;Fi;Fbd;Ffr;Ftv;").
Proof using . intros tv fr bd i rho tp tr md HNULL (Ai & kc & H). exists Ai, kc. apply JAi_drop_tv; [exact HNULL | exact H]. Qed.
Lemma SPA_JA_drop_tv : ltac2:(tb__ "0|1|
S16S17S0S0A2M0A1S16S17S17S0S20A2S0A2A1S16S3cA1S19S35S1S16S32Q40A1A1S3fS41S4S6R3A1S5S34R4A1A1A3G0S21S1aG0A1S2dG0RaR7A3S18G0R1A2A3S22S24S39R6R2A2A1S21S20S1bS20S20S3bR6R2A2A3Z0A3A2F_;Ft;F_;S2bVsegs;VJA;S26R9R8R7A3A1R5R4R3R2A6S2bVsegs;VJA;S26S3aG0R7RaA3R9R8A3A1R6R5R4R3A6F_;F_;Fw;Ftp;Frho;FS;Fi;Fbd;Ffr;Ftv;").
Proof using .
  intros tv fr bd i S rho tp [tr [ms md]] HNULL [Hsm HJ]. split; [exact Hsm|]. apply JA_drop_tv; [|exact HJ].
  exact (HNULL (smatchA_facts segs _ _ _ _ Hsm)).
Qed.

Lemma SPA_JA_drop_tv_fact : ltac2:(tb__ "0|1|
S16S17S0S0A2M0A1S16S17S17S0S20A2S0A2A1S16S3cA1S19S35S1S16S32Q40A1A1S3fG0S21S1aG0A1S2dG0R9R6A3S18G0R1A2A3S21S1cS30S4S14SfS44S1dS0S0R2A3SeZ0A1A3A1S5S34R6A1A1A3S1eA3F_;Ft;S2bVsegs;VJA;S26R9R8R7A3A1R5R4R3R2A6S2bVsegs;VJA;S26S3aG0R7RaA3R9R8A3A1R6R5R4R3A6F_;F_;Fw;Ftp;Frho;FS;Fi;Fbd;Ffr;Ftv;").
Proof using .
  intros tv fr bd i S rho tp w HZ. apply SPA_JA_drop_tv. intros HF t Ht. left. intros Hnz.
  assert (X : holds rho (SPBranch BC_EQ (fst t) (SLit 0))).
  { pose proof (HZ t Ht) as H. apply existsb_exists in H as (g & Hg & E). apply sprop_eqb_sound in E. subst g. exact (proj1 (Forall_forall _ _) HF _ Hg). }
  apply (proj1 (holds_beq _ _ _)) in X.
  unfold tnz in Hnz. rewrite X in Hnz. apply Hnz. rewrite U_lit. reflexivity.
Qed.
Lemma JAi_tv_ext : ltac2:(tb__ "0|6|
S16S17S0S0A2M0A1M1G1S16S17S17S0S20A2S0A2A1S16S3cA1S42S20S1S16S32Q40A1A1S16S3eA1S3dS21S16S17S20S20A2M2A1S40G0G2S3bR4A1M3R9A4S40G0G2G3RaA4A3S19G0G0S21S1aG0A1M4S2dG0ReR3A3S18G0R2A2M5A3S21G4S2dG0ReR4A3G5A3S25S39RaR3A2S39RaR4A2A2F_;F_;Ft';Ft;Fk;VJAi;S26RcRaR9A3R8R7R6R5R4R3A7VJAi;S26RcRbRaA3R9R8R7R6R5R4A7F_;F_;F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fbd;Ffr;Ftv';Ftv;").
Proof using .
  intros tv tv' fr bd Ai kc rho tp tr md M1 M2 (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCK & HCN).
  cbn [nd_tv nd_fr nd_bd nd_am ND] in *.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [|split; [exact HFR|split; [exact HK0|split; [exact HP0|split; [revert HXA; unfold TobjJA.XA, TobjJA.tvals; cbn [nd_tv nd_am ND]; rewrite M1; exact (fun H => H)|split; [exact HBU|split; [exact HPA|split; [exact HCK|exact (capN_map BX Ai rho rho tv tv' M1 HCN)]]]]]]]].
  split; [eapply tvinA_map; eauto|]. split; [eapply tvd_map; eauto | eapply tvz_map; eauto].
Qed.
Lemma SPA_JA_tv_ext : ltac2:(tb__ "0|6|
S16S17S0S0A2M0A1M1G1S16S17S17S0S20A2S0A2A1S16S3cA1S35S1S16S32Q40A1A1S3fS41S4S6R3A1S5S34R4A1A1A3S23S21S16S17S20S20A2M2A1S40G0G2S3bR4A1M3R8A4S40G0G2G3R9A4A3S19G0G0S21S1aG0A1M4S2dG0RcR3A3S18G0R2A2M5A3S21G4S2dG0RcR4A3G5A3S25S39R9R3A2S39R9R4A2A2F_;F_;Ft';Ft;Fk;A2F_;S2bVsegs;VJA;S26R9R7R6A3A1R5R4R3R2A6S2bVsegs;VJA;S26R9R8R7A3A1R6R5R4R3A6F_;F_;Fw;Ftp;Frho;FS;Fbd;Ffr;Ftv';Ftv;").
Proof using .
  intros tv tv' fr bd S rho tp w H [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc.
  destruct (H (smatchA_facts segs _ _ _ _ Hsm)) as [M1 M2].
  eapply JAi_tv_ext; eauto.
Qed.

Lemma JA_null_size0 : ltac2:(tb__ "0|3|
S27S1S16S32Q40M0A1A1S16S3eA1S3dS17S0S0A2M1VJA;R6R5R4R3R2A5S2eG1R2S2aR7A1A3S21S20S33G0S2R7S1dS0S0R3A3A2A2Z0M2A3S21S20S33G0S2R8S1bS0S0R4A3A2A2G2A3F_;F_;F_;Ft;Fmd;Ftr;Ftp;Frho;Fnd;").
Proof using .
  intros nd rho tp tr md t (Ai & kc & (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & _)) Hin Hz.
  unfold tvz in HZ. pose proof (proj1 (Forall_forall _ _) HZ t Hin) as X. cbv beta in X.
  unfold tnz, tvv in X. cbn [snd] in X. apply X. intros Hnz. exact (Hnz Hz).
Qed.

End Sum.

Lemma SPA_x_requiv : ltac2:(tb__ "0|2|
S2cS1S35S16S17S0S0A2M0A1S16S32Q40A1M1A1S3fS2fG0G0G0G0S23S21G1S2R7S1dS0S0R1A3A2S2R7S1dS0S0R2A3A2A3S21G1S2R7S1bS0S0R1A3A2S2R7S1bS0S0R2A3A2A3A2Lr';Lr;S36R4A1R3A5S21S1cS31G0S38ScS34R5A1A1A1R4A3S1eA3S2bVsegs;R8R6R7R4R3A6S2bVsegs;R9S45R7R6A2R8R5R4A6F_;F_;F_;Fw;Ftp;FX';FA;Frho;FJ;").
Proof using .
  intros J rho A X' tp [tr [ms md]] HF Hb [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|exact Hk].
  split; [exact Hsm|]. split; [exact HMI|].
  split; [unfold axwf in Hwf |- *; cbn; apply andb_prop in Hwf as [_ Hwf]; rewrite Hb, Hwf; reflexivity|].
  split; [|exact Hhz].
  unfold shadow_ok in Hsh |- *. cbn [ax_X ax_setX ax_S ax_base]. clear Hb. revert Hsh.
  induction HF as [|r r' l l' Hrr HF IH]; intros Hsh; [constructor|]. inversion Hsh as [|r0 l0 Hr Hl]; subst.
  constructor; [|exact (IH Hl)].
  destruct Hrr as [E1 E2]. unfold xr_ok in Hr |- *. cbn zeta in Hr |- *. rewrite E1, E2. exact Hr.
Qed.

Lemma SPA_reshape : ltac2:(tb__ "0|3|
S2cS1S35S19S3S3S16S32Q40M0A1A1S3fS21S1aS3A1S2dS3S15S34R6A1A1R5A3S18S3R4A2A3S21S16S7A1S11R4A1S1fS7A1A3S21S13S9R5A1SdA3S21S1cS10S9R7A1A1S1eA3S21S1cS12ScS34RaA1A1R7A2S1eA3S41S4S6RcA1S5S34RbA1A1A3S23S21S20S43S33G0S2RdS8R9A1A2A2M1SbRdR9A2A2S43S33G0S2RdS8RaA1A2A2M2SbRdRaA2A2A3S21S20S43G1SaRdR9A2A2S43G2SaRdRaA2A2A3A2F_;S2bVsegs;ReRcRdR8R7A6S2bVsegs;RfS37RdS46S34RdA1RcRaA3A2ReR9R8A6F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Fo';Fo;Fi;FA;Frho;FJ;").
Proof using .
  intros J rho A i o o' tp [tr [ms md]] Hn Hc Hd Hw Hwf Hrg [(Hsm & HMI & Hwf' & Hsh & Hhz) Hk]. split; [|exact Hk].
  pose proof (smatch_reshape segs rho (ax_S A) i o o' _ Hn Hc Hd Hw Hwf Hrg Hsm) as Hsm'.
  assert (Hin_o : In o (ss_objs (ax_S A))) by (eapply nth_error_In; exact Hn).
  pose proof (Hrg (smatch_facts segs _ _ _ Hsm)) as [R1 R2].
  split; [exact Hsm'|]. split; [exact HMI|]. split; [unfold axwf in Hwf' |- *; cbn; exact Hwf'|]. split; [|exact Hhz].
  apply shadow_ok_reobjs; [exact Hsh|]. apply xshadow_outside_cover; [exact Hsh|].
  unfold reshape_obj_at. cbn [set_objs ss_objs]. intros o2 x Ho2 Hx. apply in_app_or in Ho2 as [Ho2|[<-|Ho2]].
  - exists o2. split; [eapply In_firstn_In; exact Ho2 | exact Hx].
  - exists o. split; [exact Hin_o|]. unfold obj_range in Hx |- *. cbn [fst snd] in Hx |- *. lia.
  - exists o2. split; [eapply In_skipn_In; exact Ho2 | exact Hx].
Qed.

End WithSegs.
End TobjJAX.

