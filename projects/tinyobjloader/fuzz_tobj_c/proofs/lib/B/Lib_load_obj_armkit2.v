(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "holds"; "SLit"; "sv_eqb"; "rw"; "sobj"; "sprop_eqb"; "SPUle"; "SVar"; "obj_range"; "SAlu"; "ss_next"; "SMd"; "SPUlt"; "ob_base"; "ob_hi"; "ob_lo"; "ss_facts"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Datatypes"; "bool"; "list"; "prod"; "true"; "pair"; "nat"; "false"; "app"; "fst"; "snd"; "None"; "negb"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "BUD"; "bd_nn"; "bsumK"; "bsumV"; "bd_wpos"; "bd_subst"; "pay_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "entailsA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "pow"; "mul"; "sub"; "leb"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "ndesc"; "JA"; "NDA"; "amode"; "TPA"; "frinA"; "tvinA"; "am_eqb"; "am_subst"; "fr_sub_eqb"; "nd_am"; "nd_bd"; "nd_below"; "nd_fr"; "nd_tv"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Stdlib.Lists.List"; "In"; "existsb"; "filter"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_loop"; "xLC"; "pI"; "xLK"; "xLD"; "HNEXT"; "entA"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF"; "efmeasA"; "bud_pay2"; "bitem_eqb"; "bud_le2"; "phi_reads"; "robj_ownframe_off"; "robj_stackN"; "wsub_id_on"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_ok"; "FBx"; "tvz"; "T0"; "tvd"; "robj_tracked"; "svT"; "tv_sub_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG"; "bd_permb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_bud"; "VLA"; "RL"; "z0"; "Mline"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC"; "FFx"; "pclMA"; "robjs_okF"; "xrs_okF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs"; "kb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2.Site"; "lines_chk"; "robj_ent"; "robjs_chkC"; "xextraLO"; "xrs_chkC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_sub"; "wsub"; "wsub_get"; "sv_subst"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface"; "in_lits"; "X_lits"; "in_litsL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_armkit2"; "xr_inlits"; "xr_stackC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_defs"; "NP"; "vBUF"; "vCFGp"; "vLEN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_lglue"; "frL"; "V_B"; "V_L"; "extraLO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_p0"; "P0_lo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "uleq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "IMG_HI";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "alloc_lawsA"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SUB"; "M_MUL"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_load_obj_pro"; "ax_fnodup"; "ax_tidy"; "ax_xnodup"; "fnodup"; "xnodup"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve"; "B32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "xr_tracked"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS"; "robj_ownframe"; "xr_len0"; "xr_ownlocal"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT"; "robj_stackA2"; "robj_tpiece"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Sorting.Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena ObjXform ObjUnbase.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RtCells.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAM2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p2.TobjJAC.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require TobjJAR TobjJAS TobjJAT TobjJAF.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p1.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAT OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAF OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAK OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p5.TobjJAG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.CertGlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ResidualA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require p3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.p3.ObjZeroA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import ObjEmptyA PinA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code Lib_scan_double Lib_vec_reserve.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require np.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Lib_builderH_defs.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_scan_double OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_vec_reserve OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.np.Lib_builder_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Lib_builderH_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import Lib_rom_defs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nn.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require nk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import Lib_load_obj_defs Lib_load_obj_pro Lib_load_obj_pro2 Lib_load_obj_loop Lib_load_obj_disp Lib_load_obj_lglue Lib_load_obj_bud.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Import ScanDoubleAddr LOAddr LOLAddr.

Lemma xnodup_incl : ltac2:(tb__ "0|1|
S18S19S0S0A2M0A1G0S4eG0R1S9dR2A1A3S4eG0R2R3A3F_;Fr;Fl;").
Proof.
  induction l as [|x l IH]; intros r H; cbn in H; [exact H|].
  destruct (existsb _ l); [right; exact (IH r H)|]. destruct H as [<-|H]; [left; reflexivity | right; exact (IH r H)].
Qed.
Lemma fnodup_incl : ltac2:(tb__ "0|0|
S18S2A1S2S4eS2R1S9cR2A1A3S4eS2R2R3A3F_;Ff;Fl;").
Proof.
  induction l as [|x l IH]; intros f H; cbn in H; [exact H|].
  destruct (existsb _ l); [right; exact (IH f H)|]. destruct H as [<-|H]; [left; reflexivity | right; exact (IH f H)].
Qed.

Section Tidy.
Variable segs' : list Segment.
Lemma SPA_xnodup : ltac2:(tb__ "0|0|
S4dS1S30S18S4aQ40A1A1S5bS4cVsegs';R5R3R4R2R1A6S4cVsegs';R6S9bR4A1R5R3R2A6F_;Fw;Ftp;FA;Frho;FJ;").
Proof. intros J rho A tp w H. unfold ax_xnodup. apply SPA_x_sub; [apply xnodup_incl | exact H]. Qed.
Lemma SPA_fnodup : ltac2:(tb__ "0|0|
S4dS1S30S18S4aQ40A1A1S5bS4cVsegs';R5R3R4R2R1A6S4cVsegs';R6S99R4A1R5R3R2A6F_;Fw;Ftp;FA;Frho;FJ;").
Proof.
  intros J rho A tp w H. unfold ax_fnodup. apply SPA_refacts; [exact H | |].
  - destruct w as [tr [ms md]]. destruct H as [(Hsm & _) _]. destruct Hsm as [Hwf _].
    unfold swf in Hwf. repeat (apply andb_prop in Hwf as [Hwf ?X]).
    apply forallb_forall. intros f Hf. apply (proj1 (forallb_forall _ _) X f (fnodup_incl _ f Hf)).
  - intros HF. apply Forall_forall. intros f Hf. exact (proj1 (Forall_forall _ _) HF f (fnodup_incl _ f Hf)).
Qed.
Lemma SPA_tidy : ltac2:(tb__ "0|0|
S4dS1S30S18S4aQ40A1A1S5bS4cVsegs';R5R3R4R2R1A6S4cVsegs';R6S9aR4A1R5R3R2A6F_;Fw;Ftp;FA;Frho;FJ;").
Proof. intros J rho A tp w H. unfold ax_tidy. apply SPA_fnodup. apply SPA_xnodup. exact H. Qed.
End Tidy.

Lemma uval_sub_le : ltac2:(tb__ "0|0|
S1S0S0S33S27R3R1A2S27R3R2A2A2S23S14S27R4ScS95R3R2A3A2S38S27R4R3A2S27R4R2A2A2A3F_;Fb;Fa;Frho;").
Proof.
  intros rho a b H. pose proof (uval_range rho a) as Ra. pose proof (uval_range rho b) as Rb.
  unfold uval in *. cbn [eval]. rewrite sub_val. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. lia.
Qed.
Lemma VLA_val : ltac2:(tb__ "0|2|
S1S14S0S24S33Z0R2A2S34R2Z40A2A2S34S27R4S54A2S27R4S53A2A2S33S27R5S53A2S36Z2M0Z1aA2A2S34S27R6R4A2S36G0Z1bA2M1A2S23S14S27R7S6eR6R5A2A2S35S35S37S71S38S27R7S53A2S27R7S54A2A2A2S37G1R6A2A2S27R7R5A2A2A3F_;F_;F_;F_;Finner;Fph;Frho;").
Proof.
  intros rho ph inner Hph Hi Hc Hin. pose proof (uval_range rho pI) as RI. pose proof (uval_range rho inner) as RN.
  assert (E1 : uval rho (SAlu ALU_SUB xLC pI) = uval rho xLC - uval rho pI) by (apply uval_sub_le; lia).
  assert (E2 : uval rho (SMd M_MUL (SLit Mline) (SAlu ALU_SUB xLC pI)) = Mline * (uval rho xLC - uval rho pI)).
  { rewrite uval_mul_lit by (unfold Mline; rewrite ?E1; lia). rewrite E1. reflexivity. }
  unfold VLA. rewrite uval_add_small by (rewrite uval_add_small by (rewrite E2, uval_lit by (unfold Mline; lia); unfold Mline; lia); rewrite E2, uval_lit by (unfold Mline; lia); unfold Mline; lia).
  rewrite uval_add_small by (rewrite E2, uval_lit by (unfold Mline; lia); unfold Mline; lia).
  rewrite E2, uval_lit by (unfold Mline; lia). reflexivity.
Qed.

Lemma efmeasA_VLA : ltac2:(tb__ "0|2|
S30S3bS1cS14S0S1S23S14S5cS1bS19S19S30S3bA2M0S1cA2S19S14S0A2S1bG0S1cS1bS30S3bR6R5A4R4A4S1bS14S0S6fS6eR3R2A2M1A4A4R1A2S35S37S6fS36Z2Z40A2A2S27R1G1A2A2A3Frho;Finner;Fph;Fk;Fnd;FX;").
Proof. intros. reflexivity. Qed.

Definition xr_inlits (r : sv * sv) : bool := ltac2:(tb__ "0|1|
S4fS19S0S0A2M0G0S17S17L_;S5S1fS0S0R1A3S1fS0S0Vr;A3A2S5S20S0S0R1A3S20S0S0Vr;A3A2S1dX17x2Lx;S84A3").
Lemma in_litsL_In : ltac2:(tb__ "0|1|
S18S19S0S0A2M0A1S14S14S14S4eG0S1bS0S0S4R3A1S4R2A1A4R4A3S24S33R4R2A2S34R2S35R4R3A2A2A2S85R6R3A2F_;F_;Fa;Fn;Fb;Fl;").
Proof.
  induction l as [|x l IH]; intros b n a Hin Ha; [destruct Hin|]. destruct Hin as [->|Hin]; cbn; [left; exact Ha|].
  destruct x as [xb xn]. destruct xb; try (exact (IH b n a Hin Ha)); destruct xn; try (exact (IH b n a Hin Ha)). right. exact (IH b n a Hin Ha).
Qed.
Lemma xr_inlits_sound : ltac2:(tb__ "0|1|
S19S0S0A2S1S14S23S17S86R3A1S1aA3S24S33S27R3S1fS0S0R4A3A2M0R2A2S34R2S35G0S27R3S20S0S0R4A3A2A2A2A2S83R3A1F_;F_;Fa;Frho;Fr;").
Proof.
  intros r rho a H Ha. unfold xr_inlits in H. apply existsb_exists in H as (x & Hin & Hc). apply lazy_andb_prop in Hc as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. destruct r as [rb rn]. cbn [fst snd] in H1, H2, Ha. subst rb rn. destruct x as [xb xn]. cbn [fst snd] in Ha.
  assert (HL : forall y, In y OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface.X_lits -> exists b n, y = (SLit b, SLit n) /\ 0 <= b /\ 0 <= n /\ b + n < 2 ^ 40).
  { intros y Hy. unfold OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.nk.Lib_fuzz_iface.X_lits in Hy. cbn [In] in Hy.
    repeat (destruct Hy as [<-|Hy]; [eexists _, _; split; [reflexivity|]; lia|]). destruct Hy. }
  destruct (HL _ Hin) as (b & n & E & Hb & Hn & Hbn). injection E as -> ->.
  rewrite !uval_lit in Ha by lia. exact (in_litsL_In _ b n a Hin Ha).
Qed.

Definition xr_stackC (facts : list sprop) (r : sv * sv) : bool := ltac2:(tb__ "0|7|
S0S17Lx;S20S0S0Vr;A3S14S17S17L_;M0S39Z0M1R1A2G0S3aR1S36Z2M2Z28A2A2G0S91Vfacts;S6aG1S1fS0S0Vr;A3M3A4S91Vfacts;G3G1S4S38S36G2Z2fA2R1A2A1A4S1dX17x2S1dX17x2S1dX17x2Ln;S15S1dLi;S97S0S0S1dLb;La;M4Lop;M5G5S98G4Lop;M6G6S17S16S0S1dLa;Lw;Lsgn;S15S0S14S1dLk;Li;Ll;X0x8").
Lemma xr_stackC_sound : ltac2:(tb__ "0|1|
S18S2A1S1S14S19S0S0A2S14S4bS2S3R4A1R5A3S64R5R4A2S23S17S87R7R4A2S1aA3S24S33S27R7S1fS0S0R5A3A2M0R4A2S34R4S35G0S27R7S20S0S0R5A3A2A2A2A2S24S33R7R5A2S34R5S36Z2Z2fA2A2A2F_;F_;F_;F_;Fa;Fr;FT;Frho;Ffacts;").
Proof.
  intros facts rho T r a HF [HT _] H Ha. unfold xr_stackC in H. destruct r as [rb rn]. cbn [fst snd] in H, Ha.
  destruct rn as [n| | | | | | |]; try discriminate.
  apply lazy_andb_prop in H as [H0 H]. apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H3].
  apply Z.leb_le in H0. apply Z.ltb_lt in H1.
  pose proof (uleq_sound rho facts _ 0 _ HF H2) as U2. pose proof (uleq_sound rho facts _ 0 _ HF H3) as U3.
  unfold U in U2, U3. rewrite U_lit in U3. unfold M64v in U3. rewrite Z.mod_small in U3 by lia.
  unfold svT in U2. cbn [eval] in U2. rewrite HT in U2.
  rewrite uval_lit in Ha by lia. unfold uval in Ha. lia.
Qed.

Section Site.
Variable AInv : ltac2:(tb__ "0|0|
S6dS1S18S4aQ40A1A1S59OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S93S52VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S14S78VCST;R1A2S24S33Z0R2A2S34R2S92A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S14S78VXGL;R1A2S24S33Z0R2A2S34R2S92A2A2F_;Fa;").
Hypothesis HXlits : ltac2:(tb__ "0|0|
S14S83R1A1S78VXGL;R2A2F_;Fa;").
Variable rho0 : valuation.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S18S19S19S14S14A2S14A2A1").

Definition robjs_chkC (facts : list sprop) (tv : list (sv * sv)) (fr : list (sv * Z * sv)) (extra : sobj -> bool) (R : list sobj) : bool := ltac2:(tb__ "0|2|
S51S7S7S17S17L_;M0Vextra;R1A1S1aG0S69Vtv;S21S1cA1M1R1A3S1aG0Sa4Vfacts;Vtv;R1A3S1aG0Sa0Vfr;U0G1R1A4S1aG0S61Vfr;R1A2S1aG0S62Vfacts;R1A2S1aSa3Vfacts;R1A2X17x2X17x2X17x2X17x2X17x2X17x2Lo;VR;A3").

Lemma robjs_chkC_sound : ltac2:(tb__ "0|1|
S6dS1S18S2A1S18S19S0S0A2A1S18S19S19S0S14A2S0A2A1S7S17F_;S18S7A1S1S18S4aQ40A1A1S59VAInv;RaR3R2R1A4S4bS2S3RaA1R9A3S3fVrho0;RcA2S64RcS67Vrho0;A1A2S41VFB;ReRdRbA4S68ReRcA2S66RfRdA2S40VFF;R11R10RdA4S23S17S7bR10RfReRdRcA5S1aA3S7S14S4eS7R2RfA3S23S17R11R3A1S1aA3S24S33S1fS14S14SbR16R4A2M0A3R3A2S34R3S20S14S14G0A3A2A2S73VCST;Vrho0;S65VFB;R17R15A3S72VFF;R17R14A3R4A5F_;F_;F_;Fa;Fo;S74VCST;Vrho0;VFB;VFF;R13R11R10ReA8F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fextra;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho facts tv fr extra R rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR Hchk Hextra o a Ho Hr.
  unfold robjs_chkC in Hchk. pose proof (proj1 (forallb_forall _ _) Hchk o Ho) as Hc. cbv beta in Hc.
  apply lazy_orb_prop in Hc as [Hc|Hc]; [exact (Hextra o a Ho Hc Hr)|].

  assert (JAT : forall cls, (cls = robj_tracked tv None o \/ cls = robj_tpiece facts tv o \/ cls = TobjJAS.robj_ownframe fr 0 None o \/ cls = robj_stackA2 facts o) ->
                 cls = true -> pclMA CST rho0 (FBx FB rho tv) (FFx FF rho fr) a).
  { intros cls Hcls E. apply (robjs_checkP_sound segs AInv CST ALA rho0 FB FF Ai rho facts tv fr None (fun _ => false) [o] rho1 tp1 md1 HM HF HT0 HN HD HZ HFR) with (o := o);
      [| intros o' a' _ HE' _; discriminate HE' | left; reflexivity | exact Hr].
    rewrite robjs_checkP_ref_eq. unfold robjs_checkP_ref. cbn [forallb]. destruct Hcls as [<-|[<-|[<-| <-]]]; rewrite E;
      destruct (robj_stackA2 facts o), (robj_tracked tv None o), (robj_tpiece facts tv o), (TobjJAS.robj_ownframe fr 0 None o); reflexivity. }
  apply lazy_orb_prop in Hc as [Hc|Hc]; [exact (JAT _ (or_introl eq_refl) Hc)|].
  apply lazy_orb_prop in Hc as [Hc|Hc]; [exact (JAT _ (or_intror (or_introl eq_refl)) Hc)|].
  apply lazy_orb_prop in Hc as [Hc|Hc]; [exact (JAT _ (or_intror (or_intror (or_introl eq_refl))) Hc)|].
  apply lazy_orb_prop in Hc as [Hc|Hc].
  {
    destruct (robj_ownframe_off_sound fr o rho a Hc Hr) as (x & Hx & Hc6 & Hax).
    pose proof (proj1 (Forall_forall _ _) (proj1 HFR) x Hx) as (X1 & _ & _).
    destruct (law_blocks _ _ _ ALA Ai rho1 tp1 md1 HM) as (_ & _ & HFrl).
    destruct (HFrl _ _ X1) as (_ & _ & _ & F4 & F5 & _). pose proof (topG_range (aa_geom Ai)) as TG.
    destruct Hax as [Hax|Hax]; [|exfalso; unfold frv in F5, Hax; cbn [fst snd] in F5, Hax; pose proof (fs_frame_size_bounds' _ Hc6); lia].
    right; right; right. exists (fst (frv rho x)), (snd (frv rho x)), (uval rho (snd x)). split; [|exact Hax].
    apply In_FFx. right. exists x. split; [exact Hx | reflexivity]. }
  apply lazy_orb_prop in Hc as [Hc|Hc].
  { left. exact (robj_stackN_sound facts rho _ o a HF HT0 Hc Hr). }
  exact (JAT _ (or_intror (or_intror (or_intror eq_refl))) Hc).
Qed.

Definition xrs_chkC (facts : list sprop) (tv : list (sv * sv)) (fr : list (sv * Z * sv)) (extra : sv * sv -> bool) (X : list (sv * sv)) : bool := ltac2:(tb__ "0|3|
S51S19S0S0A2M0G0S17S17L_;M1Vextra;R1A1S1aG1Sa1R1A1S1aG1S86R1A1S1aG1S9fVtv;S21S1cA1M2R1A3S1aG1Sa2Vfr;G2R1A3S1aS87Vfacts;R1A2X17x2X17x2X17x2X17x2X17x2Lr;VX;A3").

Lemma xrs_chkC_sound : ltac2:(tb__ "0|3|
S6dS1S18S2A1S18S19S0S0A2M0A1M1S18S19S19S0S14A2S0A2A1G0S17F_;G1S1S18S4aQ40A1A1S59VAInv;RaR3R2R1A4S4bS2S3RaA1R9A3S3fVrho0;RcA2S64RcS67Vrho0;A1A2S41VFB;ReRdRbA4S68ReRcA2S66RfRdA2S40VFF;R11R10RdA4S23S17S7dR10RfReRdRcA5S1aA3G0S14S4eG0R2RfA3S23S17R11R3A1S1aA3S24S33S27R16S1fS0S0R4A3A2M2R3A2S34R3S35G2S27R16S20S0S0R4A3A2A2A2A2S26S73VCST;Vrho0;S65VFB;R17R15A3S72VFF;R17R14A3R4A5S78VXGL;R4A2A2F_;F_;F_;Fa;Fr;S75VCST;VXGL;Vrho0;VFB;VFF;R13R11R10ReA9F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FX;Fextra;Ffr;Ftv;Ffacts;Frho;FAi;").
Proof using ALA HXlits.
  intros Ai rho facts tv fr extra X rho1 tp1 md1 HM HF HT HT0 HN HD HZ HFR Hchk Hextra r a Hr Ha.
  unfold xrs_chkC in Hchk. pose proof (proj1 (forallb_forall _ _) Hchk r Hr) as Hc. cbv beta in Hc.
  apply lazy_orb_prop in Hc as [Hc|Hc]; [exact (Hextra r a Hr Hc Ha)|].

  assert (JAS : forall cls, (cls = xr_len0 r \/ cls = xr_tracked tv None r \/ cls = xr_ownlocal fr None r) -> cls = true ->
                 pclMA CST rho0 (FBx FB rho tv) (FFx FF rho fr) a \/ RtCells.in_rangesZ XGL a).
  { intros cls Hcls E.
    apply (xrs_checkL_sound segs AInv CST XGL ALA rho0 FB FF Ai rho facts tv fr None [] (fun _ => false) [r] rho1 tp1 md1 HM HF HT0 HN HD HZ HFR) with (r := r);
      [| intros r' a' _ HE' _; discriminate HE' | left; reflexivity | exact Ha].
    rewrite xrs_checkL_ref_eq. unfold xrs_checkL_ref. cbn [forallb]. destruct Hcls as [<-|[<-| <-]]; rewrite E;
      destruct (xr_len0 r), (xr_lit_in XGL r), (xr_tracked tv None r), (existsb (xr_in_stack_obj facts r) [mkObj (fst r) (SLit 0) (snd r) [] DUnknown]), (xr_ownlocal fr None r); reflexivity. }
  apply lazy_orb_prop in Hc as [Hc|Hc]; [exact (JAS _ (or_introl eq_refl) Hc)|].
  apply lazy_orb_prop in Hc as [Hc|Hc]; [right; apply HXlits; exact (xr_inlits_sound r rho a Hc Ha)|].
  apply lazy_orb_prop in Hc as [Hc|Hc]; [exact (JAS _ (or_intror (or_introl eq_refl)) Hc)|].
  apply lazy_orb_prop in Hc as [Hc|Hc]; [exact (JAS _ (or_intror (or_intror eq_refl)) Hc)|].
  left. left. exact (xr_stackC_sound facts rho _ r a HF HT0 Hc Ha).
Qed.

Lemma extraLO_pclMA : ltac2:(tb__ "0|1|
S1S18S19S0S0A2A1S18S19S19S0S14A2S0A2A1S7S14S77S88Vrho0;R5A3S90VCST;VFB;VFF;Vrho0;A4S23S17S8fR4A1S1aA3S24S33S1fS14S14SbR8R5A2M0A3R4A2S34R4S20S14S14G0A3A2A2S73VCST;Vrho0;S65VFB;R9R8A3S72VFF;R9R7A3R5A5F_;F_;F_;F_;Fa;Fo;Ffr;Ftv';Frho;").
Proof.
  intros rho tv' fr o a Hav (P1 & P2 & P3) HE Hr.
  assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
  { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
  apply (pclMA_mono CST rho0 FB (FBx FB rho tv') FF (FFx FF rho fr) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
  unfold extraLO in HE. apply lazy_orb_prop in HE as [HE|HE]; [|apply lazy_orb_prop in HE as [HE|HE]];
    apply lazy_andb_prop in HE as [Hb HE]; apply lazy_andb_prop in HE as [Hl Hh]; apply sv_eqb_sound in Hb; apply sv_eqb_sound in Hl; apply sv_eqb_sound in Hh;
    unfold obj_range, obj_lo_of, obj_hi_of in Hr; rewrite Hb, Hl, Hh in Hr; cbn [fst snd] in Hr.
  - apply P1. rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)).
    rewrite soff_lit_small in Hr by lia. pose proof (uval_range rho vLEN) as RL.
    assert (HL : soff rho vLEN <= uval rho vLEN).
    { unfold soff, uval. rewrite bv_signed_U. destruct (Zsigned_spec (bv_unsigned (eval rho vLEN))) as [[_ X]|[_ X]]; rewrite X; lia. }
    unfold uval in *. lia.
  - apply P2. rewrite <- (AG 15%positive vCFGp eq_refl ltac:(reflexivity)). rewrite !soff_lit_small in Hr by lia. unfold uval in *. lia.
  - apply P3. rewrite <- (AG 28%positive (SVar 28) eq_refl ltac:(reflexivity)). rewrite !soff_lit_small in Hr by lia. unfold uval in *. lia.
Qed.

Definition xextraLO (r : sv * sv) : bool := ltac2:(tb__ "0|3|
S17S17L_;M0G0S5S1fS0S0Vr;A3M1S89A2S5S20S0S0Vr;A3M2S8bA2S1dX17x2S1aG0S5G1S8aA2S5G2S4Z90A1A2S1dX17x2X17x2").
Lemma xextraLO_pclMA : ltac2:(tb__ "0|2|
S1S18S19S0S0A2M0A1S18S19S19S0S14A2S0A2A1G0S14S77S88Vrho0;R5A3S90VCST;VFB;VFF;Vrho0;A4S23S17S7cR4A1S1aA3S24S33S27R8S1fS0S0R5A3A2M1R4A2S34R4S35G1S27R8S20S0S0R5A3A2A2A2A2S73VCST;Vrho0;S65VFB;R9R8A3S72VFF;R9R7A3R5A5F_;F_;F_;F_;Fa;Fr;Ffr;Ftv';Frho;").
Proof.
  intros rho tv' fr r a Hav (P1 & P2 & P3) HE Ha.
  assert (AG : forall v e, e = SVar v -> (v < NP)%positive -> uval rho e = uval rho0 e).
  { intros v e -> Hv. unfold uval. cbn [eval]. rewrite <- (proj1 Hav v Hv). reflexivity. }
  apply (pclMA_mono CST rho0 FB (FBx FB rho tv') FF (FFx FF rho fr) a); [intros x Hx; apply In_FBx; left; exact Hx | intros x Hx; apply In_FFx; left; exact Hx |].
  unfold xextraLO in HE. apply lazy_orb_prop in HE as [HE|HE]; apply lazy_andb_prop in HE as [Hb Hl]; apply sv_eqb_sound in Hb; apply sv_eqb_sound in Hl;
    destruct r as [rb rl]; cbn [fst snd] in Hb, Hl, Ha; subst rb rl.
  - apply P1. rewrite <- (AG 13%positive vBUF eq_refl ltac:(reflexivity)), <- (AG 14%positive vLEN eq_refl ltac:(reflexivity)). exact Ha.
  - apply P2. rewrite <- (AG 15%positive vCFGp eq_refl ltac:(reflexivity)). rewrite uval_lit in Ha by lia. exact Ha.
Qed.

Definition robj_ent (o : sobj) : bool := ltac2:(tb__ "0|1|
S17S17L_;M0S5S10Vo;A1S58S54A1A2G0S5S12Vo;A1S4Z0A1A2S5S11Vo;A1S4Z10A1A2S1dX17x2S1dX17x2").

Definition lines_chk (facts : list sprop) : bool := ltac2:(tb__ "0|3|
S17S17L_;M0S4fS2S8SfS54S53A2A1Vfacts;A3G0S4fS2S8S9S53S55A2A1Vfacts;A3G0S4fS2S8S9S55S4ZffffffffA1M1A2A1Vfacts;A3G0S4fS2S8S9S76Z10S55A2M2G1A2A1Vfacts;A3G0S4fS2S8S9S56S4Z800000000000A1A2A1Vfacts;A3S4fS2S8S9ScS94S56G2A3SaP1eA1A2A1Vfacts;A3S1dX17x2S1dX17x2S1dX17x2S1dX17x2S1dX17x2").
Lemma lines_blk : ltac2:(tb__ "0|6|
S1S18S2A1S14S4bS2S3R3A1R2A3S23S17S79R3A1S1aA3S64R5R3A2S24S23S14S27R6S58S54A1A2S35S27R6S56A2M0S37Z10M1S27R6S54A2M2A2A2A3S24S34G2S27R6S53A2M3A2S24S33G3S27R6S55A2M4A2S24S33S37G1G4A2M5ZffffffffA2S24S23S14S27R6S76G1S55A2A2G5A3S33S35G0G5A2R4A2A2A2A2A2A2F_;F_;F_;FT;Ffacts;Frho;").
Proof.
  intros rho facts T HF H [HT HT2]. unfold lines_chk in H.
  apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H]. apply lazy_andb_prop in H as [H3 H]. apply lazy_andb_prop in H as [H4 H].
  apply lazy_andb_prop in H as [H5 H6].
  pose proof (holds_mem _ _ _ HF H1) as F1. pose proof (holds_mem _ _ _ HF H2) as F2. pose proof (holds_mem _ _ _ HF H3) as F3.
  pose proof (holds_mem _ _ _ HF H4) as F4. pose proof (holds_mem _ _ _ HF H5) as F5. pose proof (holds_mem _ _ _ HF H6) as F6.
  rewrite h_ult in F1. rewrite h_ule in F2, F3, F4, F5, F6. rewrite uval_lit in F3, F4, F5 by lia.
  pose proof (uval_range rho xLK) as RK. pose proof (uval_range rho xLD) as RD. pose proof (uval_range rho pI) as RI.
  assert (EK : uval rho (kb 16 xLK) = 16 * uval rho xLK) by (unfold kb; apply uval_mul_lit; lia). rewrite EK in F4.
  assert (EI : uval rho (SMd M_MUL (SLit 16) pI) = 16 * uval rho pI) by (apply uval_mul_lit; lia).
  assert (E30 : uval rho (SVar 30) = T) by (unfold uval; cbn [eval]; exact HT). rewrite E30 in F6.
  rewrite uval_add_small in F6 by (rewrite EK; lia). rewrite EK in F6.
  unfold entA. rewrite uval_add_small by (rewrite EI; lia). rewrite EI. repeat split; lia.
Qed.

Lemma robj_ent_pclMA : ltac2:(tb__ "0|2|
S1S18S2A1S14S18S19S0S0A2M0A1S18S19S19S0S14A2S0A2A1S7S14S4bS2S3R7A1R6A3S23S17S79R7A1S1aA3S64R9R7A2S66RaR7A2S4eG0S1bS0S0S56S76Z10S55A2A4R8A3S23S17S7aR7A1S1aA3S24S33S1fS14S14SbRdR8A2M1A3R7A2S34R7S20S14S14G1A3A2A2S73VCST;Vrho0;S65VFB;ReRbA3S72VFF;ReRaA3R8A5F_;F_;F_;F_;F_;F_;F_;Fa;Fo;Ffr;Ftv;FT;Ffacts;Frho;").
Proof.
  intros rho facts T tv fr o a HF Hchk HT HZ Hin HE Hr.
  destruct (lines_blk rho facts T HF Hchk HT) as (EA & Hi & Hck & Hk32 & EK & Htop). destruct HT as [_ HT2].
  unfold robj_ent in HE. apply lazy_andb_prop in HE as [Hb HE]. apply lazy_andb_prop in HE as [Hl Hh].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr. cbn [fst snd] in Hr. rewrite !soff_lit_small in Hr by lia.
  change (bv_unsigned (eval rho (entA pI))) with (uval rho (entA pI)) in Hr. rewrite EA in Hr. pose proof (uval_range rho pI) as RI.
  assert (Hnz : tnz rho (xLD, kb 16 xLK)).
  { intros Z0. pose proof (proj1 (Forall_forall _ _) HZ _ Hin) as Z1. cbv beta in Z1. unfold tvv in Z1. cbn [fst snd] in Z1.
    specialize (Z1 ltac:(intros H; exact (H Z0))). change (bv_unsigned (eval rho (kb 16 xLK))) with (uval rho (kb 16 xLK)) in Z1. lia. }
  right; right; left. exists (uval rho xLD), (uval rho (kb 16 xLK)). split.
  - apply In_FBx. right. exists (xLD, kb 16 xLK). split; [exact Hin|]. split; [exact Hnz | reflexivity].
  - rewrite EK. lia.
Qed.

Lemma lines_nz : ltac2:(tb__ "0|1|
S1S18S2A1S14S18S19S0S0A2M0A1S4bS2S3R4A1R3A3S23S17S79R4A1S1aA3S64R6R4A2S66R7R4A2S4eG0S1bS0S0S56S76Z10S55A2A4R5A3S25S23S14S27R9S56A2Z0A3A1F_;F_;F_;F_;F_;Ftv;FT;Ffacts;Frho;").
Proof.
  intros rho facts T tv HF Hchk HT HZ Hin Z0.
  destruct (lines_blk rho facts T HF Hchk HT) as (_ & Hi & Hck & _ & EK & _). pose proof (uval_range rho pI) as RI.
  pose proof (proj1 (Forall_forall _ _) HZ _ Hin) as Z1. cbv beta in Z1. unfold tvv in Z1. cbn [fst snd] in Z1.
  specialize (Z1 ltac:(intros H; exact (H Z0))). change (bv_unsigned (eval rho (kb 16 xLK))) with (uval rho (kb 16 xLK)) in Z1. lia.
Qed.

Lemma VLA_lt : ltac2:(tb__ "0|9|
S1S1S14S14S0S30S30S3bS3bS1cS1cS23S4aQ40A1M0S6RaP1ccM1A2S6RbG1A2A3S23G0S6RbP1d3M2A2S6RcG2A2A3S34S27RdS54A2S27RdS53A2A2S33S27ReS53A2S36Z2M3Z1aA2A2S34S27ReRbA2S36G3Z1bA2A2S24S33Z0M4RdA2S34RdReA2A2S34RfZ40A2S24S33G4S5cS1bS19S19S30S3bA2M5S1cA2M6S19S14S0A2M7S1bG5S1cS1bS30S3bRcRaA4R8A4S1bS14S0S6fS6eRfReA2A4A4R11A2M8A2S34G8S5cS1bG6G7S1bG5S1cS1bS30S3bRdRbA4R9A4S1bS14S0S6fS6eR10S70A2A4A4R12A2A2A2F_;F_;F_;F_;F_;F_;F_;Fk';Fk;Fnd';Fnd;FX';FX;Finner';Fph';Fph;Frho';Frho;").
Proof.
  intros rho rho' ph ph' inner' X X' nd nd' k k' E460 E467 Hi Hc Hin Hph Hph64.
  assert (EI : uval rho' pI = uval rho pI) by (unfold uval, pI; cbn [eval]; rewrite E460; reflexivity).
  assert (EC : uval rho' xLC = uval rho xLC) by (unfold uval, xLC; cbn [eval]; rewrite E467; reflexivity).
  rewrite !efmeasA_VLA. rewrite (VLA_val rho' ph' inner') by lia. rewrite (VLA_val rho ph z0) by (unfold z0; rewrite ?uval_lit; lia).
  unfold z0. rewrite uval_lit by lia. rewrite EI, EC. pose proof (uval_range rho' inner'). pose proof (uval_range rho pI). unfold Mline, RL.
  change (2 ^ 64) with 18446744073709551616. change (2 ^ 37) with 137438953472. change (2 ^ 27) with 134217728 in *. change (2 ^ 26) with 67108864 in *. lia.
Qed.

Lemma V_B_agree : ltac2:(tb__ "0|0|
S1S1S77S57R2R1A3S15S4eS15R1S8dA3S23S4aQ40A1S6R4R2A2S6R5R2A2A3F_;Fv;F_;Frho';Frho;").
Proof.
  intros rho rho' [HV _] v Hv. symmetry. apply HV. unfold V_B in Hv. cbn [In] in Hv.
  destruct Hv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; reflexivity.
Qed.
Lemma V_L_agree : ltac2:(tb__ "0|0|
S1S1S77S57R2R1A3S15S4eS15R1S8eA3S23S4aQ40A1S6R4R2A2S6R5R2A2A3F_;Fv;F_;Frho';Frho;").
Proof.
  intros rho rho' [HV _] v Hv. symmetry. apply HV. unfold V_L in Hv. cbn [In] in Hv.
  destruct Hv as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; reflexivity.
Qed.

Lemma tvz_in_kd : ltac2:(tb__ "0|2|
S1S18S19S0S0A2M0A1S0S14S0S66R5R4A2S4eG0S1bS0S0R4SeS96S4R3A1R2A3A4R5A3S24S34Z0M1R4A2S33R4Z10A2A2S33S27R8R4A2S9eA2S25S23S14S27R9R5A2G1A3A1S25S23S14S27RaR8A2G1A3A1F_;F_;F_;F_;F_;Fk;Fe;Fd;Ftv;Frho;").
Proof.
  intros rho tv d e k HZ Hin He HK Hk Hd.
  pose proof (proj1 (Forall_forall _ _) HZ _ Hin) as Z1. cbv beta in Z1. unfold tnz, tvv in Z1. cbn [fst snd] in Z1. unfold uval in Hd, Hk, HK.
  specialize (Z1 ltac:(intros H; exact (H Hd))). unfold B32, Lib_vec_reserve.B32 in HK.
  pose proof (uval_mul_lit rho e k ltac:(lia) ltac:(unfold uval; nia)) as E1. unfold uval in E1. rewrite E1 in Z1. nia.
Qed.
End Site.

Lemma BUD_split : ltac2:(tb__ "0|2|
S18S2A1S18S28A1M0G0G0S19S14S14A2S14S14S14S1S4bS2S3R1A1R9A3S23S17S5dRaS4Z0M1A1G1R8R7A5S1aA3S29S1eS28RaR9A3R7R6R5R4R3A6S29S1eS28RbR9A3R8R7R6R5R4A6F_;F_;F_;Frho;FKf;FKm;FV;FBXv;FY;FX;Fcommon;Ffacts;").
Proof.
  intros facts common X Y BXv V Km Kf rho HF Hpay (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2).
  rewrite bd_wpos_app in Hw. apply andb_prop in Hw as [Wc Wx]. unfold bd_nn in Hn. apply Forall_app in Hn as [Nc Nx].
  destruct (bud_pay2_sound facts (SLit 0) 0 X Y rho HF Nx Hpay) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  rewrite bsumV_app in B1. rewrite bsumK_app in B2. pose proof (uval_range rho (SLit 0)).
  unfold BUD. rewrite bsumV_app, bsumK_app. rewrite bd_wpos_app, Wc, P7. repeat (split; [first [assumption | reflexivity | lia]|]).
  split; [unfold bd_nn; apply Forall_app; split; [exact Nc | exact P6]|]. lia.
Qed.

Section Split.
Variable AInv : ltac2:(tb__ "0|0|
S6dS1S18S4aQ40A1A1S59OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Variable NP' : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S18S19S19S14S14A2S14A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Lemma JA_bd_split : ltac2:(tb__ "0|2|
S18S19S0S0A2A1S18S19S19S0S14A2S0A2A1S3eS18S28A1M0G0G0S18S2A1S1S18S4aQ40A1A1S18S5aA1S59S4bS2S3R4A1R5A3S23S17S5dR6S4Z0M1A1G1R8R7A5S1aA3S3cVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S3dRdRcS1eS28RaR9A3RbA4R6R5R4R3A10S3cVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S3dReRdS1eS28RbR9A3RcA4R7R6R5R4A10F_;F_;F_;Fmd;Ftr;Ftp;Frho;Ffacts;FY;FX;Fcommon;Fam;Ffr;Ftv;").
Proof.
  intros tv fr am common X Y facts rho tp tr md HF Hpay (Ai & kc & HJ). exists Ai, kc.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HN3 & HFR & HK0 & HP0 & HXA & HBU & HPA).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN3, HFR, HXA, HBU |- *.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HN3|]. split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split; [exact HXA|]. split; [|exact HPA].
  exact (BUD_split facts common X Y _ _ _ _ rho HF Hpay HBU).
Qed.
Lemma SPA_bd_split : ltac2:(tb__ "0|2|
S18S19S0S0A2A1S18S19S19S0S14A2S0A2A1S3eS18S28A1M0G0G0S18S2A1S30S1S18S4aQ40A1A1S5bS4bS2S3R3A1R5A3S23S17S5dR6S4Z0M1A1G1R8R7A5S1aA3S4cS52S3cVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S3dRdRcS1eS28RaR9A3RbA4AcR6R5R4R3A6S4cS52S3cVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S3dReRdS1eS28RbR9A3RcA4AcR7R6R5R4A6F_;F_;F_;Fw;Ftp;Frho;FA;Ffacts;FY;FX;Fcommon;Fam;Ffr;Ftv;").
Proof.
  intros tv fr am common X Y facts A rho tp [tr [ms md]] HF Hpay [Hsm HJ]. split; [exact Hsm|].
  exact (JA_bd_split tv fr am common X Y facts rho tp tr md HF Hpay HJ).
Qed.

Lemma SPA_bd_repay : ltac2:(tb__ "0|2|
S18S19S0S0A2A1S18S19S19S0S14A2S0A2A1S3eS18S28A1M0G0G0G0G0S18S2A1S30S1S18S4aQ40A1A1S5bS23S17S6cRaS1eS28R9R8A3A2S1aA3S23S17S6cS1eS28RaR8A3R7A2S1aA3S4bS2S3R5A1R7A3S23S17S5dR8S4Z0M1A1G1RbRaA5S1aA3S4cS52S3cVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S3dR11R10ReRfA4AcR8R7R6R5A6S4cS52S3cVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S3dR12R11RbR10A4AcR9R8R7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Frho;FA;Ffacts;Fbd';FY;FX;Fcommon;Fbd;Fam;Ffr;Ftv;").
Proof.
  intros tv fr am bd common X Y bd' facts A rho tp w HP1 HP2 HF Hpay HS.
  apply (SPA_bd_permb segs AInv CST XGL NP' Kc rho0 P0f FB FF BX PA tv fr (common ++ Y) bd' am A rho tp w HP2).
  apply (SPA_bd_split tv fr am common X Y facts A rho tp w HF Hpay).
  exact (SPA_bd_permb segs AInv CST XGL NP' Kc rho0 P0f FB FF BX PA tv fr bd (common ++ X) am A rho tp w HP1 HS).
Qed.
End Split.

Definition bd_common (src tgt : list bitem) : list bitem := ltac2:(tb__ "0|0|
S50S28S28S4fS28S5eR1A1Vsrc;A3Li;Vtgt;A3").
Definition bd_minus (l other : list bitem) : list bitem := ltac2:(tb__ "0|0|
S50S28S28S22S4fS28S5eR1A1Vother;A3A1Li;Vl;A3").

Lemma pay_okF_split : ltac2:(tb__ "0|1|
S1OF_;S18S2A1S0S14S18S28A1M0G0G0G0G0S23S17S6cR5S1eS28R3R2A3A2S1aA3S23S17S6cS1eS28R4R2A3R5A2S1aA3S23S17S2dR5A1S1aA3S23S17S5dRbRaR9R5R4A5S1aA3S2fRdRcRbRaR9R8A6F_;F_;F_;F_;FY;FX;Fcommon;Fbto;Fbfrom;FcostK;FcostV;Ffacts;Fpre;").
Proof.
  intros pre facts costV costK bfrom bto common X Y HP1 HP2 Hwc Hpay.
  pose proof (bd_permb_sound _ _ HP1) as P1. pose proof (bd_permb_sound _ _ HP2) as P2.
  pose proof Hpay as H. rewrite bud_pay2_ref_eq in H; unfold bud_pay2_ref in H.
  apply lazy_andb_prop in H as [Hwx H]. apply lazy_andb_prop in H as [Hwy H]. apply lazy_andb_prop in H as [_ H]. apply lazy_andb_prop in H as [Hc _].
  apply Z.leb_le in Hc.
  split; [|split; [exact Hc|]].
  - unfold bd_wpos in *. apply forallb_forall. intros it Hit.
    assert (Hin : In it (common ++ Y)) by (eapply Permutation_in; [apply Permutation_sym; exact P2 | exact Hit]).
    apply in_app_or in Hin as [Hin|Hin]; [exact (proj1 (forallb_forall _ _) Hwc it Hin) | exact (proj1 (forallb_forall _ _) Hwy it Hin)].
  - intros rho HF Hpre Hwf Hnf.
    assert (Hn2 : bd_nn (common ++ X) rho).
    { unfold bd_nn in *. apply Forall_forall. intros it Hit. apply (proj1 (Forall_forall _ _) Hnf). eapply Permutation_in; [apply Permutation_sym; exact P1 | exact Hit]. }
    unfold bd_nn in Hn2. apply Forall_app in Hn2 as [Hnc Hnx].
    destruct (bud_pay2_sound facts costV costK X Y rho HF Hnx Hpay) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
    unfold pay_sem. rewrite (bsumV_perm bfrom (common ++ X) rho P1), (bsumK_perm bfrom (common ++ X) rho P1).
    rewrite <- (bsumV_perm (common ++ Y) bto rho P2), <- (bsumK_perm (common ++ Y) bto rho P2).
    rewrite !bsumV_app, !bsumK_app. split; [lia|]. split; [lia|].
    unfold bd_nn. apply Forall_forall. intros it Hit.
    assert (Hin : In it (common ++ Y)) by (eapply Permutation_in; [apply Permutation_sym; exact P2 | exact Hit]).
    apply in_app_or in Hin as [Hin|Hin]; [exact (proj1 (Forall_forall _ _) Hnc it Hin) | exact (proj1 (Forall_forall _ _) Q6 it Hin)].
Qed.

Section LatchExit.
Variable AInv : ltac2:(tb__ "0|0|
S6dS1S18S4aQ40A1A1S59OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Hypothesis ALA : ltac2:(tb__ "0|0|
S93S52VAInv;VCST;A3").
Variable NP' : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S18S19S19S14S14A2S14A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.
Lemma latch_exit : ltac2:(tb__ "0|1|
S30S30S7fS3bS18S19S0S0A2A1S18S28A1S3eS1OF_;S18S15A1S1S18S4aQ40A1A1S5bS60R4R5A2S23S17S32RdRcRbA3S1aA3S23S17S82RcVNP';A2S1aA3S23S17Sa5VNP';SdS31RfA1A1A2S1aA3S23S17S47SdS31R10A1A1RdA2S1aA3S23S17S6bRfS49ReA1RdA3S1aA3S23S17S44R10S48RfA1S8cA3S1aA3S23S17S5fS13S31R13A1A1S2eR11ReA2S46R10A1A3S1aA3S23S17S42S43R12ReA2S45R11A1A2S1aA3S23S17S63RdR13A2S1aA3RfRdA1S4cS52S3cVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;R14AcR17ReRdRcA6S24R11S7eRfR16A2M0A1S4cS52S3cVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S3dR14S8cR13R12A4AcR17G0ReRdA6A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FV;FPhi;Fam;Fbdj;Ftvj;Fndi;Fs;FT;FL;").
Proof.
  intros L T s ndi tvj bdj am Phi V rho tp w HR He Hid Hnp Hnb Htv Hfr Hbd Ham HV HP HS. split.
  - exact (phi_sub V Phi HR s rho HV HP).
  - exact (SPA_entails_JA2 segs AInv CST XGL ALA NP' Kc rho0 P0f FB FF BX PA HKc L T s ndi (NDA tvj frL bdj am) rho tp w He Hid Hnp Hnb Htv Hfr Hbd Ham HS).
Qed.
End LatchExit.

Lemma efmeasA_sub : ltac2:(tb__ "0|4|
S30S30S3bS3bS1cS1cS14S0S7fS1S23S0S81R2R3A2R3A3S23S14S5cS1bS19S19S30S3bA2M0S1cA2M1S19S14S0A2M2S1bG0S1cS1bS30S3bRbR9A4R7A4S1bS14S0R5R4A4M3A4S7eR2R3A2A2S5cS1bG1G2S1bG0S1cS1bS30S3bRaR8A4R6A4G3A4R2A2A3F_;Frho;Fs;Fe;Fr;Fk';Fk;Fnd';Fnd;FX';FX;").
Proof. intros X X' nd nd' k k' r e s rho He. unfold efmeasA. cbn [ef_rank ef_var fst snd]. rewrite <- eval_subst, He. reflexivity. Qed.

Lemma BUD_split_sem : ltac2:(tb__ "0|1|
S18S2A1S18S28A1M0G0G0S19S14S14A2S14S14S14S1S4bS2S3R1A1R9A3S23S17S2dR7A1S1aA3S4bS2S3R3A1RbA3S2aRaR4A2S24S33S2cRaR5A2S2cRbR5A2A2S24S33S2bRaR5A2S2bRbR5A2A2S2aRaR5A2A2A2F_;F_;S29S1eS28RbRaA3R8R7R6R5R4A6S29S1eS28RcRaA3R9R8R7R6R5A6F_;F_;F_;F_;Frho;FKf;FKm;FV;FBXv;FY;FX;Fcommon;Ffacts;").
Proof.
  intros facts common X Y BXv V Km Kf rho HF HwY Hsem (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2).
  rewrite bd_wpos_app in Hw. apply andb_prop in Hw as [Wc Wx]. unfold bd_nn in Hn. apply Forall_app in Hn as [Nc Nx].
  destruct (Hsem HF Nx) as (P1 & P2 & P6).
  rewrite bsumV_app in B1. rewrite bsumK_app in B2.
  unfold BUD. rewrite bsumV_app, bsumK_app. rewrite bd_wpos_app, Wc, HwY. repeat (split; [first [assumption | reflexivity | lia]|]).
  split; [unfold bd_nn; apply Forall_app; split; [exact Nc | exact P6]|]. lia.
Qed.
Section SplitSem.
Variable AInv : ltac2:(tb__ "0|0|
S6dS1S18S4aQ40A1A1S59OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Variable NP' : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S18S19S19S14S14A2S14A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Lemma SPA_bd_repay_sem : ltac2:(tb__ "0|1|
S18S19S0S0A2A1S18S19S19S0S14A2S0A2A1S3eS18S28A1M0G0G0G0G0S18S2A1S30S1S18S4aQ40A1A1S5bS23S17S6cRaS1eS28R9R8A3A2S1aA3S23S17S6cS1eS28RaR8A3R7A2S1aA3S23S17S2dR9A1S1aA3S4bS2S3R6A1R8A3S4bS2S3R7A1R9A3S2aRdR8A2S24S33S2cRdR9A2S2cReR9A2A2S24S33S2bRdR9A2S2bReR9A2A2S2aRdR9A2A2A2F_;F_;S4cS52S3cVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S3dR12R11RfR10A4AcR9R8R7R6A6S4cS52S3cVAInv;VCST;VXGL;VNP';VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;S3dR13R12RcR11A4AcRaR9R8R7A6F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FA;Ffacts;Fbd';FY;FX;Fcommon;Fbd;Fam;Ffr;Ftv;").
Proof.
  intros tv fr am bd common X Y bd' facts A rho tp w HP1 HP2 HwY HF Hsem HS.
  apply (SPA_bd_permb segs AInv CST XGL NP' Kc rho0 P0f FB FF BX PA tv fr (common ++ Y) bd' am A rho tp w HP2).
  pose proof (SPA_bd_permb segs AInv CST XGL NP' Kc rho0 P0f FB FF BX PA tv fr bd (common ++ X) am A rho tp w HP1 HS) as HS1.
  destruct w as [tr [ms md]]. destruct HS1 as [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HN3 & HFR & HK0 & HP0 & HXA & HBU & HPA).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN3, HFR, HXA, HBU |- *.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HN3|]. split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split; [exact HXA|]. split; [|exact HPA].
  exact (BUD_split_sem facts common X Y _ _ _ _ rho HF HwY Hsem HBU).
Qed.
End SplitSem.

Lemma efmeasA_VLA_sub : ltac2:(tb__ "0|6|
S30S30S3bS3bS1cS1cS14S14S7fS1S23S0S80R2P1ccM0A2SaG0A1A3S23S0S80R3P1d3M1A2SaG1A1A3S23S14S5cS1bS19S19S30S3bA2M2S1cA2M3S19S14S0A2M4S1bG2S1cS1bS30S3bRcRaA4R8A4S1bS14S0R6S6eR5S70A2A4M5A4S7eR3R4A2A2S5cS1bG3G4S1bG2S1cS1bS30S3bRbR9A4R7A4G5A4R3A2A3F_;F_;Frho;Fs;Fph;Fr;Fk';Fk;Fnd';Fnd;FX';FX;").
Proof.
  intros X X' nd nd' k k' r ph s rho H460 H467. unfold efmeasA. cbn [ef_rank ef_var fst snd]. f_equal. f_equal.
  unfold VLA, z0, xLC, pI. cbn [eval]. unfold rho_sub. cbn [rw]. rewrite H460, H467. reflexivity.
Qed.
