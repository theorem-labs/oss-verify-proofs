(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sprop"; "SLit"; "SVar"; "ss_next"; "ss_facts"; "rw"; "sobj"; "SAlu"; "SPBranch"; "SPUle"; "agree_below"; "sprop_eqb"; "sstate"; "ss_objs"; "swf"; "SPNot"; "eval"; "holds"; "mkSS"; "rm"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "@Corelib.Init.Datatypes"; "list"; "prod"; "cons"; "bool"; "true"; "app"; "nil"; "pair"; "length"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA"; "bitem"; "BIc"; "BUD"; "KU"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_X"; "ax_setS"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA"; "NDA"; "AHeadN"; "AHead"; "ANone"; "ND"; "nd_below"; "ndesc"; "AK0"; "AV0"; "JA"; "JAi"; "TPA"; "chainZ"; "@Stdlib.PArith.BinPos.Pos"; "add"; "leb"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "AA"; "aa_geom"; "topG"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "ax_setX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD.WithSegs.D"; "lenN_stateA"; "pop_stateA"; "tail_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAD.WithSegs"; "ghost_factsA"; "link_factA"; "two52"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR"; "e32"; "hdr_cells"; "open_factsA"; "plain_obj"; "robjs_okF"; "xrs_ok47"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "IMG_HI"; "SHADOW_OFF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "T_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAy"; "null_entry"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "set_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "alloc_lawsA"; "@stdpp.base"; "NoDup"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjArena.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TobjJVA TobjJVAy InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Geometry Budget Model RtCells Iface GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require BudA CfgGenTA TobjJA TobjJAM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require h2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require TobjJAR.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.BudA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.CfgGenTA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h0.TobjJAX OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h1.TobjJAC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.CertGlueA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.TobjJAR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.h2.TobjJAH.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma BUD_const_absorb : ltac2:(tb__ "0|3|
S1eS28A1S0S0S0S0S0S0S0S0S3S2aS23S28RaS20S28S29Z1M0Z0M1R6A3S20S28S29G1G0R5A3S24S28A1A3A3A3S25S0S0S47R9G1A2S47S47R8G1A2R7A2A4R4R3R2R1A6S48G1R7A2M2G2S2aRdS25S0S0S47RcR9A2S47S47RbR8A2RaA2A4R7R6R5R4A6F_;F_;F_;Frho;FKf;FKm;FV;Fpk;Fpv;Fkc;Fx2;Fx1;Fb;").
Proof.
  intros b x1 x2 kc pv pk V Km Kf rho H Hpv Hpk.
  pose proof H as (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2). cbn [fst snd] in *.
  rewrite bsumV_app in B1. rewrite bsumK_app in B2. rewrite bd_wpos_app in Hw. apply andb_prop in Hw as [Hw _].
  unfold BIc in B1, B2. cbn [bsumV bsumK bi_v bi_k] in B1, B2. unfold bival in B1, B2. cbn [lfval bi_f bi_c] in B1, B2.
  apply bd_nn_app in Hn as [Hn _].
  unfold BUD. cbn [fst snd]. repeat (split; [first [assumption | lia]|]). lia.
Qed.

Ltac top_rng H := match type of H with context [topG ?G] => let TG := fresh "TG" in pose proof (topG_range G) as TG end.

Section WithSegs.
Variable segs : list Segment.
Variable AInv : ltac2:(tb__ "0|0|
S4eS3S1eS45Q40A1A1S51OF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
S1eS1fS1fS0S0A2S0A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Context {dF : Z}.
Hypothesis HBX : BXok_d dF BX.

Let JA : ltac2:(tb__ "0|0|
S3cS35Fnd;") := ltac2:(tb__ "0|0|
S3fVAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").

Lemma JA_arena_init : ltac2:(tb__ "0|2|
S1eS1fS2S2A2A1S1eS1fS1fS2S0A2S2A2A1S1eS28A1S30S3S1eS45Q40A1A1S4cS34Vsegs;VJA;S36R7R6S23S28R5S20S28S29Z1M0Z0M1S3eA3S20S28S29G1G0S3dA3S24S28A1A3A3A3S39A4A1R4R3R2R1A6S34Vsegs;VJA;S36R8R7R6S38S5G1A1S22A2A4A1R5R4R3R2A6F_;Fw;Ftp;Frho;FA;Fbd;Ffr;Ftv;").
Proof using HBX.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd A rho tp w [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, 0.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HNDZ & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HNDZ, HFR, HXA, HBU |- *.
  unfold XA in HXA. cbn [am_eval] in HXA. destruct HXA as [HXA HCEN]. cbn [XAz0] in HXA. subst kc.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HNDZ|]. split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split.
  - unfold XA. cbn [nd_am nd_tv am_eval]. unfold uval. rewrite U_lit. change (0 mod M64v) with 0. split.
    2: { apply (lcenZ_mode FB ANz); [intros bn []| exact HCEN]. }
    cbn -[chainZ KU]. exists []. split; [|reflexivity].
    split; [reflexivity|]. split; [constructor | constructor].
  - split; [|exact (conj HPA (conj HCKi HCNi))].
    cbn [nd_bd nd_am]. unfold apot in HBU |- *. cbn [am_eval apotz] in HBU |- *. unfold uval. rewrite U_lit. change (0 mod M64v) with 0.
    unfold areq. rewrite Z.eqb_refl. unfold bxa in HBU |- *. cbn [fst snd] in HBU |- *.
    apply (BUD_const_absorb bd (fst (bx2 BX)) (snd (bx2 BX)) 0 AV0 AK0); [exact HBU | unfold AV0; lia | unfold AK0, KU; lia].
Qed.

Lemma JA_head0_none : ltac2:(tb__ "0|0|
S1eS1fS2S2A2A1S1eS1fS1fS2S0A2S2A2A1S1eS28A1S2S21S30S3S1eS45Q40A1A1S4cS2cS21S54S4SfScS53R6S5Z0A1A3A1S8S2fR4A1A1A3S22A3S34Vsegs;VJA;S36RaR9R8S38R7R6A2A4A1R5R4R3R2A6S34Vsegs;VJA;S36RbRaR9S39A4A1R6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fpot;Fhd;Fbd;Ffr;Ftv;").
Proof using HBX.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd hd pot A rho tp w Hz [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, 0.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HNDZ & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HNDZ, HFR, HXA, HBU |- *.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  assert (Hh : uval rho hd = 0).
  { pose proof (holds_mem _ _ _ HF Hz) as F0. apply (proj1 (holds_beq _ _ _)) in F0. change (bv_unsigned (eval rho hd)) with (uval rho hd) in F0.
    rewrite U_lit in F0. change (0 mod M64v) with 0 in F0. exact F0. }
  unfold XA in HXA. cbn [nd_am nd_tv am_eval] in HXA. rewrite Hh in HXA. destruct HXA as [HXA HCEN]. cbn -[chainZ KU] in HXA. destruct HXA as (ns & [HA _] & Hkc).
  pose proof (achain_nil _ _ HA) as ->. cbn [length Z.of_nat] in Hkc. rewrite Z.mul_0_r in Hkc. subst kc.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HNDZ|]. split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split.
  { unfold XA. cbn [nd_am nd_tv am_eval]. split; [reflexivity|].
    apply (lcenZ_mode FB (AHz 0 pot)); [|exact HCEN]. intros bn (ns' & HA' & Hin'). pose proof (achain_nil _ _ HA') as ->. destruct Hin'. }
  split; [|exact (conj HPA (conj HCKi HCNi))].
  cbn [nd_bd nd_am]. unfold apot in HBU |- *. cbn [am_eval apotz] in HBU |- *. rewrite Hh in HBU. unfold bxa in HBU |- *. cbn [fst snd] in HBU |- *.
  pose proof (apot_range (AHead hd pot) rho) as _.
  assert (HP : exists pv pk, 0 <= pv /\ 0 <= pk /\ BUD bd (fst (bx2 BX) + pv, snd (bx2 BX) + pk + 0) (aa_V Ai) (aa_Km Ai) (aa_Kf Ai) rho).
  { destruct pot.
    - exists (fst (areq (rm rho) 0)), (snd (areq (rm rho) 0)). pose proof (areq_range (rm rho) 0). split; [lia|]. split; [lia|]. exact HBU.
    - exists 0, 0. split; [lia|]. split; [lia|]. exact HBU. }
  destruct HP as (pv & pk & Hpv & Hpk & HB').
  apply (BUD_bx_ext bd (fst (bx2 BX), snd (bx2 BX))); [cbn; lia | cbn; lia |].
  apply (BUD_bx_drop bd (fst (bx2 BX)) (snd (bx2 BX)) pv pk); [ | exact (proj1 (BXok_d_pair _ BX HBX)) | exact (proj2 (BXok_d_pair _ BX HBX)) | exact Hpv | exact Hpk].
  apply (BUD_bx_ext bd (fst (bx2 BX) + pv, snd (bx2 BX) + pk + 0)); [cbn; lia | cbn; lia | exact HB'].
Qed.

Lemma JA_add_nulls : ltac2:(tb__ "0|2|
S1eS1fS2S2A2M0A1M1G1S1eS1fS1fS2S0A2S2A2A1S1eS28A1S30S3S1eS45Q40A1A1S4cS2cS21S55G0S6aR7A3S22A3S34Vsegs;VJA;S3aR9R7R6A3A1R5R4R3R2A6S34Vsegs;VJA;S3aS23G0RaR9A3R8R7A3A1R6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fbd;Ffr;Fnl;Ftv;").
Proof using .
  intros tv nl fr bd A rho tp w Hn [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  unfold JAi. cbn [nd_tv nd_fr nd_bd nd_am ND] in *.
  assert (HCNT : cntS rho tv <= cntS rho (tv ++ nl)) by (rewrite cntS_app; pose proof (cntS_bounds rho nl); lia).
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [|split; [exact HFR|split; [exact HK0|split; [exact HP0|split; [|split; [exact HBU|exact (JA_tail_le _ _ _ rho rho tv (tv ++ nl) HCNT (conj HPA (conj HCKi HCNi)))]]]]]].
  2: { unfold XA in HXA |- *. cbn [am_eval] in HXA |- *. destruct HXA as [HXA HCEN]. split; [exact HXA|].
       intros bn L1 L2 L3 L4. apply (HCEN bn L1 L2 L3). intros v Hv. apply L4. unfold tvals in *. rewrite map_app. apply in_or_app. left. exact Hv. }
  split; [|split].
  - unfold tvinA in *. rewrite Forall_app. split; [exact HN|]. apply Forall_forall. intros t Ht Hnz.
    exfalso. exact (TobjJVAy.null_entry_not_tnz rho t (proj1 (forallb_forall _ _) Hn t Ht) Hnz).
  - apply TobjJVAy.tvd_app_nulls; [exact Hn | exact HD].
  - unfold tvz in *. rewrite Forall_app. split; [exact HZ|]. apply Forall_forall. intros t Ht _.
    apply TobjJVAy.null_entry_size0. exact (proj1 (forallb_forall _ _) Hn t Ht).
Qed.

Definition two52 : Z := 2 ^ 52.
Definition ghost_factsA (g : positive) : list sprop := ltac2:(tb__ "0|1|
S20S4SdS5ZfA1S6Vg;A1M0A2S20S4SdG0S5S5eA1A2S24S4A1A3A3").

Definition link_factA (g : sv) (g' : positive) : sprop := ltac2:(tb__ "0|0|
SdSbS52S6Vg';A1S5Z10A1A3Vg;A2").

Lemma BUD_kc_item : ltac2:(tb__ "0|1|
S1eS28A1S0S0S0S0S0S0S3S2aR8S25S0S0R7S47R6R5A2A4R4R3R2R1A6S48S2bR6A2S48Z0M0R8A2S2aS23S28RbS20S28S29G0Z1S2bA3S24S28A1A3A3S25S0S0RaS47R9S4bR8S2bA2A2A4R7R6R5R4A6F_;F_;F_;Frho;FKf;FKm;FV;Fkc;Fx2;Fx1;Fb;").
Proof.
  intros b x1 x2 kc V Km Kf rho H Hk Hx2.
  pose proof H as (A1 & A2 & A3 & A4 & A5 & Hw & Hn & B1 & B2). cbn [fst snd] in *.
  unfold BUD. cbn [fst snd]. rewrite bsumV_app, bsumK_app, bd_wpos_app, Hw. unfold BIc. cbn [bsumV bsumK bi_v bi_k bd_wpos forallb andb Z.leb].
  unfold bival. cbn [lfval bi_f bi_c]. unfold KU in *.
  split; [lia|]. split; [lia|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [reflexivity|].
  split; [apply bd_nn_app; split; [exact Hn | repeat constructor; unfold bival; cbn [lfval bi_f bi_c]; lia]|]. lia.
Qed.

Lemma NoDup_range_length : ltac2:(tb__ "0|1|
S1eS0A1S0S48Z0R1A2M0S6eS0R3A2S56S0S0S2dG0S49R1R4A2A2Lz;R4A3S48S4aS26S0R5A2A1R4A2F_;F_;F_;Fhi;Fl;").
Proof.
  intros l hi Hhi HD HF. apply NoDup_ListNoDup in HD.
  assert (HI : incl l (map Z.of_nat (seq 0 (Z.to_nat hi)))).
  { intros z Hz. pose proof (proj1 (Forall_forall _ _) HF z Hz) as Rz. cbv beta in Rz. apply in_map_iff. exists (Z.to_nat z). split; [lia|]. apply in_seq. lia. }
  pose proof (NoDup_incl_length HD HI) as L. rewrite length_map, length_seq in L. lia.
Qed.

Section D.
Hypothesis ALA : ltac2:(tb__ "0|0|
S6dVsegs;VAInv;VCST;A3").
Hypothesis HCST : ltac2:(tb__ "0|0|
S0S67VCST;R1A2S2dS48Z0R2A2S49R2S65A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S67VXGL;R1A2S2dS48Z0R2A2S49R2S65A2A2F_;Fa;").
Hypothesis HKc : Kc_ok Kc.
Hypothesis HNP : NP_okA NP.
Let JAi : ltac2:(tb__ "0|0|
S3cS4eS0S35Fkc;FAi;Fnd;") := ltac2:(tb__ "0|0|
S40VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").

Lemma chain_len_boundA : ltac2:(tb__ "0|2|
S4eS3S1eS45Q40A1A1S51S1eS1fS0S0A2M0A1M1S0G1VAInv;R7R6R5R4A4S42VFB;R8S17R7A1R4R3R2A6S48S4aS26G0R3A2A1Z7fffff800000A2F_;F_;Fns;Fh;Ftvs;Fmd;Ftp;Frho;FAi;").
Proof using ALA.
  intros Ai rho tp md tvs h ns HM [HA [HF HND]].
  rewrite <- (length_map fst). apply NoDup_range_length; [lia | exact HND |].
  apply Forall_forall. intros b Hb. apply in_map_iff in Hb as ([b' cap] & <- & Hin). cbn [fst].
  destruct (proj1 (Forall_forall _ _) HF _ Hin) as (Hblk & _). cbn [fst snd] in Hblk.
  destruct (law_blocks _ _ _ ALA Ai rho tp md HM) as (_ & HBl & _). destruct (HBl _ _ Hblk) as (G1 & _ & G3 & G4 & _).
  top_rng G4. lia.
Qed.

Definition lenN_stateA (A : axst) : axst := ltac2:(tb__ "0|0|
S2fVA;A1S10S7R1A1S1S57S32VA;S6cR2S43R1P1A2A2A2S23S4S5cR1A1S8R2A1A3A2Tn;TS;").

Lemma JA_lenN : ltac2:(tb__ "0|1|
S1eS1fS2S2A2A1S1eS1fS1fS2S0A2S2A2A1S1eS28A1S2S21S30S3S1eS45Q40A1A1S4cS2cS21S12S2fS59R4A1A1A1S22A3S2cS21S44VNP;S7S2fR5A1A1A2S22A3S2cS21S3bS7S2fR6A1A1S36RbRaR9S38R8R7A2A4A2S22A3S34Vsegs;VJA;S36RcRbRaS38R9R8A2A4A1R7R6R5R4A6S2eS3S3S2dSeS7S2fR9A1A1M0R8R1A3S34Vsegs;VJA;S36ReRdRcS37RbS6G0A1A2A4A1S59R9A1R1R7R6A6A2Lrho';A2F_;F_;F_;F_;Fw;Ftp;Frho;FA;Fpot;Fhd;Fbd;Ffr;Ftv;").
Proof using ALA HBX HKc.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd hd pot A rho tp w Hwf Hnp Hnb [Hsm (Ai & kc & HJ)]. destruct w as [tr [ms md]]. apply Pos.leb_le in Hnp.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  destruct (nd_below_split _ _ Hnb) as (Hbt & Hbf & Hbb & Hba). cbn [nd_tv nd_fr nd_bd nd_am am_below] in Hbt, Hbf, Hbb, Hba.
  unfold XA in HXA. cbn [am_eval] in HXA. destruct HXA as [HXA HCEN]. cbn -[chainZ KU] in HXA. destruct HXA as (ns & HC & Hkc).
  pose proof (chain_len_boundA Ai rho tp md _ _ ns HM HC) as HLB.
  set (n := ss_next (ax_S A)) in *.
  set (v := 16 * Z.of_nat (length ns) + 15).
  set (rho' := rho_set_rw rho n (Z_to_bv 64 v)).
  assert (Hag : agree_below n rho rho').
  { subst rho'. split; [|split; intros; reflexivity]. intros i Hi. unfold rho_set_rw. cbn [rw].
    replace (Pos.eqb i n) with false; [reflexivity|]. symmetry. apply Pos.eqb_neq. lia. }
  assert (Uv : bv_unsigned (rw rho' n) = v).
  { subst rho'. unfold rho_set_rw. cbn [rw]. rewrite Pos.eqb_refl. rewrite Z_to_bv_unsigned. apply bv_wrap_small. rewrite two64. subst v. lia. }
  assert (Hrm : rm rho' = rm rho) by reflexivity.
  clearbody rho'.
  exists rho'. split; [exact Hag|].
  assert (HJ' : JAi (NDA tv fr bd (AHead hd pot)) Ai kc rho' tp tr md).
  { eapply (JAi_stable segs AInv CST XGL NP Kc rho0 P0f FB FF BX PA HKc ALA n); [lia | exact Hnb | exact Hag | apply mat_equiv_refl | exact HJ]. }

  assert (SP1 : SPA segs (TobjJA.JAi AInv CST XGL NP Kc rho0 P0f FB FF BX PA (NDA tv fr bd (AHead hd pot)) Ai kc) (ax_setS A (set_next (ax_S A) (n + 1))) rho' tp (tr, mkCfg ms md)).
  { apply SPA_set_next.
    - split; [exact (smatchA_agree segs rho rho' tp A _ Hag Hsm) | exact HJ'].
    - pose proof (proj1 (proj2 (proj2 Hsm))) as HwfA. unfold axwf in HwfA |- *. cbn [ax_S ax_setS ax_X ax_base set_next ss_next] in HwfA |- *. fold n in HwfA.
      apply andb_prop in HwfA as [HX1 HX2]. apply andb_true_intro. split.
      + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX1 rr Hr) as Y. unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
        apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
      + eapply sv_below_mono; [|exact HX2]. lia.
    - unfold lenN_stateA, ax_with_facts, with_facts in Hwf. cbn [ax_S ax_setS set_next ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in Hwf. fold n in Hwf.
      unfold set_next. eapply swf_facts_suffix. exact Hwf. }
  assert (G12 : Forall (holds rho') (ghost_factsA n)).
  { unfold ghost_factsA, two52. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [holds]; rewrite U_lit; cbn [eval]; rewrite Uv; unfold M64v; rewrite Z.mod_small by lia; subst v; lia. }
  pose proof (SPA_refacts segs _ rho' _ (ghost_factsA n ++ ss_facts (ax_S A)) tp (tr, mkCfg ms md) SP1) as SP2.
  unfold lenN_stateA. fold n. split.
  - apply SP2.
    + unfold lenN_stateA, ax_with_facts, with_facts in Hwf. cbn [ax_S ax_setS set_next ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in Hwf. fold n in Hwf.
      pose proof (swf_facts _ Hwf) as WFF. cbn [ss_facts ss_next] in WFF. exact WFF.
    + intros HF'. apply Forall_app. split; [exact G12 | exact HF'].
  -
    exists Ai, kc. pose proof HJ' as (Hav' & _ & HM' & HT' & _ & _ & HN3' & HFR' & HK0' & _ & HXA' & HBU' & HPA').
    cbn [nd_tv nd_fr nd_bd nd_am] in HN3', HFR', HXA', HBU'.
    split; [exact Hav'|]. split; [exact Hk|]. split; [exact HM'|]. split; [exact HT'|]. split; [exact HB|]. split; [exact HFF|].
    split; [exact HN3'|]. split; [exact HFR'|]. split; [exact HK0'|]. split; [exact HP0|]. cbn [nd_tv nd_fr nd_bd nd_am]. split; [|split; [|exact HPA']].
    + unfold XA in HXA' |- *. cbn [am_eval] in HXA' |- *. destruct HXA' as [HXA' HCEN']. split; [|exact HCEN'].
      cbn -[chainZ KU] in HXA' |- *. destruct HXA' as (ns' & HC' & Hkc').
      exists ns'. split; [exact HC'|]. split; [exact Hkc'|]. unfold uval. cbn [eval]. rewrite Uv. subst v.
      assert (length ns' = length ns).
      {
        rewrite Hkc in Hkc'. unfold KU in Hkc'. lia. }
      rewrite H. lia.
    + unfold apot in HBU' |- *. cbn [am_eval apotz] in HBU' |- *. unfold bxa in HBU' |- *. cbn [fst snd] in HBU' |- *.
      destruct pot.
      * pose proof (areq_range (rm rho') (uval rho' hd)) as [R1 R2]. pose proof (XAz_kc_nonneg _ _ _ _ _ _ HXA') as Hkc0.
        apply (BUD_bx_ext bd (fst (bx2 BX), snd (bx2 BX) + kc)); [cbn; lia | cbn; lia |].
        apply (BUD_bx_drop bd (fst (bx2 BX)) (snd (bx2 BX) + kc) (fst (areq (rm rho') (uval rho' hd))) (snd (areq (rm rho') (uval rho' hd))));
          [ | exact (proj1 (BXok_d_pair _ BX HBX)) | lia | lia | lia].
        revert HBU'. apply BUD_bx_ext; cbn [fst snd]; lia.
      * exact HBU'.
Qed.

Lemma rw_set4 : ltac2:(tb__ "0|4|
S3S1S45Q40A1M0G0G0G0S4dS4dS4dS4dR6R5R4A3S43R5P1M1A2R3A3S43R5P2M2A2R2A3S43R5P3M3A2R1A3S3S2dS2cG0S9R1R6A2R5A3S2dS2cG0S9R1S43R6G1A2A2R4A3S2dS2cG0S9R1S43R6G2A2A2R3A3S2dS2cG0S9R1S43R6G3A2A2R2A3SeR6R7R1A3A2A2A2A2Trho';Ft;Fz;Fy;Fx;Fn;Frho;").
Proof using .
  clear. intros rho n x y z t. unfold rho_set_rw. cbn [rw].
  assert (E1 : Pos.eqb n (n + 3) = false) by (apply Pos.eqb_neq; lia).
  assert (E2 : Pos.eqb n (n + 2) = false) by (apply Pos.eqb_neq; lia).
  assert (E3 : Pos.eqb n (n + 1) = false) by (apply Pos.eqb_neq; lia).
  assert (E4 : Pos.eqb (n + 1) (n + 3) = false) by (apply Pos.eqb_neq; lia).
  assert (E5 : Pos.eqb (n + 1) (n + 2) = false) by (apply Pos.eqb_neq; lia).
  assert (E6 : Pos.eqb (n + 2) (n + 3) = false) by (apply Pos.eqb_neq; lia).
  rewrite E1, E2, E3, E4, E5, E6, !Pos.eqb_refl. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [|split; intros; reflexivity]. intros i Hi. cbn [rw].
  assert (A0 : Pos.eqb i (n + 3) = false) by (apply Pos.eqb_neq; lia). assert (B0 : Pos.eqb i (n + 2) = false) by (apply Pos.eqb_neq; lia).
  assert (C0 : Pos.eqb i (n + 1) = false) by (apply Pos.eqb_neq; lia). assert (D0 : Pos.eqb i n = false) by (apply Pos.eqb_neq; lia).
  rewrite A0, B0, C0, D0. reflexivity.
Qed.

Definition tail_obj (hd : sv) (n : positive) : sobj := ltac2:(tb__ "0|0|
S62SbS52Vhd;S5Z18A1A3SbS52S6S43Vn;P1A2A1S5Z8A1A3A2").
Definition pop_stateA (A : axst) (hd g : sv) : axst := ltac2:(tb__ "0|1|
S2fVA;A1S10S7R1A1S1S16S1bR2A1S1cR2A1S19R2A1S18R2A1S1dR2A1S23SaS11R2A1S20SaS6bVhd;Z0Z18S60R1A1A4S20SaS5bVhd;R1A2S24SaA1A3A3A3S8R2A1S43R1P4A2S1aR2A1A9S10S57S58S32VA;R1A2S20S1fS2S2A2S25S2S2Vhd;S5fS6S43R2P1A2A1A1A4S31VA;A1A3A2S23S4S23S4S61Vhd;R2A2S23S4S5cS43R2P3A2M0A1S20S4S5dVg;G0A2S24S4A1A3A3A3S8R3A1A3A2TS';Tn;TS;").

Lemma JA_popN : ltac2:(tb__ "0|6|
S1eS1fS2S2A2M0A1S1eS1fS1fS2S0A2S2A2A1S1eS28A1S2S2S30S3S1eS45Q40M1A1A1M2S4cS2cS21S12S2fS5aR4R6R5A3A1A1S22A3S2cS2S33R5A1S5S66A1A3S2cS21S44VNP;S7S2fR6A1A1A2S22A3S2cS21S3bS7S2fR7A1A1S36RcRbRaS37R9R8A2A4A2S22A3S2cS21S54S4SfS13ScS53RaS5Z0M3A1A3A1A1S8S2fR8A1A1A3S22A3S4eS3G2S51S56S4S15RcA1S8S2fRdA1A1A3VP0f;Vrho0;A1S68VNP;Vrho0;ReA3VAInv;R7R6R5R4A4S41Vrho0;R8A2S69R11S50S4fR9A1A1A2S2dS63VCST;Vrho0;VFB;VFF;R12R18R17S11S2fR13A1A1A8S64R12S31R13A1A2A2F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FAi;S34Vsegs;VJA;S36RfReRdS37RcRbA2A4A1RaR9R8R7A6S2eS3S3S2dSeS7S2fRcA1A1M4RbR1A3S2dS34Vsegs;VJA;S36S20G0S25S2S2ReS5fS6S43G4P1A2A1A1A4R11A3R10S23S28RfS20S28S29G3Z1S2bA3S24S28A1A3A3S37S6G4A1S6S43G4P3A2M5A1A2A4A1S5aRcReRdA3R1RaR9A6S2cS0S47S46G1S9R1G5A2A2Z10A2S46G1S14RbRdA2A2A3A2A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FA;Fg;Fhd;Fbd;Ffr;Ftv;").
Proof using ALA HCST HXGL HBX HKc HNP.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd hd g A rho tp w Hwf Hbase Hnp Hnb Hnz HSITE [Hsm (Ai & kc & HJ)].
  destruct w as [tr [ms md]]. apply Pos.leb_le in Hnp.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HN, HD, HZ, HFR, HXA, HBU.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  destruct (HSITE Ai rho tp md HF HP0 Hav HM HT (T_ok_of_TPA NP rho0 HNP rho Ai Hav HT)) as [HROK HX47].
  destruct (nd_below_split _ _ Hnb) as (Hbt & Hbf & Hbb & Hba). cbn [nd_tv nd_fr nd_bd nd_am am_below] in Hbt, Hbf, Hbb, Hba.
  apply andb_prop in Hba as [Hba Hbg].

  unfold XA in HXA. destruct HXA as [HXA HCEN]. cbn -[chainZ KU uval] in HXA. cbn [am_eval] in HCEN. destruct HXA as (ns & HC & Hkc & HG).
  assert (Hh : uval rho hd <> 0).
  { exact (tnz_of_fact rho hd (SLit 0) (holds_mem _ _ _ HF Hnz)). }
  destruct HC as (HA & HNS & HND).
  destruct (achain_cons (rm rho) _ ns HA Hh) as (cap & r & ->).
  pose proof HA as HA0.
  cbn [achain] in HA. destruct HA as (_ & _ & Hcap0 & Hrd8 & (u & Hrd16 & Hu) & Hdef & (nx & Hrd0 & HAr)).
  set (h := uval rho hd) in *.
  pose proof (Forall_inv HNS) as HNh. pose proof (Forall_inv_tail HNS) as HNr.
  destruct HNh as (Hlive & Hnfb & Hut & Hcap & Hcap32 & Hxm). cbn [fst snd] in Hlive, Hnfb, Hut, Hcap, Hcap32, Hxm.
  destruct (law_blocks' segs AInv CST ALA HCST Ai rho tp md HM) as (HPD & HBl & HFr).
  destruct (HBl h (HDR + cap) Hlive) as (G1 & G2 & G3 & G4 & G5). unfold HDR in G4, G5. unfold HDR in Hcap32.
  pose proof (rd64_range _ _ _ Hrd0) as Rnx. pose proof (rd64_range _ _ _ Hrd8) as Rcap. pose proof (rd64_range _ _ _ Hrd16) as Ru.
  cbn [length] in Hkc, HG. rewrite Nat2Z.inj_succ in Hkc, HG.
  set (G := uval rho g) in *. set (n := ss_next (ax_S A)) in *.
  destruct (rw_set4 rho n (Z_to_bv 64 nx) (Z_to_bv 64 cap) (Z_to_bv 64 u) (Z_to_bv 64 (G - 16))) as (R0 & R1 & R2 & R3 & Hag).
  set (rho' := rho_set_rw (rho_set_rw (rho_set_rw (rho_set_rw rho n (Z_to_bv 64 nx)) (n + 1) (Z_to_bv 64 cap)) (n + 2) (Z_to_bv 64 u)) (n + 3) (Z_to_bv 64 (G - 16))) in *.
  assert (Hrm : rm rho' = rm rho) by reflexivity.
  assert (Ehd : eval rho' hd = eval rho hd) by (symmetry; apply (eval_agree n); [exact Hag | exact Hba]).
  assert (Eg : eval rho' g = eval rho g) by (symmetry; apply (eval_agree n); [exact Hag | exact Hbg]).
  clearbody rho'.
  exists rho'. split; [exact Hag|].
  pose proof (agree_below_vals _ _ _ Hag) as Hagv.
  pose proof (Nat2Z.is_nonneg (length r)) as Hlen.
  assert (Ucap : bv_unsigned (rw rho' (n + 1)%positive) = cap) by (rewrite R1, Z_to_bv_unsigned; apply bv_wrap_small; rewrite two64; lia).
  assert (Uu : bv_unsigned (rw rho' (n + 2)%positive) = u) by (rewrite R2, Z_to_bv_unsigned; apply bv_wrap_small; rewrite two64; lia).
  assert (Unx : bv_unsigned (rw rho' n) = nx) by (rewrite R0, Z_to_bv_unsigned; apply bv_wrap_small; rewrite two64; lia).
  assert (Ug' : bv_unsigned (rw rho' (n + 3)%positive) = G - 16) by (rewrite R3, Z_to_bv_unsigned; apply bv_wrap_small; rewrite two64; unfold G in *; pose proof (uval_range rho g); lia).
  assert (Uhd : bv_unsigned (eval rho' hd) = h) by (rewrite Ehd; reflexivity).

  assert (DISJ : forall a, h <= a < h + (HDR + cap) -> forall o, In o (ss_objs (ax_S A)) -> ~ (fst (obj_range rho o) <= a < snd (obj_range rho o))).
  { intros a Ha. eapply (chain_block_free segs AInv CST ALA HCST rho0 FB FF Ai rho tp md tv fr); eauto. }
  assert (HNx : tvinA FB Ai rho (tv ++ [])) by (rewrite app_nil_r; exact HN).
  pose proof (fbinA_FBx FB Ai rho tv [] HB HNx) as FBX. pose proof (ffinA_FFx FF Ai rho fr HFF HFR) as FFX.

  pose proof (smatchA_agree segs rho rho' tp A _ Hag Hsm) as Hsm'.
  pose proof Hwf as Hwf0. unfold pop_stateA, ax_with_facts, with_facts in Hwf0.
  cbn [ax_S ax_setX ax_setS ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in Hwf0. fold n in Hwf0.
  apply swf_facts_suffix in Hwf0.
  assert (Hwf1 : swf (mkSS (ss_pc (ax_S A)) (ss_regs (ax_S A)) (ss_fregs (ax_S A)) (ss_fcsr (ax_S A)) (ss_resv (ax_S A))
                           (ss_objs (ax_S A) ++ [carved hd 0 24 (hdr_cells n)]) (ss_facts (ax_S A)) (n + 4) (ss_lenient (ax_S A))) = true).
  { revert Hwf0. unfold swf. cbn [ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts]. rewrite !forallb_app. cbn [forallb].
    intros H. apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [H1 H3]. apply andb_prop in H3 as [H3 H4]. apply andb_prop in H4 as [H4 H5].
    rewrite H1, H3, H4, H2. reflexivity. }
  set (A1 := ax_setS A (mkSS (ss_pc (ax_S A)) (ss_regs (ax_S A)) (ss_fregs (ax_S A)) (ss_fcsr (ax_S A)) (ss_resv (ax_S A))
                           (ss_objs (ax_S A) ++ [carved hd 0 24 (hdr_cells n)]) (ss_facts (ax_S A)) (n + 4) (ss_lenient (ax_S A)))).
  assert (SP1 : SPA segs (TobjJA.JAi AInv CST XGL NP Kc rho0 P0f FB FF BX PA (NDA tv fr bd (AHeadN hd g)) Ai kc) A1 rho' tp (tr, mkCfg ms md)).
  { subst A1. apply (SPA_carve_obj segs _ rho' A tp (tr, mkCfg ms md) hd 0 24 (hdr_cells n) (n + 4)).
    - split; [exact Hsm'|]. eapply (JAi_stable segs AInv CST XGL NP Kc rho0 P0f FB FF BX PA HKc ALA n); [lia | exact Hnb | exact Hag | apply mat_equiv_refl | exact HJ].
    - exact Hwf1.
    - lia.
    - lia. - lia. - lia. - lia.
    - rewrite Uhd. lia.
    - rewrite Uhd. lia.
    - unfold hdr_cells, cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - apply Forall_forall. intros o Ho. rewrite Uhd.
      rewrite (obj_range_agree_vals n rho rho' o Hagv (proj1 (forallb_forall _ _) (swf_objs _ (smatch_swf segs _ _ _ (proj1 Hsm))) o Ho)).
      destruct (obj_range rho o) as [lo hi] eqn:Eo. apply ranges_disjoint_by_points. intros a Ha1 Ha2.
      apply (DISJ a ltac:(unfold HDR; lia) o Ho). rewrite Eo. cbn [fst snd]. exact Ha1.
    - intros off Hoff. rewrite Hrm, Uhd. unfold wok_of, rd_of.
      destruct (rm rho (Z_to_bv 64 (h + off))) as [x|] eqn:Ex; [split; [reflexivity | exists x; reflexivity]|].
      exfalso. apply (Hdef (h + off)); [unfold HDR; lia | exact Ex].
    - unfold hdr_cells, cells_in_view. rewrite Hrm, Uhd.
      repeat constructor; intros j Hj; cbn [eval]; rewrite ?R0, ?R1, ?R2; unfold rd_of.
      + rewrite Z.add_0_r. rewrite (rd64_enc_bytes (rm rho) h nx Hrd0 j Hj). reflexivity.
      + rewrite (rd64_enc_bytes (rm rho) (h + 8) cap Hrd8 j Hj). reflexivity.
      + rewrite (rd64_enc_bytes (rm rho) (h + 16) u Hrd16 j Hj). reflexivity.
    - intros rr y j Hr Hy Hj Hin. rewrite Hbase in Hin. cbn [eval] in Hin. rewrite lit_unsigned in Hin. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF in Hin.
      rewrite Uhd in Hin.
      pose proof Hsm' as (_ & _ & HwfA & _). unfold axwf in HwfA. apply andb_prop in HwfA as [HXb _].
      pose proof (proj1 (forallb_forall _ _) HXb rr Hr) as Yb. unfold xr_below in Yb. apply andb_prop in Yb as [Yb1 Yb2].
      rewrite <- (eval_agree n rho rho' _ Hag Yb1), <- (eval_agree n rho rho' _ Hag Yb2) in Hy.
      pose proof (HX47 rr y Hr ltac:(unfold uval; exact Hy)) as Hy47.
      pose proof (word_byte_of_shadow (Sh y) j (Sh_is_shadow y Hy47) Hj) as WS.
      destruct (word_byte_range (Sh y) j ltac:(pose proof (Sh_is_shadow y Hy47) as SS; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS; lia) Hj) as (_ & EWB & _).
      rewrite EWB in WS. unfold Sh in WS. replace (y / 8 + SHADOW_OFF) with (SHADOW_OFF + y / 8) in WS by lia.
      unfold is_shadowZ, HIGH_SHADOW_END in WS, G5. unfold HDR in Hin. lia. }

  assert (E24 : bv_unsigned (eval rho' (SAlu ALU_ADD hd (SLit 24))) = h + 24).
  { rewrite U_add, Uhd, U_lit. unfold M64v. rewrite (Z.mod_small 24) by lia. apply Z.mod_small. lia. }
  assert (E8 : bv_unsigned (eval rho' (SAlu ALU_ADD (SVar (n + 1)) (SLit 8))) = cap + 8).
  { rewrite U_add, U_lit. cbn [eval]. rewrite Ucap. unfold M64v. rewrite (Z.mod_small 8) by lia. apply Z.mod_small. lia. }
  set (A2 := ax_setS A (mkSS (ss_pc (ax_S A)) (ss_regs (ax_S A)) (ss_fregs (ax_S A)) (ss_fcsr (ax_S A)) (ss_resv (ax_S A))
                           (ss_objs (ax_S A) ++ [carved hd 0 24 (hdr_cells n); tail_obj hd n]) (ss_facts (ax_S A)) (n + 4) (ss_lenient (ax_S A)))).
  assert (SP2 : SPA segs (TobjJA.JAi AInv CST XGL NP Kc rho0 P0f FB FF BX PA (NDA tv fr bd (AHeadN hd g)) Ai kc) A2 rho' tp (tr, mkCfg ms md)).
  { assert (EA2 : A2 = ax_setS A1 (mkSS (ss_pc (ax_S A1)) (ss_regs (ax_S A1)) (ss_fregs (ax_S A1)) (ss_fcsr (ax_S A1)) (ss_resv (ax_S A1))
                                           (ss_objs (ax_S A1) ++ [tail_obj hd n]) (ss_facts (ax_S A1)) (n + 4) (ss_lenient (ax_S A1)))).
    { subst A1 A2. cbn [ax_S ax_setS ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_lenient]. rewrite <- app_assoc. reflexivity. }
    rewrite EA2. unfold tail_obj. apply (SPA_carve_plain segs (TobjJA.JAi AInv CST XGL NP Kc rho0 P0f FB FF BX PA (NDA tv fr bd (AHeadN hd g)) Ai kc) rho' A1 tp (tr, mkCfg ms md) _ _ (n + 4) SP1).
    - subst A1. cbn [ax_S ax_setS ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_lenient]. rewrite <- app_assoc. cbn [app]. exact Hwf0.
    - subst A1. cbn [ax_S ax_setS ss_next]. lia.
    - rewrite E8. lia.
    - rewrite E24, E8. lia.
    - subst A1. cbn [ax_S ax_setS ss_objs]. rewrite E24, E8. apply Forall_app. split.
      + apply Forall_forall. intros o Ho.
        rewrite (obj_range_agree_vals n rho rho' o Hagv (proj1 (forallb_forall _ _) (swf_objs _ (smatch_swf segs _ _ _ (proj1 Hsm))) o Ho)).
        destruct (obj_range rho o) as [lo hi] eqn:Eo. apply ranges_disjoint_by_points. intros a Ha1 Ha2.
        apply (DISJ a ltac:(unfold HDR; lia) o Ho). rewrite Eo. cbn [fst snd]. exact Ha1.
      + apply Forall_cons; [|apply Forall_nil]. unfold obj_range, obj_lo_of, obj_hi_of, carved. cbn [ob_base ob_lo ob_hi fst snd].
        rewrite !soff_lit_small by lia. rewrite Uhd. unfold ranges_disjoint. cbn [fst snd]. lia.
    - intros z Hz. rewrite E24, E8 in Hz. rewrite Hrm. destruct (rm rho (Z_to_bv 64 z)) as [x|] eqn:Ex; [exists x; reflexivity|].
      exfalso. apply (Hdef z); [unfold HDR; lia | exact Ex].
    -
      subst A1. intros rr y j Hr Hy Hj Hin. cbn [ax_X ax_setS ax_base] in Hr, Hin, Hy. rewrite Hbase in Hin. rewrite E24, E8 in Hin.
      change (bv_unsigned (eval rho' (SLit SHADOW_OFF))) with (uval rho' (SLit SHADOW_OFF)) in Hin. rewrite uval_lit in Hin by (unfold SHADOW_OFF; lia).
      pose proof Hsm' as (_ & _ & HwfA & _). unfold axwf in HwfA. apply andb_prop in HwfA as [HXb _].
      pose proof (proj1 (forallb_forall _ _) HXb rr Hr) as Yb. unfold xr_below in Yb. apply andb_prop in Yb as [Yb1 Yb2].
      rewrite <- (eval_agree n rho rho' _ Hag Yb1), <- (eval_agree n rho rho' _ Hag Yb2) in Hy.
      pose proof (HX47 rr y Hr ltac:(unfold uval; exact Hy)) as Hy47.
      pose proof (word_byte_of_shadow (Sh y) j (Sh_is_shadow y Hy47) Hj) as WS.
      destruct (word_byte_range (Sh y) j ltac:(pose proof (Sh_is_shadow y Hy47) as SS; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS; lia) Hj) as (_ & EWB & _).
      rewrite EWB in WS. unfold Sh in WS. replace (y / 8 + SHADOW_OFF) with (SHADOW_OFF + y / 8) in WS by lia.
      unfold is_shadowZ, HIGH_SHADOW_END in WS, G5. unfold HDR in *. lia. }

  assert (XB : xr_below (ss_next (ax_S A2)) (hd, e32 (SVar (n + 1))) = true).
  { subst A2. unfold xr_below. cbn [fst snd ax_S ax_setS ss_next e32 sv_below]. rewrite (sv_below_mono n (n + 4) hd ltac:(lia) Hba). cbn [andb]. rewrite andb_true_r. apply Pos.ltb_lt. lia. }
  assert (XOK : xr_ok rho' (ss_objs (ax_S A2)) (bv_unsigned (eval rho' (ax_base A2))) (hd, e32 (SVar (n + 1)))).
  { subst A2. cbn [ax_base ax_setS ax_S ss_objs fst snd]. rewrite Hbase. cbn [eval]. rewrite lit_unsigned. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF.
      unfold xr_ok. cbn zeta. cbn [fst snd]. rewrite Uhd. unfold e32. rewrite U_add, U_lit. cbn [eval]. rewrite Ucap. unfold M64v. rewrite (Z.mod_small 32) by lia. rewrite (Z.mod_small (cap + 32)) by lia.
      destruct Hxm as [Xal Xm]. split; [exact Xal|]. split; [lia|].
      intros a Ha. assert (Ha47 : 0 <= a < 2 ^ 47) by (unfold HDR in Ha; lia). pose proof (Sh_is_shadow a Ha47) as HSa.
      destruct (Xm a ltac:(unfold HDR; lia)) as [XW (v & Xv1 & Xv2)].
      assert (OUTW : forall j, 0 <= j < 8 -> outside_all rho' (ss_objs (ax_S A) ++ [carved hd 0 24 (hdr_cells n); tail_obj hd n]) (word_byte (SHADOW_OFF + a / 8) j)).
      { intros j Hj. pose proof (word_byte_of_shadow (Sh a) j HSa Hj) as WS.
        replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia).
        apply outside_all_app_iff. split.
        - eapply (outside_all_exts n rho rho'); [reflexivity | exact (swf_objs _ (smatch_swf segs _ _ _ (proj1 Hsm))) | exact Hag |].
          unfold outside_all. apply Forall_forall. intros o Ho Hr.
          destruct (HROK o _ Ho Hr) as [Hc|Himg]; [|unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in WS; unfold IMG_HI in Himg; lia].
          pose proof (law_client_app _ _ _ ALA Ai rho tp md _ HM (pclFA_client CST _ _ _ Ai _ FBX FFX HT (pclMA_pclFA _ _ _ _ _ Hc))) as APP.
          unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in APP. top_rng APP. unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in WS. lia.
        - unfold outside_all. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn zeta.
          + unfold obj_range, obj_lo_of, obj_hi_of, carved. cbn [ob_base ob_lo ob_hi fst snd].
            rewrite !soff_lit_small by lia. rewrite Uhd. unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in WS. unfold HIGH_SHADOW_END in G5. unfold HDR in *. lia.
          + unfold obj_range, obj_lo_of, obj_hi_of, tail_obj, plain_obj. cbn [ob_base ob_lo ob_hi fst snd].
            rewrite soff_lit_small by lia. rewrite (soff_smallu rho') by (unfold uval; rewrite E8; lia). unfold uval. rewrite E8, E24.
            unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in WS. unfold HIGH_SHADOW_END in G5. unfold HDR in *. lia. }
      split; [pose proof HSa as SS; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END, Sh in SS; lia|].
      split; [rewrite shadow_addr_word_byte; apply OUTW; apply Z.mod_pos_bound; lia|].
      split; [intros j Hj; split; [apply OUTW; exact Hj | rewrite Hrm; exact (XW j Hj)]|].
      exists v. rewrite Hrm. split; [exact Xv1 |]. unfold HDR in Xv2. replace (h + (cap + 32)) with (h + (32 + cap)) by lia. exact Xv2. }
  pose proof (SPA_x_publish segs _ rho' A2 _ tp _ XB XOK SP2) as SP3.

  assert (FB' : forallb (sprop_below (ss_next (ax_S (ax_setX A2 ((hd, e32 (SVar (n + 1))) :: ax_X A2)))))
                        ((open_factsA hd n ++ ghost_factsA (n + 3) ++ [link_factA g (n + 3)]) ++ ss_facts (ax_S A)) = true).
  { subst A2. cbn [ax_S ax_setX ax_setS ss_next]. rewrite forallb_app. apply andb_true_intro. split.
      * unfold pop_stateA, ax_with_facts, with_facts in Hwf.
        cbn [ax_S ax_setX ax_setS ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in Hwf. fold n in Hwf.
        pose proof (swf_facts _ Hwf) as WFF. cbn [ss_facts ss_next] in WFF. rewrite forallb_app in WFF. apply andb_prop in WFF as [W1 _]. exact W1.
      * apply forallb_forall. intros q Hq. eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) (swf_facts _ (smatch_swf segs _ _ _ (proj1 Hsm))) q Hq)]. lia. }
  assert (FH : Forall (holds rho') (ss_facts (ax_S (ax_setX A2 ((hd, e32 (SVar (n + 1))) :: ax_X A2)))) ->
               Forall (holds rho') ((open_factsA hd n ++ ghost_factsA (n + 3) ++ [link_factA g (n + 3)]) ++ ss_facts (ax_S A))).
  { subst A2. cbn [ax_S ax_setX ax_setS ss_facts]. intros HF'. apply Forall_app. split; [|exact HF'].
      apply Forall_app. split; [|apply Forall_app; split].
      * unfold open_factsA. apply Forall_app. split.
        -- unfold e32.
           assert (E1 : bv_unsigned (eval rho' (SAlu ALU_ADD (SVar (n + 1)) (SLit 32))) = cap + 32).
           { rewrite U_add, U_lit. cbn [eval]. rewrite Ucap. unfold M64v. rewrite (Z.mod_small 32) by lia. apply Z.mod_small. lia. }
           assert (E2 : bv_unsigned (eval rho' (SAlu ALU_ADD hd (SAlu ALU_ADD (SVar (n + 1)) (SLit 32)))) = h + (cap + 32)).
           { rewrite U_add, E1, Uhd. unfold M64v. apply Z.mod_small. lia. }
           assert (ET : bv_unsigned (rw rho' V_TOP) = topG (aa_geom Ai)).
           { rewrite <- (proj1 Hag V_TOP ltac:(unfold NP_okA in HNP; lia)). exact (proj1 (T_ok_of_TPA NP rho0 HNP rho Ai Hav HT)). }
           repeat apply Forall_cons; try apply Forall_nil; cbn [holds]; rewrite ?E2, ?E1, ?U_lit, ?Uhd; cbn [eval]; rewrite ?Ucap, ?Uu, ?ET; unfold M64v;
             rewrite ?Z.mod_small by lia; lia.
        -- destruct hd as [v0| | | | | | |]; try apply Forall_nil. apply Forall_cons; [|apply Forall_nil]. cbn [holds]. cbn [eval] in Uhd. rewrite Uhd.
           change (2 ^ 4) with 16. split; [lia | exact G2].
      * unfold ghost_factsA, two52. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [holds]; rewrite U_lit; cbn [eval]; rewrite Ug'; unfold M64v; rewrite Z.mod_small by lia; lia.
      * apply Forall_cons; [|apply Forall_nil]. unfold link_factA. cbn [holds]. rewrite U_add, U_lit. cbn [eval]. rewrite Ug', Eg. fold G. unfold M64v.
        rewrite (Z.mod_small 16) by lia. unfold G. pose proof (uval_range rho g). unfold uval in *. rewrite Z.mod_small by lia. lia. }
  pose proof (SPA_refacts segs _ rho' _ ((open_factsA hd n ++ ghost_factsA (n + 3) ++ [link_factA g (n + 3)]) ++ ss_facts (ax_S A)) tp (tr, mkCfg ms md) SP3 FB' FH) as SP4.
  split.
  2: { rewrite Ug'. unfold G, uval. lia. }
  subst A2. unfold pop_stateA. fold n. split; [exact (proj1 SP4)|].

  exists Ai, (kc - KU).
  assert (HJ' : JAi (NDA tv fr bd (AHeadN hd g)) Ai kc rho' tp tr md).
  { eapply (JAi_stable segs AInv CST XGL NP Kc rho0 P0f FB FF BX PA HKc ALA n); [lia | exact Hnb | exact Hag | apply mat_equiv_refl | exact HJ]. }
  pose proof HJ' as (Hav' & _ & HM' & HT' & _ & _ & (HN' & HD' & HZ') & HFR' & HK0' & _ & HXA' & HBU' & HPA').
  cbn [nd_tv nd_fr nd_bd nd_am] in HN', HD', HZ', HFR', HXA', HBU'.
  assert (TVV : tvv rho' (hd, e32 (SVar (n + 1))) = (h, HDR + cap)).
  { unfold tvv, e32. cbn [fst snd]. rewrite Uhd, U_add, U_lit. cbn [eval]. rewrite Ucap. unfold M64v, HDR. rewrite (Z.mod_small 32) by lia. rewrite Z.mod_small by lia. f_equal. lia. }
  assert (TNZ : tnz rho' (hd, e32 (SVar (n + 1)))) by (unfold tnz; cbn [fst]; rewrite Uhd; exact Hh).
  split; [exact Hav'|]. split; [exact Hk|]. split; [exact HM'|]. split; [exact HT'|]. split; [exact HB|]. split; [exact HFF|].
  split.
  {
    split; [|split].
    - unfold tvinA in HN' |- *. apply Forall_cons; [|exact HN']. intros _. rewrite TVV. cbn [snd]. split; [unfold HDR; lia|]. split; [exact Hlive | exact Hnfb].
    - cbn [tvd]. split; [|exact HD']. intros t' Ht' _ Hnz' Heq. rewrite TVV in Heq.
      unfold untracked in Hut. rewrite <- (tvals_agree n rho rho' tv Hagv Hbt) in Hut.
      apply (Hut (tvv rho' t')); [unfold tvals; apply in_map; exact Ht' | unfold tnz in Hnz'; unfold tvv; cbn [fst]; exact Hnz' | symmetry; exact Heq].
    - unfold tvz in HZ' |- *. apply Forall_cons; [|exact HZ']. intros Hz. exfalso. exact (Hz TNZ). }
  split; [exact HFR'|]. split; [exact HK0'|]. split; [exact HP0|].
  cbn [nd_tv nd_fr nd_bd nd_am].

  assert (HCNT : cntS rho' tv <= cntS rho' ((hd, e32 (SVar (n + 1))) :: tv)) by (rewrite cntS_cons; destruct (is_smallZ _); lia).
  refine (conj _ (conj _ (JA_tail_le _ _ _ rho' rho' tv _ HCNT HPA'))).
  +
    unfold XA. split.
    2: {
         intros bn L1 L2 L3 L4. cbn [am_eval amblkZ]. unfold uval. cbn [eval]. rewrite Unx.
         unfold tvals in L4. cbn [map] in L4. rewrite TVV in L4.
         assert (L4' : untrackedZ (tvals rho tv) bn).
         { intros v Hv Hvz. apply L4; [|exact Hvz]. right. rewrite <- (tvals_agree n rho rho' tv Hagv Hbt) in Hv. exact Hv. }
         pose proof (HCEN bn L1 L2 L3 L4') as HAM. cbn [amblkZ] in HAM. destruct HAM as (ns' & HA' & Hin').
         rewrite (achain_det _ _ _ _ HA0 HA') in Hin'. cbn [map] in Hin'. destruct Hin' as [E|Hin'].
         - exfalso. apply (L4 (h, HDR + cap)); [left; reflexivity | cbn [fst]; exact Hh | exact E].
         - exists r. split; [rewrite Hrm; exact HAr | exact Hin']. }
    cbn -[chainZ KU uval HDR untrackedZ tvals]. unfold uval. cbn [eval]. rewrite Unx, Ug'.
    exists r. split; [|split; [unfold KU in *; lia | lia]].
    split; [rewrite Hrm; exact HAr|]. split; [|inversion HND; assumption].
    apply Forall_forall. intros bc Hbc. destruct (proj1 (Forall_forall _ _) HNr bc Hbc) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6).
    split; [exact Y1|]. split; [exact Y2|]. split.
    { unfold tvals. cbn [map]. rewrite TVV. intros v [<-|Hv] Hvz.
      - intros Heq. injection Heq as E1 E2. inversion HND; subst. apply H1. rewrite E1. apply list_elem_of_In. apply in_map_iff. exists bc. split; [reflexivity | exact Hbc].
      - intros Heq. rewrite <- (tvals_agree n rho rho' tv Hagv Hbt) in Y3. exact (Y3 v Hv Hvz Heq). }
    split; [exact Y4|]. split; [exact Y5|]. rewrite Hrm. exact Y6.
  +
    unfold apot in HBU' |- *. cbn [am_eval apotz] in HBU' |- *. unfold bxa in HBU' |- *. cbn [fst snd] in HBU' |- *.
    apply (BUD_bx_ext (bd ++ [BIc 0 1 KU]) (fst (bx2 BX) + 0, snd (bx2 BX) + 0 + (kc - KU))); [cbn; lia | cbn; lia |].
    apply (BUD_kc_item bd (fst (bx2 BX) + 0) (snd (bx2 BX) + 0) kc); [exact HBU' | unfold KU in *; nia | lia].
Qed.

Lemma JA_headN_none : ltac2:(tb__ "0|0|
S1eS1fS2S2A2A1S1eS1fS1fS2S0A2S2A2A1S1eS28A1S2S2S30S3S1eS45Q40A1A1S4cS2cS21S54S4SfScS53R6S5Z0A1A3A1S8S2fR4A1A1A3S22A3S34Vsegs;VJA;S36RaR9R8S37R7R6A2A4A1R5R4R3R2A6S34Vsegs;VJA;S36RbRaR9S39A4A1R6R5R4R3A6F_;F_;Fw;Ftp;Frho;FA;Fg;Fhd;Fbd;Ffr;Ftv;").
Proof using HBX.
  pose proof (BXok_d_pair _ BX HBX) as [HBX1 HBX2].
  intros tv fr bd hd g A rho tp w Hz [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, 0.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HNDZ & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HNDZ, HFR, HXA, HBU |- *.
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  assert (Hh : uval rho hd = 0).
  { pose proof (holds_mem _ _ _ HF Hz) as F0. apply (proj1 (holds_beq _ _ _)) in F0. change (bv_unsigned (eval rho hd)) with (uval rho hd) in F0.
    rewrite U_lit in F0. change (0 mod M64v) with 0 in F0. exact F0. }
  unfold XA in HXA. cbn [nd_am nd_tv am_eval] in HXA. rewrite Hh in HXA. destruct HXA as [HXA HCEN]. cbn -[chainZ KU] in HXA. destruct HXA as (ns & [HA _] & Hkc & _).
  pose proof (achain_nil _ _ HA) as ->. cbn [length Z.of_nat] in Hkc. rewrite Z.mul_0_r in Hkc. subst kc.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HNDZ|]. split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split.
  { unfold XA. cbn [nd_am nd_tv am_eval]. split; [reflexivity|].
    apply (lcenZ_mode FB (AHNz 0 (uval rho g))); [|exact HCEN]. intros bn (ns' & HA' & Hin'). pose proof (achain_nil _ _ HA') as ->. destruct Hin'. }
  split; [|exact (conj HPA (conj HCKi HCNi))].
  cbn [nd_bd nd_am]. unfold apot in HBU |- *. cbn [am_eval apotz] in HBU |- *. exact HBU.
Qed.

Lemma JA_dropN : ltac2:(tb__ "0|0|
S1eS1fS2S2A2A1S1eS1fS1fS2S0A2S2A2A1S1eS28A1S2S2S30S3S1eS45Q40A1A1S4cS34Vsegs;VJA;S36R9R8R7S37R6R5A2A4A1R4R3R2R1A6S34Vsegs;VJA;S36RaR9R8S38R7S27A2A4A1R5R4R3R2A6F_;Fw;Ftp;Frho;FA;Fg;Fhd;Fbd;Ffr;Ftv;").
Proof using .
  intros tv fr bd hd g A rho tp w [Hsm (Ai & kc & HJ)]. split; [exact Hsm|]. exists Ai, kc.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & HNDZ & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  cbn [nd_tv nd_fr nd_bd nd_am] in HNDZ, HFR, HXA, HBU |- *.
  split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [exact HNDZ|]. split; [exact HFR|]. split; [exact HK0|]. split; [exact HP0|]. split; [|split; [|exact (conj HPA (conj HCKi HCNi))]].
  - unfold XA in HXA |- *. cbn [nd_am nd_tv am_eval] in HXA |- *. destruct HXA as [HXA HCEN]. split; [|exact HCEN].
    cbn -[chainZ KU] in HXA |- *. destruct HXA as (ns & HC & Hkc & _). exists ns. auto.
  - cbn [nd_bd nd_am]. unfold apot in HBU |- *. cbn [am_eval apotz] in HBU |- *. exact HBU.
Qed.
End D.
End WithSegs.
