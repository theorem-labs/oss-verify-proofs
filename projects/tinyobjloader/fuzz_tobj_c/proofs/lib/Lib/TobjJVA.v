(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "valuation"; "ss_next"; "sobj"; "ss_facts"; "sprop"; "sv_eqb"; "SLit"; "SVar"; "rm"; "eval"; "holds"; "sv_below"; "obj_range"; "smatch"; "ss_objs"; "agree_below"; "swf"; "ob_base"; "mkSS"; "ob_hi"; "ob_lo"; "ss_lenient"; "SPUle"; "cell"; "sprop_eqb"; "SAlu"; "SPBranch"; "SPNot"; "dflt_writable"; "ob_dflt"; "ss_fcsr"; "ss_fregs"; "ss_pc"; "ss_regs"; "ss_resv"; "ob_cells"; "rw"; "sprop_below"; "mkCell"; "ranges_disjoint"; "DUnknown"; "SPAlign"; "c_off"; "c_val"; "c_width"; "mkObj"; "obj_holds"; "rd"; "sfcsr"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "iff"; "False"; "True"; "@Corelib.Init.Datatypes"; "bool"; "prod"; "true"; "list"; "pair"; "option"; "fst"; "cons"; "Some"; "app"; "snd"; "false"; "andb"; "nil"; "nat"; "None"; "negb"; "orb"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "amode"; "am_below"; "am_subst"; "AOpen"; "AHead"; "am_eqb"; "ANone"; "pl_eqb"; "AHeadN"; "NP_ok"; "pl_below"; "pl_subst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "ok_frame"; "LQ"; "SP"; "LQJ"; "ok_frameJ"; "stableJ"; "@Stdlib.Lists.List"; "In"; "nth_error"; "forallb"; "existsb"; "flat_map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA.WithSegs.Sum"; "JGA"; "aedesc"; "XA"; "andesc"; "hdr_obj"; "adrop"; "ad_state"; "drop_last_state"; "nodeA"; "JGAi"; "echeckA"; "enodeA"; "nodes_ok"; "ad_rank"; "ameas"; "has_cell8"; "untracked"; "ad_var"; "eecheckA"; "jcertA"; "am_svs"; "carve_state"; "ejcertA"; "hdr_shape"; "open_state"; "plain_obj"; "ad_am"; "ad_tv"; "hdr_cells"; "hdr_open"; "open_facts"; "slot_obj"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "agree_vals"; "jpost"; "LQP"; "pos_add_nat"; "import_sub"; "import_post"; "call_check"; "wsub_dom_below"; "J_ofP"; "call_checkP"; "call_linkP"; "import_okP"; "call_link"; "new_objs"; "sv_vars_all"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "eqb"; "mul"; "leb"; "ltb"; "modulo"; "of_nat"; "opp"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "world"; "triple"; "etriple"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "ma_blocks"; "ma_L"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "rho_sub"; "rho_absorb"; "sv_subst"; "wsub_id_below"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "tv_below"; "tnz"; "tvv"; "T_after"; "fbin"; "call_checkT"; "tvin"; "T_ok"; "pclF"; "tvd"; "tvz"; "FBx"; "TPI"; "robjs_check"; "remove_nth"; "robjs_ok"; "tv_sub_eqb"; "malloc_contracts"; "malloc_contracts_ex"; "JG_pre"; "caddr"; "robjs_okF"; "PostsC"; "T_afterN"; "import_tv"; "inited"; "keptF"; "tvL_ok"; "T0"; "JG"; "JGi"; "JLG"; "ivar_ok"; "patchf"; "rho_patch"; "tv_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Contract"; "MInvR";
"L_malloc_null"; "L_malloc_ok"; "Pre_malloc"; "V_RES"; "ok_sideK"; "vm_insensitive"; "L_free"; "Pre_free"; "JL_free"; "J_alloc_pre"; "J_free_pre"; "Posts_malloc"; "V_TOP"; "mem_kept"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "add"; "le"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "entails"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "uleq"; "lf_state"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "wview"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "topL"; "mc_img_hi"; "mc_img_lo"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "edge"; "enodeJ"; "jnode"; "SPfamEJ"; "SPfamGJ"; "add_facts"; "cfg_edges"; "e_src"; "e_sub"; "e_tgt"; "edge_okJ"; "e_leaf"; "eedge_okJ"; "enj_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA.WithSegs"; "JGA"; "XA"; "JGA_pre"; "PostsCA"; "am_svs"; "JLGA"; "hdr_obj"; "untracked"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena"; "HDR"; "achain"; "rd64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "BC_EQ"; "aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA.WithSegs.PostsA"; "JLGA"; "JGA_pre"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA.WithSegs.ClientA"; "PostsCA"; "amL_ok"; "new_objs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA.WithSegs.FrameA"; "PDAh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "in_rng"; "@stdpp.base"; "NoDup"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymFrame SymEntail SymCFG SymSummary SymCall ExampleMemcpy Glue3 SymBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue ObjXform TobjJV TobjArena.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Inductive amode : Type :=
| ANone
| AHead (hd : sv)
| AOpen (hd nx cap : sv) (slots : list (sv * sv))
| AHeadN (hd g : sv).

Definition pl_below (n : positive) (l : list (sv * sv)) : bool := ltac2:(tb__ "0|1|
S67S3fS0S0A2M0G0S4aSdVn;S44S0S0R1A3A2SdVn;S48S0S0R1A3A2A2Lt;Vl;A3").
Definition pl_subst (s : wsub) (l : list (sv * sv)) : list (sv * sv) := ltac2:(tb__ "0|1|
S8cS3fS0S0A2M0G0G0S42S0S0Sb3Vs;S44S0S0R1A3A2Sb3Vs;S48S0S0R1A3A2A4Lt;Vl;A4").
Fixpoint pl_eqb (l l' : list (sv * sv)) : bool :=
  match l, l' with
  | [], [] => true
  | t :: r, t' :: r' => sv_eqb (fst t) (fst t') && sv_eqb (snd t) (snd t') && pl_eqb r r'
  | _, _ => false
  end.
Lemma pl_eqb_sound : ltac2:(tb__ "0|1|
S41S3fS0S0A2A1M0G0S36S3eS58R2R1A2S40A3S36G0R3R2A3F_;Fl';Fl;").
Proof.
  induction l as [|[a b] r IH]; intros [|[a' b'] r'] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. cbn in H1, H2. rewrite H1, H2, (IH r' H3). reflexivity.
Qed.

Definition am_below (n : positive) (am : amode) : bool := ltac2:(tb__ "0|2|
S51S3eLam;Vam;S40S0SdVn;R1A2M0Lhd;S0S0S0S41S3fS0S0A2A1S4aS4aS4aSdVn;R4A2SdVn;R3A2A2SdVn;R2A2M1A2S5bVn;R1A2A2Lsl;Lcap;Lnx;Lhd;S0S0S4aG1G0A2Lg;Lhd;X51x4").
Definition am_subst (s : wsub) (am : amode) : amode := ltac2:(tb__ "0|2|
S51S51Lam;Vam;S57S0S55Sb3Vs;R1A2M0A1Lhd;S0S0S0S41S3fS0S0A2A1S54Sb3Vs;R4A2Sb3Vs;R3A2Sb3Vs;R2A2M1S5cVs;R1A2A4Lsl;Lcap;Lnx;Lhd;S0S0S59G1G0A2Lg;Lhd;X51x4").
Definition am_eqb (a b : amode) : bool := ltac2:(tb__ "0|5|
S51S3eLa;Va;S51S3eLb;M0Vb;S40S0S49Lhd;M1S0S0S0S41S3fS0S0A2A1M2S49Lslots;Lcap;Lnx;Lhd;M3S0S0S49Lg;Lhd;M4X51x4S0G0Vb;S49S0S7R2R1A2Lh';G3G4X51x4Lh;S0S0S0G2G0Vb;S49G1S0S0S0G2S4aS4aS4aS7R8R4A2S7R7R3A2A2S7R6R2A2A2S58R5R1A2A2Lsl';Lc';Ln';Lh';G4X51x4Lsl;Lc;Ln;Lh;S0S0G0Vb;S49G1G3S0S0S4aS7R4R2A2S7R3R1A2A2Lg';Lh';X51x4Lg;Lh;X51x4").

Lemma am_eqb_sound : ltac2:(tb__ "0|0|
S51S51S36S3eS56R2R1A2S40A3S36S51R3R2A3F_;Fb;Fa;").
Proof.
  intros [|h|h n c sl|h g] [|h'|h' n' c' sl'|h' g'] H; cbn -[pl_eqb] in H; try discriminate; try reflexivity.
  - apply sv_eqb_sound in H. congruence.
  - apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3. apply pl_eqb_sound in H4. congruence.
  - apply andb_prop in H as [H1 H2]. apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. congruence.
Qed.

Definition NP_ok (NP : positive) : Prop := (V_TOP < NP)%positive.
Lemma NP_ok_intro : ltac2:(tb__ "0|0|
S34S36S3eSeeSe9R1A2S40A3S5aR2A1F_;FNP;").
Proof. intros NP H. apply Pos.ltb_lt. exact H. Qed.

Section WithSegs.
Variable segs : list Segment.
Variable C : mconsts.
Variable E : entry_consts.

Section Sum.
Variable NP : positive.
Variable Kc : ltac2:(tb__ "0|0|
S41S6bA1S6aOF_;F_;").
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Hypothesis ML : malloc_laws segs C.

Hypothesis HNP : NP_ok NP.

Let Uv (rho : valuation) (e : sv) : Z := bv_unsigned (eval rho e).

Lemma T_ok_of_TPI : ltac2:(tb__ "0|0|
S2SacS8eVNP;Vrho0;R2A3Sc4VC;Vrho0;R2A3SbfR4Sf7SaeR3A1A1A2F_;F_;FAi;Frho;").
Proof using HNP. intros rho Ai Hav HT. exact (T_of_TPI C NP rho0 rho Ai Hav HNP HT). Qed.
Lemma T_ok_T0 : ltac2:(tb__ "0|0|
S2SacS8eVNP;Vrho0;R2A3Sc4VC;Vrho0;R2A3SbfR4Sd4Vrho0;A1A2F_;F_;FAi;Frho;").
Proof using HNP. intros rho Ai Hav HT. rewrite <- (TPI_top _ _ _ HT). exact (T_ok_of_TPI rho Ai Hav HT). Qed.
Lemma T_ok_T0_of : ltac2:(tb__ "0|0|
S2S33S8eVNP;Vrho0;R2A3SbfR3R2A2SbfR4Sd4Vrho0;A1A2F_;F_;FT;Frho;").
Proof using HNP.
  intros rho T [Hw _] [ET RT]. unfold T_ok, T0 in *. rewrite (Hw V_TOP HNP). split; [reflexivity|]. rewrite ET. exact RT.
Qed.

Lemma pclF_caddrT : ltac2:(tb__ "0|0|
S2SacS33S8eVNP;Vrho0;R3A3SbfR4Sf7SaeR3A1A1A2SbcVFB;R4A2Sc0Vsegs;VC;Vrho0;VFB;R4A5SccVsegs;VC;R6S4dS33A1R5A5F_;F_;F_;F_;Fa;FAi;Frho;").
Proof using HNP.
  intros rho Ai a [Hw _] [HT _] HP Hp.
  destruct Hp as [H|[H|(b & n & Hin & Hr)]]; [left | right; left; exact H | right; right].
  - unfold T0 in H. rewrite (Hw V_TOP HNP), HT in H. exact H.
  - exists b, n. split; [exact (HP _ Hin)|]. split; [discriminate | exact Hr].
Qed.

Definition nodes_ok (Ai : MA) (rho : valuation) (tv : list (sv * sv)) (ns : list (Z * Z)) : Prop := ltac2:(tb__ "0|3|
S37S8dS3fS33S33A2M0G0S37S65G0S42S33S33S44S33S33R1A3S9eS113S48S33S33R1A3A2A4M1SadVAi;A1A3S37S39S65G0G1VFB;A3A1S3fS0S0A2M2S65G2R1Vtv;A3Sb9Vrho;R2A2S39S36G0SbaVrho;R3A2S42S33S33S44S33S33R4A3S9eS113S48S33S33R4A3A2A4A3A1F_;F_;Ft;A2A2Lbc;Vns;A3S124S33S8cG0S33S44S33S33A2Vns;A4A2A2").

Definition XA (am : amode) (Ai : MA) (rho : valuation) (tv : list (sv * sv)) : Prop := ltac2:(tb__ "0|d|
S51OLam;Vam;S3dS0S38S41S3fS33S33A2M0A1M1G1S37S114SaVrho;A1M2VUv;Vrho;R2A2M3R1A3S78VAi;Vrho;Vtv;R1A4M4A2Lns;A2Lhd;S0S0S0S41S3fS0S0A2M5A1VUv;Vrho;R4A2S33VUv;Vrho;R3A2M6S33S37S39S36S33R2Z0M7A3A1S37S9dG7R1A2S37S65G0S42S33S33R2S9eS113R1A2A4M8SadVAi;A1A3S37S39S65G0G8VFB;A3A1S37G5S65G5R1Vtv;A3Sb9Vrho;R2A2S39S36G0SbaVrho;R3A2S42S33S33R5S9eS113R4A2A4A3A1F_;F_;Ft;S37S33S37S9dS9eR3Z18A2M9R1A2S9fR1S9eS9eR3S113A2R2A2MaA2A2S39S36S43Sb5Q8A1MbA1SaVrho;Sb7Q40R2A2A2S4dGbA1A3A1F_;Fz;S37S8dG5G5S37S9dG9VUv;Vrho;S44S0S0R1A3A2McA2S9dS9eGcVUv;Vrho;S48S0S0R1A3A2A2GaA2A2Lps;R3A3S38G1G1S37S114G2VUv;Vrho;R6A2R1A3S37G4S39S65S33R3S8cG0S33S44S33S33A2R1A4A3A1A2A2Lns;A2A2A2A2A2A2A2A2Tc;Th;Lsl;Lcap;Lnx;Lhd;S0S0S38G1G1S37S114G2G6R1A3S37G4S37S9dS9eSa2Z10Sa6S50G0R1A2A1A2ZfA2G3A2S9dG3Sa0Z2Z34A2A2A2A2A2Lns;A2Lg;Lhd;X51x4").

Definition JGAi (tv : list (sv * sv)) (am : amode) (Ai : MA) : jpred := ltac2:(tb__ "0|0|
S2S41S6bA1S6aS37Sd6Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;Vtv;VAi;R3R2R1AcS6eVam;VAi;R3Vtv;A4A2Lmd;Ltr;Lrho;").
Definition JGA (tv : list (sv * sv)) (am : amode) : jpred := ltac2:(tb__ "0|0|
S2S41S6bA1S6aS38SacSacS75Vtv;Vam;R1R4R3R2A6LAi;A2Lmd;Ltr;Lrho;").

Ltac clear_sec := try clear ML; try clear HNP; try clear FB; try clear P0f; try clear rho0; try clear Kc; try clear NP.

Lemma nodes_ok_agree : ltac2:(tb__ "0|0|
SacS34S2S2S41S3fS0S0A2A1S41S3fS33S33A2A1S8eR5R4R3A3S36S3eSb8R6R3A2S40A3S78R8R6R4R3A4S78R9R6R5R4A4F_;F_;F_;Fns;Ftv;Frho';Frho;Fn;FAi;").
Proof using .
  clear_sec. intros Ai n rho rho' tv ns Hag Hb [HF HD]. split; [|exact HD].
  apply Forall_forall. intros bc Hin. destruct (proj1 (Forall_forall _ _) HF bc Hin) as (H1 & H2 & H3).
  split; [exact H1|]. split; [exact H2|]. intros t Ht Hnz.
  pose proof (proj1 (forallb_forall _ _) Hb t Ht) as Hbt.
  rewrite (tvv_agree n rho rho' t Hag Hbt). apply H3; [exact Ht|].
  apply (proj1 (tnz_agree n rho rho' t Hag Hbt)). exact Hnz.
Qed.

Lemma XA_agree : ltac2:(tb__ "0|0|
S51SacS34S2S2S41S3fS0S0A2A1S8eR4R3R2A3Sb5Q40A1S36S43Sb5Q8A1A1SaR4R1A2SaR5R1A2A3Fa;S36S3eS52R6R8A2S40A3S36S3eSb8R7R4A2S40A3S6eRaR9R7R5A4S6eRbRaR7R6A4F_;F_;F_;F_;F_;Ftv;Frho';Frho;Fn;FAi;Fam;").
Proof using .
  intros am Ai n rho rho' tv Hag Hrm Hamb Hb HX. destruct am as [|hd|hd nx cap sl|hd g]; cbn -[pl_below] in HX |- *.
  - exact I.
  - destruct HX as (ns & HA & HN). exists ns. unfold Uv in *.
    rewrite <- (eval_agree_vals n rho rho' hd Hag Hamb).
    split; [|exact (nodes_ok_agree Ai n rho rho' tv ns Hag Hb HN)].
    eapply achain_frame; [exact HA | intros z _; apply Hrm | intros z _ Hz; rewrite Hrm; exact Hz].
  - cbn -[pl_below] in Hamb. apply andb_prop in Hamb as [Hamb Hsl]. apply andb_prop in Hamb as [Hamb Hc]. apply andb_prop in Hamb as [Hh Hn].
    unfold Uv in *.
    rewrite <- (eval_agree_vals n rho rho' hd Hag Hh), <- (eval_agree_vals n rho rho' nx Hag Hn), <- (eval_agree_vals n rho rho' cap Hag Hc).
    destruct HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & ns & HA & HN & Hnin).
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split.
    + intros t Ht Hnz. pose proof (proj1 (forallb_forall _ _) Hb t Ht) as Hbt.
      rewrite (tvv_agree n rho rho' t Hag Hbt). apply X5; [exact Ht|]. apply (proj1 (tnz_agree n rho rho' t Hag Hbt)). exact Hnz.
    + split; [intros z Hz; rewrite Hrm; exact (X6 z Hz)|]. split.
      * apply Forall_forall. intros ps Hps. pose proof (proj1 (Forall_forall _ _) X7 ps Hps) as Y. cbv beta in Y.
        pose proof (proj1 (forallb_forall _ _) Hsl ps Hps) as Hbp. apply andb_prop in Hbp as [Hb1 Hb2].
        rewrite <- (eval_agree_vals n rho rho' (fst ps) Hag Hb1), <- (eval_agree_vals n rho rho' (snd ps) Hag Hb2). exact Y.
      * exists ns. split; [|split; [exact (nodes_ok_agree Ai n rho rho' tv ns Hag Hb HN) | exact Hnin]].
        eapply achain_frame; [exact HA | intros z _; apply Hrm | intros z _ Hz; rewrite Hrm; exact Hz].
  - apply andb_prop in Hamb as [Hh Hg]. destruct HX as (ns & HA & HN & HL). exists ns. unfold Uv in *.
    rewrite <- (eval_agree_vals n rho rho' hd Hag Hh), <- (eval_agree_vals n rho rho' g Hag Hg).
    split; [|split; [exact (nodes_ok_agree Ai n rho rho' tv ns Hag Hb HN) | exact HL]].
    eapply achain_frame; [exact HA | intros z _; apply Hrm | intros z _ Hz; rewrite Hrm; exact Hz].
Qed.

Lemma JGAi_stable : ltac2:(tb__ "0|0|
S34S41S3fS0S0A2A1S51SacS2S2S41S6bA1S6aSedVNP;R8A2S36S3eSb8R9R8A2S40A3S36S3eS52RaR8A2S40A3S11RbR7R6A3S75RbRaR9R8R6R5A6S75RcRbRaR8R7R6A6F_;F_;F_;F_;F_;Fmd;Ftr;Frho';Frho;FAi;Fam;Ftv;Fn;").
Proof using ML.
  intros n tv am Ai rho rho' tr md Hle Hb Hamb Hag [HJ HX]. split.
  - exact (JGi_stable segs C NP Kc rho0 P0f FB ML n tv Ai rho rho' tr md Hle Hb Hag HJ).
  - eapply (XA_agree am Ai n rho rho' tv); [apply agree_below_vals; exact Hag | | exact Hamb | exact Hb | exact HX].
    intros a. destruct Hag as (_ & _ & Hm). symmetry. apply Hm.
Qed.

Lemma stableJ_JGA : ltac2:(tb__ "0|0|
S34S41S3fS0S0A2A1S51SedVNP;R3A2S36S3eSb8R4R3A2S40A3S36S3eS52R5R3A2S40A3S64R6S6cR5R4A2A2F_;F_;F_;Fam;Ftv;Fn;").
Proof using ML.
  intros n tv am Hle Hb Hamb rho rho' tr md Hag [Ai H]. exists Ai. eapply JGAi_stable; eauto.
Qed.

Lemma ok_frameJ_JGA : ltac2:(tb__ "0|0|
Sa9OF_;S41S3fS0S0A2A1S51S5fVsegs;R3VKc;A3S63Vsegs;R4S6cR3R2A2A3F_;Fam;Ftv;Fok;").
Proof using . intros ok tv am H rho tr ms md ms' (Ai & (_ & Hk & _) & _). exact (H tr ms md ms' Hk). Qed.

Lemma JGA_none : ltac2:(tb__ "0|0|
S41S3fS0S0A2A1S2S41S6bA1S6aS3bS6cR4S57R3R2R1A5Sd5Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R4R3R2R1AbA2Fmd;Ftr;Frho;Ftv;").
Proof using . intros tv rho tr md. split; [intros (Ai & H & _); exists Ai; exact H | intros [Ai H]; exists Ai; split; [exact H | exact I]]. Qed.

Definition nodeA (n : sstate * (list (sv * sv) * amode)) : jnode := ltac2:(tb__ "0|3|
S42S1S5eS44S1S3fS41S3fS0S0A2A1M0S51A2M1Vn;A3S6cS44G0S51S48S1G1Vn;A3M2A3S48G0S51G2A3A2A4").

Definition echeckA (nodes : list (sstate * (list (sv * sv) * amode))) (e : edge) : bool := ltac2:(tb__ "0|6|
S43S3fS1S3fS41S3fS0S0A2A1M0S51A2M1A2M2A1S3eLx;M3S66G2Vnodes;S103Ve;A1A3G2G2S3eLp;R1S1G1G1S3eLp0;R1G0S51G3S66G2Vnodes;S105Ve;A1A3G2G2S3eLp1;R1S1G1G1S3eLp2;R1G0S51S4aS4aS4aS4aS4aSb4S104Ve;A1M4VNP;A2SebVNP;S3R9A1M5A2A2Sb8G5R7A2A2Sc8G4R7R2A3A2S52G5R6A2A2S56S53G4R1A2R6A2A2Lamj;Ltvj;X3fx1Lp2;LTj;X3fx1Lp1;S49X43x2Lami;Ltvi;X3fx1Lp0;LTi;X3fx1Lp;S49X43x2").

Lemma XA_subst : ltac2:(tb__ "0|5|
Sb0S51SacS2S41S3fS0S0A2M0A1M1G1S36S41S3fS33S33A2M2A1S8cG0G2SbaSb1R3R6A2A1R1A4S8cG0G2SbaR3A1R2A4A3S4cG0G0S36S43G0A1M3S66G0R6R3A3S46G0R2A2M4A3S36G3S66G0R6R4A3G4A3S3bSb9Sb1R9RcA2R3A2Sb9R9R4A2A2F_;F_;Ft';Ft;Fk;S6eS53R8R7A2R6R5R4A4S6eR8R7Sb1R6R9A2R4A4F_;F_;F_;Ftv';Ftv;Frho;FAi;Fam;Fs;").
Proof using .
  clear_sec. intros s am Ai rho tv tv' M1 M2 HX.
  assert (NODES : forall ns, nodes_ok Ai rho tv ns -> nodes_ok Ai (rho_sub rho s) tv' ns).
  { intros ns [HF HD]. split; [|exact HD]. apply Forall_forall. intros bc Hin.
    destruct (proj1 (Forall_forall _ _) HF bc Hin) as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
    intros t' Ht' Hnz'. destruct (In_nth_error _ _ Ht') as [k Hk'].
    assert (exists t, nth_error tv k = Some t) as [t Hk].
    { pose proof (Forall2_map_eq _ _ _ _ M1) as L.
      destruct (nth_error tv k) eqn:En; [eexists; reflexivity|]. exfalso. apply nth_error_None in En.
      assert (k < length tv')%nat by (apply nth_error_Some; congruence). lia. }
    rewrite (map_nth2 _ _ _ _ k t t' M1 Hk Hk'). apply H3; [eapply nth_error_In; exact Hk|].
    apply (proj1 (M2 k t t' Hk Hk')). exact Hnz'. }
  destruct am as [|hd|hd nx cap sl|hd g]; cbn -[pl_subst] in HX |- *.
  - exact I.
  - unfold Uv in *. rewrite <- !eval_subst. destruct HX as (ns & HA & HN). exists ns. split; [exact HA | exact (NODES ns HN)].
  - unfold Uv in *. rewrite <- !eval_subst. destruct HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & ns & HA & HN & Hnin).
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split.
    + intros t' Ht' Hnz'. destruct (In_nth_error _ _ Ht') as [k Hk'].
      assert (exists t, nth_error tv k = Some t) as [t Hk].
      { pose proof (Forall2_map_eq _ _ _ _ M1) as L.
        destruct (nth_error tv k) eqn:En; [eexists; reflexivity|]. exfalso. apply nth_error_None in En.
        assert (k < length tv')%nat by (apply nth_error_Some; congruence). lia. }
      rewrite (map_nth2 _ _ _ _ k t t' M1 Hk Hk'). apply X5; [eapply nth_error_In; exact Hk|].
      apply (proj1 (M2 k t t' Hk Hk')). exact Hnz'.
    + split; [exact X6|]. split.
      * apply Forall_forall. intros ps Hps. unfold pl_subst in X7. rewrite Forall_map in X7.
        pose proof (proj1 (Forall_forall _ _) X7 ps Hps) as Y. cbv beta in Y. cbn [fst snd] in Y. rewrite <- !eval_subst. exact Y.
      * exists ns. split; [exact HA|]. split; [exact (NODES ns HN) | exact Hnin].
  - unfold Uv in *. rewrite <- !eval_subst. destruct HX as (ns & HA & HN & HL). exists ns.
    split; [exact HA|]. split; [exact (NODES ns HN) | exact HL].
Qed.

Lemma JGAi_transfer : ltac2:(tb__ "0|1|
Sb0S34S41S3fS0S0A2A1M0G0S51S51SacS2S2S41S6bA1S6aS36S3eSb4RbVNP;A2S40A3SedVNP;RbA2S36S3eSb8RcRbA2S40A3S36S3eSc8ReRcRbA3S40A3S36S3eS52ReRbA2S40A3S36S51S53R10RbA2RcA3S11R10RaR9A3S75R10ReRcRbR9R8A6S75R10ReRdSb1RbR13A2RaR9A6F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Ftr;Frho';Frho;FAi;Famj;Fami;Ftvj;Ftvi;Fn;Fs;").
Proof using ML.
  intros s n tvi tvj ami amj Ai rho rho' tr md H1 H2 H3 H5 Hamb Ham Hag HJ.
  pose proof (JGAi_stable n tvi ami Ai rho rho' tr md H2 H3 Hamb Hag HJ) as [HJ' HX'].
  split; [exact (JGi_transfer segs C NP Kc rho0 P0f FB ML s n tvi tvj Ai rho' rho' tr md H1 H2 H3 H5 (agree_below_refl _ _) HJ')|].
  destruct (tv_sub_eqb_sound s tvi tvj rho' H5) as [M1 M2].
  subst ami. eapply XA_subst; [exact M1 | exact M2 | exact HX'].
Qed.

Lemma echeckA_sound : ltac2:(tb__ "0|1|
S41S3fS1S3fS41S3fS0S0A2A1S51A2A2M0A1SfcS36S3eS76R2R1A2S40A3S106S8cG0SfeS74R3A4R2A2F_;Fe;Fnodes;").
Proof using ML.
  intros nodes e H Ti Tj Hi Hj rho rho' tr md Hag HJ HF.
  unfold echeckA in H. rewrite nth_error_map in Hi, Hj.
  destruct (nth_error nodes (e_src e)) as [[Si [tvi ami]]|]; [|discriminate].
  destruct (nth_error nodes (e_tgt e)) as [[Sj [tvj amj]]|]; [|discriminate].
  cbn in Hi, Hj. injection Hi as <-. injection Hj as <-. cbn [nodeA fst snd] in *. destruct HJ as [Ai HJ].
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Pos.leb_le in H2. apply am_eqb_sound in H6.
  exists Ai. eapply JGAi_transfer; eauto.
Qed.

Lemma echeckA_all : ltac2:(tb__ "0|1|
S41S3fS1S3fS41S3fS0S0A2A1S51A2A2M0A1S41SfcA1S36S3eS67SfcS76R2A1R1A3S40A3S8dSfcS106S8cG0SfeS74R3A4A1R2A3F_;Fes;Fnodes;").
Proof using ML.
  intros nodes es H. apply Forall_forall. intros e He. apply echeckA_sound.
  exact (proj1 (forallb_forall _ _) H e He).
Qed.

Lemma SPJ_entails_JGA : ltac2:(tb__ "0|2|
S1S1Sb0S41S3fS0S0A2A1M0G0S51S51S2Sa9S36S3eSf0R9R8R7A3S40A3S36S3eSb4R8VNP;A2S40A3S36S3eSebVNP;S3RbA1A2S40A3S36S3eSb8S3RcA1R9A2S40A3S36S3eSc8RbRaR9A3S40A3S36S3eS52S3ReA1R9A2S40A3S36S3eS56S53RdR9A2RaA2S40A3S5dVsegs;S6cRdRbA2M1R10R9R8A5S5dVsegs;G1R10Sb1RaRfA2R9A5F_;F_;F_;F_;F_;F_;F_;F_;Fw;Frho;Famj;Fami;Ftvj;Ftvi;Fs;FT;FL;").
Proof using ML.
  intros L T s tvi tvj ami amj rho w He H1 H2 H3 H5 H6 H7 [Hsm [Ai HJ]]. apply Pos.leb_le in H2. apply am_eqb_sound in H7.
  split; [eapply entails_sound; eauto|].
  destruct w as [tr [ms md]]. exists Ai. eapply JGAi_transfer; eauto. apply agree_below_refl.
Qed.

Definition andesc : Type := ltac2:(tb__ "0|0|
S3fS1S3fS41S3fS0S0A2A1S51A2A2").

Definition jcertA (fuel : nat) (cutpcs : list Z) (g : positive) (cutsD exitsD : list andesc) : bool := ltac2:(tb__ "0|4|
S4aS67S3fS1S3fS41S3fS0S0A2A1S51A2M0A2M1G1S4eS17S44S1G0R1A3A1A1Ln;VcutsD;A3S43S41SfcA1M2A1S3eLx;S102Vsegs;Vfuel;Vcutpcs;Vg;S8cG1S1S44S1G0A2M3VcutsD;A4S8cG1S1G3VexitsD;A4A6G2S67SfcS76S47S6fVcutsD;VexitsD;A3A1R1A3Les;S49X43x2A2").

Lemma map_fst_nodeA : ltac2:(tb__ "0|2|
S41S3fS1S3fS41S3fS0S0A2A1S51A2M0A2M1A1S36S41S1A1S8cS3fS1S5eA2S1S44S1S5eA2S8cG1SfeS74R1A4A4S8cG1S1S44S1G0A2R1A4A3Fl;").
Proof using . clear_sec. intros l. rewrite map_map. apply map_ext. intros [a b]. reflexivity. Qed.

Theorem cfg_sound_JGA : ltac2:(tb__ "0|6|
S4cS41S33A1S34S41S6fA1M0G0Sa9OF_;Sa8S5fVsegs;R2VKc;A3S36S3eS7fR8R7R6R5R4A5S40A3S1S41S3fS0S0A2A1M1S51S2S65S3fS1S3fG1S51A2M2A2M3S42S1G2R4S42G1S51R3R2A4A4M4R9A3SaaVsegs;R9S5dVsegs;S6cR4R3A2R5R2A4M5Sa9S3aS100Vsegs;S8cG3SfeS74RcA4R1A3R9R1A1A2Lw;A4F_;Frho;FamX;FtvX;FX;S1G1S51S2S65G3G4RbA3SaaVsegs;RaG5R9A4F_;Frho;FamT;FtvT;FT;F_;F_;F_;FQ;Fok;FexitsD;FcutsD;Fg;Fcutpcs;Ffuel;").
Proof using ML.
  intros fuel cutpcs g cutsD exitsD ok Q Hok Hc Hexits T tvT amT rho HinT.
  unfold jcertA in Hc. apply andb_prop in Hc as [Hstrict Hc].
  destruct (cfg_edges segs fuel cutpcs g (map fst cutsD) (map fst exitsD)) as [es|] eqn:Hes; [|discriminate].
  change (triple segs ok (SPJ segs (snd (nodeA (T, (tvT, amT)))) (fst (nodeA (T, (tvT, amT)))) rho) Q).
  apply (cfg_sound_genJ segs fuel cutpcs g (map nodeA cutsD) (map nodeA exitsD) es ok Q).
  - intros T' J' Hin. apply in_map_iff in Hin as ([S [k a]] & Heq & _). cbn in Heq. injection Heq as <- <-.
    apply ok_frameJ_JGA. exact Hok.
  - intros T' J' Hin Hlen. exfalso. apply in_map_iff in Hin as ([S [k a]] & Heq & Hin). cbn in Heq. injection Heq as <- <-.
    pose proof (proj1 (forallb_forall _ _) Hstrict _ Hin) as X. cbn [fst] in X. rewrite Hlen in X. discriminate.
  - rewrite !map_fst_nodeA. exact Hes.
  - rewrite <- map_app. apply echeckA_all. exact Hc.
  - intros X JX rho' Hin. apply in_map_iff in Hin as ([S [k a]] & Heq & Hin). cbn in Heq. injection Heq as <- <-.
    exact (Hexits S k a rho' Hin).
  - exact (in_map nodeA cutsD (T, (tvT, amT)) HinT).
Qed.

Definition aedesc : Type := ltac2:(tb__ "0|0|
S3fS3fS1S3fS41S3fS0S0A2A1S51A2A2S3fS33S0A2A2").
Definition ad_state (n : aedesc) : sstate := fst (fst n).
Definition ad_tv (n : aedesc) : list (sv * sv) := fst (snd (fst n)).
Definition ad_am (n : aedesc) : amode := snd (snd (fst n)).
Definition ad_rank (n : aedesc) : Z := fst (snd n).
Definition ad_var (n : aedesc) : sv := snd (snd n).
Definition ameas (n : aedesc) (rho : valuation) : Z := ltac2:(tb__ "0|0|
S9eSa2S79Vn;A1Sa0Z2Z40A2A2Sb6Q40SbVrho;S7dVn;A1A2A2A2").
Definition enodeA (n : aedesc) : enodeJ := ltac2:(tb__ "0|0|
S42S3fS1S5eA2S2S33Frho;S42S1S5eS72Vn;A1S6cS87Vn;A1S86Vn;A1A2A4S7aVn;A1A4").
Definition adrop (n : aedesc) : andesc := fst n.

Definition eecheckA (nodes : list aedesc) (e : edge) : bool := ltac2:(tb__ "0|4|
S43S6dA1S3eLx;M0S66S6dVnodes;S103Ve;A1A3S6dG0S66S6dVnodes;S105Ve;A1A3S6dS4aS4aS4aS76S8cS6dS6fS71Vnodes;A4Ve;A2SdS3S72R2A1A1S7dR2A1M1A2A2Sa3Z0S79R1A1M2A2A2S4fSa4G2S79R2A1M3A2S4aSa1G2G3A2Sf2S5S107Ve;A1A1Sb3S104Ve;A1S7dR1A1A2Z1G1A4A2A2A2Lnj;S49X43x2Lni;S49X43x2").

Lemma eecheckA_sound : ltac2:(tb__ "0|0|
S41S6dA1SfcS36S3eS7eR2R1A2S40A3S108S8cS6dSfdS77R3A4R2A2F_;Fe;Fnodes;").
Proof using ML.
  intros nodes e H Ti Tj Hi Hj rho rho' tr md Hag HJ HF.
  unfold eecheckA in H. rewrite nth_error_map in Hi, Hj.
  destruct (nth_error nodes (e_src e)) as [ni|] eqn:Eni; [|discriminate].
  destruct (nth_error nodes (e_tgt e)) as [nj|] eqn:Enj; [|discriminate].
  cbn in Hi, Hj. injection Hi as <-. injection Hj as <-.
  cbn [enodeA enj_state enj_pred enj_meas fst snd] in *.
  apply andb_prop in H as [H Hdec]. apply andb_prop in H as [H Hrk]. apply andb_prop in H as [He Hvb].
  apply Z.leb_le in Hrk.
  split.
  - pose proof (echeckA_sound (map adrop nodes) e He) as EOK.
    specialize (EOK (nodeA (adrop ni)) (nodeA (adrop nj))).
    rewrite !nth_error_map, Eni, Enj in EOK. cbn [option_map nodeA adrop fst snd] in EOK.
    exact (EOK eq_refl eq_refl rho rho' tr md Hag HJ HF).
  - unfold ameas. rewrite <- eval_subst.
    rewrite (eval_agree _ rho rho' (ad_var ni) Hag Hvb).
    pose proof (urange (eval rho' (sv_subst (e_sub e) (ad_var nj)))) as R1.
    pose proof (urange (eval rho' (ad_var ni))) as R2.
    apply orb_prop in Hdec. destruct Hdec as [Hlt | Heq].
    + apply Z.ltb_lt in Hlt. nia.
    + apply andb_prop in Heq as [Heq Hu]. apply Z.eqb_eq in Heq.
      pose proof (uleq_sound rho' _ _ 1 _ HF Hu) as U1. unfold U in U1. rewrite Heq. lia.
Qed.

Definition ejcertA (fuel : nat) (cutpcs : list Z) (g : positive) (cutsE exitsE : list aedesc) : bool := ltac2:(tb__ "0|1|
S4aS67S6dS6dS4eS17S72R1A1A1A1Ln;VcutsE;A3S43S41SfcA1M0A1S3eLx;S102Vsegs;Vfuel;Vcutpcs;Vg;S8cS6dS1S72VcutsE;A4S8cS6dS1S72VexitsE;A4A6G0S67SfcS7eS47S6dVcutsE;VexitsE;A3A1R1A3Les;S49X43x2A2").

Lemma map_ad_state : ltac2:(tb__ "0|0|
S41S6dA1S36S41S1A1S8cSfdS1S109S8cS6dSfdS77R1A4A4S8cS6dS1S72R1A4A3Fl;").
Proof using . clear_sec. intros l. rewrite map_map. apply map_ext. intros [[a b] c]. reflexivity. Qed.

Theorem cfg_complete_JGA : ltac2:(tb__ "0|8|
S4cS41S33A1S34S41S6dA1M0G0Sa8S36S3eS82R6R5R4R3R2A5S40A3S1S41S3fS0S0A2A1M1S51S3fS33S0A2M2S2S65S3fS3fS1S3fG1S51A2M3A2M4G2A2M5S42G4G2S42S1G3R5S42G1S51R4R3A4A4R2A4M6R8A3SabVsegs;S5dVsegs;S6cR5R4A2R6R2A4M7Sa9S3aSffVsegs;S8cS6dSfdS77RbA4S7aS42G4G2S42S1G3R7S42G1S51R6R5A4A4R4A4R3A2R1A4R9R1A1A2Lw;A3F_;Frho;FrvX;FamX;FtvX;FX;S1G1S51G2S2S65G5G6RaA3SabVsegs;G7R9A3F_;Frho;FrvT;FamT;FtvT;FT;F_;F_;FQ;FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;").
Proof using ML.
  intros fuel cutpcs g cutsE exitsE Q Hc Hexits T tvT amT rvT rho HinT.
  unfold ejcertA in Hc. apply andb_prop in Hc as [Hstrict Hc].
  destruct (cfg_edges segs fuel cutpcs g (map ad_state cutsE) (map ad_state exitsE)) as [es|] eqn:Hes; [|discriminate].
  change (etriple segs (SPJ segs (enj_pred (enodeA (T, (tvT, amT), rvT))) (enj_state (enodeA (T, (tvT, amT), rvT))) rho) Q).
  apply (cfg_complete_genJ segs fuel cutpcs g (map enodeA cutsE) (map enodeA exitsE) es Q).
  - apply forallb_forall. intros m Hm. apply in_map_iff in Hm as (m0 & <- & Hm0).
    exact (proj1 (forallb_forall _ _) Hstrict m0 Hm0).
  - rewrite !map_ad_state. exact Hes.
  - rewrite <- map_app. apply Forall_forall. intros e He. apply eecheckA_sound.
    exact (proj1 (forallb_forall _ _) Hc e He).
  - intros En rhoE HinE. apply in_map_iff in HinE as ([[X [tvX amX]] rvX] & <- & HinE0).
    exact (Hexits X tvX amX rvX rhoE HinE0).
  - exact (in_map enodeA cutsE (T, (tvT, amT), rvT) HinT).
Qed.

Lemma map_fst_adrop : ltac2:(tb__ "0|1|
S41S6dA1S36S41S1A1S8cS3fS1S3fS41S3fS0S0A2A1S51A2M0A2S1S44S1G0A2S8cS6dS6fS71R1A4A4S8cS6dS1S72R1A4A3Fl;").
Proof using . clear_sec. intros l. rewrite map_map. apply map_ext. intros [[a b] c]. reflexivity. Qed.

Lemma eecheckA_echeckA : ltac2:(tb__ "0|0|
S41S6dA1SfcS36S3eS7eR2R1A2S40A3S36S3eS76S8cS6dS6fS71R3A4R2A2S40A3F_;Fe;Fnodes;").
Proof using .
  clear_sec. intros nodes e H. unfold eecheckA in H.
  destruct (nth_error nodes (e_src e)) as [ni|]; [|discriminate].
  destruct (nth_error nodes (e_tgt e)) as [nj|]; [|discriminate].
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. exact H.
Qed.

Lemma ejcertA_jcertA : ltac2:(tb__ "0|1|
S4cS41S33A1S34S41S6dA1M0G0S36S3eS82R5R4R3R2R1A5S40A3S36S3eS7fR6R5R4S8cS6dS6fS71R3A4S8cS6dS6fS71R2A4A5S40A3F_;FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;").
Proof using .
  clear_sec. intros fuel cutpcs g cutsE exitsE H. unfold ejcertA in H. unfold jcertA.
  rewrite !map_fst_adrop. apply andb_prop in H as [Hs H]. apply andb_true_intro. split.
  - apply forallb_forall. intros n Hn. apply in_map_iff in Hn as (m & <- & Hm). cbn [adrop fst].
    exact (proj1 (forallb_forall _ _) Hs m Hm).
  - destruct (cfg_edges segs fuel cutpcs g (map ad_state cutsE) (map ad_state exitsE)) as [es|]; [|discriminate].
    rewrite <- map_app. apply forallb_forall. intros e He. apply eecheckA_echeckA.
    exact (proj1 (forallb_forall _ _) H e He).
Qed.

Theorem cfg_sound_JGAE : ltac2:(tb__ "0|8|
S4cS41S33A1S34S41S6dA1M0G0Sa9OF_;Sa8S5fVsegs;R2VKc;A3S36S3eS7fR8R7R6S8cS6dS6fS71R5A4S8cS6dS6fS71R4A4A5S40A3S1S41S3fS0S0A2A1M1S51S3fS33S0A2M2S2S65S3fS3fS1S3fG1S51A2M3A2M4G2A2M5S42G4G2S42S1G3R5S42G1S51R4R3A4A4R2A4M6RaA3SaaVsegs;RaS5dVsegs;S6cR5R4A2R6R2A4M7Sa9S3aS100Vsegs;S8cG4SfeS74S8cS6dS6fS71RdA4A4R1A3RaR1A1A2Lw;A4F_;Frho;FrvX;FamX;FtvX;FX;S1G1S51G2S2S65G5G6RcA3SaaVsegs;RbG7RaA4F_;Frho;FrvT;FamT;FtvT;FT;F_;F_;F_;FQ;Fok;FexitsE;FcutsE;Fg;Fcutpcs;Ffuel;").
Proof using ML.
  intros fuel cutpcs g cutsE exitsE ok Q Hok Hc Hexits T tvT amT rvT rho HinT.
  apply (cfg_sound_JGA fuel cutpcs g (map adrop cutsE) (map adrop exitsE) ok Q Hok Hc).
  - intros X tvX amX r Hin. apply in_map_iff in Hin as ([[X' [tv' am']] rv'] & Heq & Hin). cbn in Heq. injection Heq as <- <- <-.
    exact (Hexits X' tv' am' rv' r Hin).
  - exact (in_map adrop cutsE (T, (tvT, amT), rvT) HinT).
Qed.

Lemma reenter_cutGAE : ltac2:(tb__ "0|4|
Sa9OF_;S41S6dA1S1S41S3fS0S0A2A1M0S51S3fS33S0A2M1Sa8S2S65S3fS3fS1S3fG0S51A2M2A2M3G1A2S42G3G1S42S1G2R6S42G0S51R5R4A4A4R3A4R7A3SaaVsegs;R9S5dVsegs;S6cR6R5A2R7R2A4Sa9S3aS100Vsegs;S8cG3SfeS74S8cS6dS6fS71R9A4A4R1A3R4R1A1A2Lw;A4F_;Frho;FQ;Frv;Fam;Ftv;FT;FcutsE;Fok;").
Proof using .
  intros ok cutsE T tv am rv Q rho Hin.
  eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
  intros w Hw. left. exists T, (JGA tv am), rho. split; [|exact Hw].
  exact (in_map nodeA (map adrop cutsE) (T, (tv, am)) (in_map adrop cutsE (T, (tv, am), rv) Hin)).
Qed.

Lemma ereenter_cutAE : ltac2:(tb__ "0|5|
S41S6dA1S1S41S3fS0S0A2A1M0S51S3fS33S0A2M1Sa8S33S2S65S3fS3fS1S3fG0S51A2M2A2M3G1A2S42G3G1S42S1G2R7S42G0S51R6R5A4A4R4A4R8A3S37S9dZ0S7aS42G3G1S42S1G2R8S42G0S51R7R6A4A4R5A4R2A2M4A2S9fG4R3A2A2SabVsegs;S5dVsegs;S6cR8R7A2R9R3A4Sa9S3aSffVsegs;S8cS6dSfdS77RbA4R5R1A4R6R1A1A2Lw;A3F_;F_;Frho;Fbound;FQ;Frv;Fam;Ftv;FT;FcutsE;").
Proof using .
  intros cutsE T tv am rv Q bound rho Hin Hm w Hw. exists w. split; [apply wsteps_refl|]. left.
  exists (enodeA (T, (tv, am), rv)), rho. split; [exact (in_map enodeA cutsE _ Hin)|]. split; [exact Hw | exact Hm].
Qed.

Lemma ereenter_rankA : ltac2:(tb__ "0|4|
S41S6dA1S1S41S3fS0S0A2A1M0S51S33S0Sa8S6dS2S2S65S3fS3fS1S3fG0S51A2M1A2M2S3fS33S0A2M3A2S42G2G3S42S1G1R9S42G0S51R8R7A4A4S42S33S0R6R5A4A4RaA3S9dZ0R7A2S9dS9eR8Z1A2S79R5A1A2SabVsegs;S5dVsegs;S6cRbRaA2RcR4A4Sa9S3aSffVsegs;S8cS6dSfdS77ReA4S7aR7R6A2R1A4R8R1A1A2Lw;A3F_;F_;F_;Frho;FrhoX;FX;FQ;FvT;FrT;Fam;Ftv;FT;FcutsE;").
Proof using .
  intros cutsE T tv am rT vT Q X rhoX rho Hin H0 Hr. apply (ereenter_cutAE cutsE T tv am (rT, vT) Q); [exact Hin|].
  unfold ameas, ad_rank, ad_var in *. cbn [fst snd] in *.
  pose proof (urange (eval rho vT)). pose proof (urange (eval rhoX (snd (snd X)))). nia.
Qed.

Definition am_svs (am : amode) : list sv := ltac2:(tb__ "0|3|
S51S41S0A1Lam;Vam;S4bS0A1M0S0S45S0R1G0A3M1Lhd;S0S0S0S41S3fS0S0A2M2A1S47S0S45S0R4S45S0R3S45S0R2G0A3A3A3S69G2S0G2S45S0S44S0S0R1A3S45S0S48S0S0R1A3G0A3A3Lps;R1A4A3Lsl;Lcap;Lnx;Lhd;S0S0S45S0R2G1A3Lg;Lhd;X51x4").
Lemma am_svs_below : ltac2:(tb__ "0|0|
S34S51S0S36S3eS52R3R2A2S40A3S65S0R2S80R3A1A3S36S3eSdR5R3A2S40A3F_;F_;Fe;Fam;Fn;").
Proof using .
  clear. intros n [|hd|hd nx cap sl|hd g] e Hb He; cbn -[pl_below flat_map] in Hb, He.
  - destruct He.
  - destruct He as [<-|[]]. exact Hb.
  - apply andb_prop in Hb as [Hb Hsl]. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
    destruct He as [<-|[<-|[<-|He]]]; try assumption.
    apply in_flat_map in He as (ps & Hps & He).
    pose proof (proj1 (forallb_forall _ _) Hsl ps Hps) as Hp. apply andb_prop in Hp as [Hp1 Hp2].
    destruct He as [<-|[<-|[]]]; assumption.
  - apply andb_prop in Hb as [H1 H2]. destruct He as [<-|[<-|[]]]; assumption.
Qed.

Definition hdr_open (am : amode) (rho : valuation) (z : Z) : Prop := ltac2:(tb__ "0|1|
S51OLam;Vam;S3cS0S3cLhd;S0S0S0S41S3fS0S0A2A1S37S9dVUv;Vrho;R4A2M0Vz;A2S9fVz;S9eG0Z18A2A2A2Lslots;Lcap;Lnx;Lhd;S0S0S3cLg;Lhd;X51x4").

Definition untracked (rho : valuation) (tv : list (sv * sv)) (bn : Z * Z) : Prop := ltac2:(tb__ "0|1|
S3fS0S0A2M0S65G0R1Vtv;A3Sb9Vrho;R2A2S39S36S3fS33S33A2SbaVrho;R3A2Vbn;A3A1F_;F_;Ft;").

Lemma blocks_disjoint : ltac2:(tb__ "0|2|
SacS2S6aS33S33S33S33S33SdcVsegs;VC;R8R7R6A5S65S3fS33S33A2M0S42S33S33R6R5A4M1SadR9A1A3S65G0S42S33S33R5R4A4SadRaA1A3S39S36G0S42S33S33R8R7A4G1A3A1S37S9dR9R5A2S9fR5S9eR9R8A2A2A2S37S9dR8R6A2S9fR6S9eR8R7A2A2A2S3cF_;F_;F_;F_;F_;F_;Fz;Fn2;Fb2;Fn1;Fb1;Fmd;Frho;FAi;").
Proof using .
  clear_sec. intros Ai rho md b1 n1 b2 n2 z HM H1 H2 Hne Hz1 Hz2. unfold MInvR in HM.
  destruct (pairwise_in2 _ _ _ _ (minv_blocks_pairwise C Ai _ _ _ HM) H1 H2) as [X|[X|X]];
    [exact (Hne X) | |]; unfold MallocInv.ranges_disjoint in X; cbn [fst snd] in X; lia.
Qed.

Lemma XA_transport : ltac2:(tb__ "0|7|
S51SacSacS2S2S6aS41S3fS0S0A2M0A1M1G1SdcVsegs;VC;R7R5R3A5S6eR9R8R6R3A4S0S65S0R1S80RbA1A3S36Sb5Q40M2A1SbR8R2A2SbR9R2A2A3F_;Fe;S33S33S65S3fS33S33A2M3S42S33S33R2R1A4M4SadRcA1A3S7cRbR8S42S33S33R3R2A4M5A3S65G3S42S33S33R4R3A4SadRdA1A3F_;F_;Fn;Fb;S33S33S33S65G3G4SadReA1A3S7cRdRaG5A3S37S9dR4R5A2S9fR5S9eR4R3A2A2A2S39S89R12RfR6A3A1S36S43Sb5Q8A1A1SaRfSb7G2R7A2M6A2SaR10G6A2A3F_;F_;F_;F_;Fn;Fb;Fz;G0S65G0R1R7A3Sb9RbR2A2S3aS38G0G0S37S65G0R1RbA3S37Sb9ReR1A2S36G3SbaReR1A2SbaRdR4A2A3A2A2Lt;A2G3S65G3R1SadR10A1A3S39S36G3R2SbaReR5A2A3A1F_;Fbn;A2F_;F_;Ft2;S6eReRcRaR7A4F_;F_;F_;F_;F_;F_;Ftv2;Ftv;Fmd;Frho2;Frho;FA2;FAi;Fam;").
Proof using Kc P0f.
  intros am Ai A2 rho rho2 md tv tv2 HM HX Hvals Hblk Hrm Htv2.

  assert (NOK : forall ns, nodes_ok Ai rho tv ns -> nodes_ok A2 rho2 tv2 ns).
  { intros ns [HF HD]. split; [|exact HD]. apply Forall_forall. intros [b cap] Hin.
    destruct (proj1 (Forall_forall _ _) HF _ Hin) as (H1 & H2 & H3). cbn [fst snd] in *.
    split; [exact (Hblk _ _ H1 H3)|]. split; [exact H2|].
    intros t2 Ht2 Hnz2 Heq. destruct (Htv2 t2 Ht2 Hnz2) as [(t & Ht & Hnz & Htt)|Hfresh].
    - apply (H3 t Ht Hnz). rewrite Htt. exact Heq.
    - exact (Hfresh _ H1 (eq_sym Heq)). }

  assert (ACH : forall ns h, nodes_ok Ai rho tv ns -> achain (rm rho) h ns ->
            (forall b cap z, In (b, cap) ns -> b <= z < b + HDR + cap -> ~ hdr_open am rho z) ->
            achain (rm rho2) h ns).
  { intros ns h [HF _] HA Hho. eapply achain_frame; [exact HA| |].
    - intros z (b & cap & Hin & Hz). destruct (proj1 (Forall_forall _ _) HF _ Hin) as (H1 & _ & H3). cbn [fst snd] in *.
      pose proof (proj1 (Forall_forall _ _) (achain_caps _ _ _ HA) _ Hin) as [Hc _]. cbn in Hc.
      apply (Hrm z b (HDR + cap) H1 H3); [unfold HDR; lia|]. apply (Hho b cap); [exact Hin | unfold HDR; lia].
    - intros z (b & cap & Hin & Hz) Hdef. destruct (proj1 (Forall_forall _ _) HF _ Hin) as (H1 & _ & H3). cbn [fst snd] in *.
      rewrite (Hrm z b (HDR + cap) H1 H3); [exact Hdef | lia | exact (Hho b cap z Hin Hz)]. }
  destruct am as [|hd|hd nx cap sl|hd g]; cbn -[flat_map] in HX |- *.
  - exact I.
  - destruct HX as (ns & HA & HN). exists ns. unfold Uv in *. rewrite (Hvals hd ltac:(left; reflexivity)).
    split; [|exact (NOK ns HN)]. apply (ACH ns _ HN HA). intros b c z _ _ Hf. exact Hf.
  - unfold Uv in *. cbn -[flat_map] in Hvals.
    rewrite (Hvals hd ltac:(auto)), (Hvals nx ltac:(auto)), (Hvals cap ltac:(auto)).
    destruct HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & ns & HA & HN & Hnin).
    split; [exact X1|]. split; [exact X2|]. split; [exact (Hblk _ _ X3 X5)|]. split; [exact X4|]. split.
    + intros t2 Ht2 Hnz2 Heq. destruct (Htv2 t2 Ht2 Hnz2) as [(t & Ht & Hnz & Htt)|Hfresh].
      * apply (X5 t Ht Hnz). rewrite Htt. exact Heq.
      * exact (Hfresh _ X3 (eq_sym Heq)).
    + split.
      * intros z Hz. unfold HDR in *. rewrite (Hrm z _ _ X3 X5); [exact (X6 z Hz) | lia | cbn; unfold Uv; lia].
      * split.
        { apply Forall_forall. intros ps Hps. pose proof (proj1 (Forall_forall _ _) X7 ps Hps) as Y. cbv beta in Y.
          assert (Hin2 : forall e, In e [fst ps; snd ps] -> In e ([hd; nx; cap] ++ flat_map (fun ps0 => [fst ps0; snd ps0]) sl)).
          { intros e He. apply in_or_app. right. apply in_flat_map. exists ps. split; [exact Hps | exact He]. }
          rewrite (Hvals (fst ps) (Hin2 _ ltac:(left; reflexivity))), (Hvals (snd ps) (Hin2 _ ltac:(right; left; reflexivity))). exact Y. }
        exists ns. split; [|split; [exact (NOK ns HN) | exact Hnin]].
        apply (ACH ns _ HN HA). intros b c z Hin Hz Hho. cbn in Hho.
        destruct HN as [HF _]. destruct (proj1 (Forall_forall _ _) HF _ Hin) as (H1 & _ & _). cbn [fst snd] in H1.
        apply (blocks_disjoint Ai rho md b (HDR + c) _ _ z HM H1 X3); [|lia|unfold Uv, HDR in *; lia].
        intros Heq. injection Heq as -> _. apply Hnin. apply in_map_iff. exists (bv_unsigned (eval rho hd), c). split; [reflexivity | exact Hin].
  - destruct HX as (ns & HA & HN & HL). exists ns. unfold Uv in *.
    rewrite (Hvals hd ltac:(left; reflexivity)), (Hvals g ltac:(right; left; reflexivity)).
    split; [|split; [exact (NOK ns HN) | exact HL]]. apply (ACH ns _ HN HA). intros b c z _ _ Hf. exact Hf.
Qed.

Lemma rm_kept_cont : ltac2:(tb__ "0|6|
SacSacS2S2S2Sf4Sb0S41S4A1S6aS6aS33S33S33SdcVsegs;VC;RdRbR5A5M0G0S65S3fS33S33A2M1S42S33S33R4R3A4SadRfA1M2A3S65G1S42S33S33R5R4A4G2A3S37S9dR6R7A2S9fR7S9eR6R5A2A2A2SeaVsegs;VC;R12R11SaSb1Sb2R10RbRdA3RcA2A1SaRfA1A6Sb5Q40M3A1S36S43Sb5Q8A1A1M4SaR10R1A2SaR11R1A2A3Fa;S36G4SaSdaR10Sd9R12R10RdA3A2Sb7G3RaA2M5A2SaR12G5A2A3F_;F_;F_;F_;F_;F_;F_;Fn;Fb;Fz;FmdL;Fmd;FR;Fs;Fms;Frho';FrhoL;Frho;FA2;FAi;").
Proof using ML.
  clear - ML HNP. intros Ai A2 rho rhoL rho' ms s R md mdL z b n HM HM2 Hb Hb2 Hz Hkept Hrm.
  cbn [rho_patch rm]. unfold patchf.
  destruct (in_ranges_dec rho R (Z_to_bv 64 z)) as [Hi|Hn]; [reflexivity|].
  rewrite Hrm.
  pose proof HM as HMi. unfold MInvR in HMi.
  pose proof (block_addr_props segs C Ai _ _ _ b n z ML HMi Hb Hz) as [Hlt _].
  assert (Hzr : 0 <= z < 2 ^ 64).
  { pose proof (minv_block_geom C Ai _ _ _ b n HMi Hb) as (G0 & _ & G2 & _). unfold PGSZ, UNIT in G2. top_ranges. lia. }
  assert (C1 : caddr segs C Ai None z) by (right; right; exists b, n; split; [exact Hb|]; split; [discriminate|exact Hz]).
  assert (C2 : caddr segs C A2 None z) by (right; right; exists b, n; split; [exact Hb2|]; split; [discriminate|exact Hz]).
  destruct (caddr_props segs C Ai None z rho md ML HM Hzr C1) as (O1 & O2 & O3).
  destruct (caddr_props segs C A2 None z rhoL mdL ML HM2 Hzr C2) as (O1' & _ & _).
  transitivity (rm (rho_sub (rho_absorb rho R ms) s) (Z_to_bv 64 z)).
  - apply Hkept; try assumption; [exact (caddr_client segs C _ _ _ C1) | exact (caddr_client segs C _ _ _ C2) |]. intros Hs. apply O3. apply (static_alloc_static C). exact Hs.
  - apply rm_absorb_out. exact Hn.
Qed.

Lemma pclF_caddr_chk : ltac2:(tb__ "0|0|
S1S1Sb0S41S4A1S41S1A1S2SacS33S8eVNP;Vrho0;R3A3S36S3eSbdVC;VNP;R9R8R7R6R5A7S40A3SbfR5Sf7SaeR4A1A1A2SbcVFB;R5A2Sc0Vsegs;VC;Vrho0;VFB;R5A5SccVsegs;VC;R7S4dS33A1R6A5F_;F_;F_;F_;F_;Fa;FAi;Frho;Fposts;FR;Fs;FPre;FCl;").
Proof using .
  clear ML. intros Cl Pre s R posts rho Ai a [Hw _] Hchk [HT _] HP Hp.
  unfold call_checkT in Hchk. apply andb_prop in Hchk as [_ Hchk]. apply andb_prop in Hchk as [_ Hn]. apply Pos.ltb_lt in Hn.
  destruct Hp as [H|[H|(b & n & Hin & Hr)]]; [left | right; left; exact H | right; right].
  - unfold T0 in H. rewrite (Hw V_TOP Hn), HT in H. exact H.
  - exists b, n. split; [exact (HP _ Hin)|]. split; [discriminate | exact Hr].
Qed.

Section CallT.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S5eS1S2Sa8S8dS6ScR2A1S5R3A1A3VTR;S5dVsegs;R5R4R3A4R2A2M0F_;G0F_;FQ;Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q) -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sa8Sa8Sa8Sa9R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S5eS5eS1S1Sb0S41S4A1M0S41S3fS1S8fA2M1A1Sa8S2S36S43G0A1SefR7R6R5A3S46G0R4A2A3S36S3eS97R8R7R6R5S8cG1S1S44S1S8fA2R4A4A5S40A3S2VTR;S5dVsegs;RbR9R1A4S90Vsegs;S3R9A1R1R6A4A2Frho1;S41S6bA1M2Sf4S6aSfVsegs;R7RdS42G2SfaR3SfbR2R1A2A4A4R10R8R4R2A3R10Sb1Sb2R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S1S8fG2Sf4S6aS2G2Sf4S6aS65G1S42S1S8fR9R8A4R10A3SfVsegs;RfR15S42G2SfaR8SfbR7R6A2A4A4R18R10R9R7A3S8eS3R16A1Sb1Sb2R11R14R9A3R15A2R7A3SfVsegs;R8RdS42G2SfaR7SfbR6R5A2A4A4RdSb1Sb2R13R16RbA3R17A2R9R8R6A4S37S99R14RcR17R18R19RfRaA7S2S98R15RdR18R19R1aR1bR10R1RbA9VTR;S5dVsegs;S96R10Sb1Sb2R16R19ReA3R1aA2RcA3S93R1aS3R1bA1R11S3R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S5dVsegs;ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;FPre;FC0;FJp;FJ;").
Hypothesis TR_callJ : ltac2:(tb__ "0|3|
S5eS5eS5eS5eS1S1Sb0S41S4A1M0S41Sf1A1Sa8S2S36S43G0A1SefR7R6R5A3S46G0R4A2A3S36S3eS94R8R7R6R5R4A5S40A3S2VTR;S5dVsegs;RdR9R1A4S62Vsegs;RcS3R9A1R1R6A5A2Frho1;S41S6bA1M1Sf4S6aSfVsegs;R7RdS42G1SfaR3SfbR2R1A2A4A4R12R8R4R2A3R12Sb1Sb2R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;Sf1S2S2G1Sf4S6aG1S6aS65Sf1R8RfA3SfVsegs;ReR14S42G1SfaR6SfbR5R4A2A4A4R19RfR7R5A3S9aR10R7R13R14R15R16Sf3RbA1RaR9A9R19RaR6R5A3R19RcR7R6A3F_;F_;F_;F_;F_;Fmd';Ftr';Fmd;Fms;Ftr;FrhoL;Frho';FL;Sf1S2S65Sf1R2RaA3S11S3RfA1M2R9R2A3VTR;S5dVsegs;R11S93ReG2Sf3R4A1S3R10A1RdA5R3A4RbA2F_;F_;Frho';FL;VTR;S5dVsegs;R11RdR7A4R8A2F_;F_;F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;FPre;FC0;FJc';FJp';FJp;FJ;").

Theorem malloc_callAT : ltac2:(tb__ "0|9|
S1Sb0S41S4A1M0S2S41S3fS0S0A2M1A1S51Sa8SacS2VTR;S5dVsegs;Se6Vsegs;VC;R2VKc;A4SdfVE;A1M2R1A4S90Vsegs;S10aR1Se8Vsegs;VC;VE;R2VKc;A5A4A2Frho1;FAi;S36S43G0A1SefR8G2R7A3S46G0R6A2A3S36S3eSbdVC;VNP;R9G2R8R7S45S1SddVE;A1M3S45S1SdeVE;A1M4S4bS1A1A3A3A7S40A3S36S3eSebVNP;S3RaA1A2S40A3S36S3eSb8S3RbA1R7A2S40A3S36S3eS52S3RcA1R7A2S40A3S36S3eSdS3RdA1SafRcPcM5A2A2S40A3S36S0SafS92RdS10aG4S3ReA1M6A4Se0A2S9S91G6UaM7A2A1A3SacS8dS6ScRdA1S5R10A1A3VP0f;Vrho0;A1S8eVNP;Vrho0;RfA3SbcVFB;R4A2SbeVFB;R5R11R10A4Sc1R12R11A2Sc2R13R12A2S6eR12R8R14R13A4S38S2S2S38S6aS6aSdcVsegs;VC;RbR2R1A5Lmd;A2LrhoM;A2SbfR16Sf7SaeRaA1A1A2S37Sc7Vsegs;VC;RbS4dS33A1R17R18A6S9fZ0Sb6Q40SbR17SafR19G5A2A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S2S8eS3R11A1ReR1A3VTR;S5dVsegs;S6cReRdA2M8SbbR12R11R10G3A4R2A4RcA2F_;Frho';S2S8eS3R12A1RfR1A3VTR;S5dVsegs;S6cS45G1S42S0S0S9S91S3R13A1G7A2A1SafR12G5A2A4RfA3ReA2SbbR13R12R11G4A4R2A4RdA2F_;Frho';VTR;S5dVsegs;G8R12RfA4RcA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Ftv;Frho;FR;Fs;FCl;").
Proof using ML TR_callP TR_ex TR_facts TR_pre.
  intros Cl s R rho tv am Q CALLEE He Hchk Hnf Hnb Hamb Hs12 Hres HR Tnull Tok.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex MA (JGAi tv am)). intros Ai.
  eapply (TR_callP (JGAi tv am Ai) (J_alloc_pre segs C Ai Kc) Cl (Pre_malloc E) s R
            (Posts_malloc segs C E Ai Kc) Q rho He).
  - exact (call_checkT_P _ _ _ _ _ _ _ Hchk).
  - intros rho1. apply CALLEE.
  -
    intros tr ms md Hsm [(Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0) HXA]. split; [|split; [exact Hk | split; [exact (tp_of_TPI _ _ _ _ _ _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk) | split; [exact (proj1 (proj2 HM)) | exact (top_of_TPI _ _ _ _ _ _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk)]]]].
    destruct (HR Ai HF HP0 Hav HP HN HD HZ HXA (ex_intro _ rho (ex_intro _ md (MI1 segs C _ _ _ _ HM))) ltac:(eapply T_of_chk; [exact Hav | exact (proj2 (proj2 HM)) | exact Hchk])) as [HRok _].
    eapply MI1. eapply (MInvR_mem segs C _ ML); [exact HM| |reflexivity].
    intros a Ha Ho. apply rm_absorb_out. eapply (R_miss segs C ML Ai None rho rho md R a (MI1 segs C _ _ _ _ HM)); [exact HRok|exact Ha|exact Ho].
  -
    intros L JL tr ms md rhoL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    destruct HJ as [(Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0) HXA].
    destruct (HR Ai HF HP0 Hav HP HN HD HZ HXA (ex_intro _ rho (ex_intro _ md (MI1 segs C _ _ _ _ HM))) ltac:(eapply T_of_chk; [exact Hav | exact (proj2 (proj2 HM)) | exact Hchk])) as [HRok Hpos].
    cbn [Posts_malloc In] in HinL.
    destruct HinL as [HinL | [HinL | []]]; injection HinL as HL HJLe; subst L JL.
    +
      destruct HJL as (A' & HM' & HbA' & Hkept & Hinit & _).
      assert (HsubA' : forall a, caddr segs C Ai None a -> caddr segs C A' None a) by (intros a; apply (caddr_mono segs C _ _ _ _ (init_kept_top _ _ Hinit)); intros b Hb; rewrite HbA'; exact Hb).
      split.
      * split; [exact (KEPT_step segs C ML Ai A' rho rhoL ms s R md md' (MI1 segs C _ _ _ _ HM) HM' HRok HsubA' Hkept)|].
        intros o' oR Hin' _. cbn in Hin'. destruct Hin'.
      * intros rho' Hlink.
        eapply TR_pre; [ | apply (Tnull (rho_patch rho' (patchf rho rho' R)) ltac:(eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]))].
        intros w [Hsm' HJ']. cbn [J_ofP] in HJ'.
        destruct HJ' as (A2 & HM2 & HbA2 & Hkept2 & Hinit2 & Hk2).
        assert (Hag' : agree_vals (ss_next Cl) rho rho') by (destruct Hlink as (A & _); exact A).
        assert (HsubA : forall b, In b (ma_blocks Ai) -> In b (ma_blocks A2)) by (intros b Hb; rewrite HbA2; exact Hb).
        split; [exact (cont_smatch segs Cl (Pre_malloc E) _ s R rho rho' tr ms md w He Hsm eq_refl Hag' Hsm')|].
        exists A2. split. { split; [|split; [exact Hk2|split; [|split; [|split; [split; [|split]|split; [|exact HP0]]]]]].
        -- eapply agree_vals_trans; [exact Hav|].
           eapply agree_vals_trans; [eapply agree_vals_le; [exact Hnf| exact Hag']| apply agree_vals_patch].
        -- eapply (MInvR_cont segs C _ ML Ai); [exact (conj HM2 (conj (init_kept_init _ _ Hinit2 (proj1 (proj2 HM))) (TPI_kept _ _ _ _ (init_kept_top _ _ Hinit2) (proj2 (proj2 HM))))) | exact HRok | intros a; apply (caddr_mono segs C _ _ _ _ (init_kept_top _ _ Hinit2)); exact HsubA | intros a; eapply call_linkP_rm; exact Hlink].
        -- intros b Hb. apply HsubA. exact (HP b Hb).
        -- apply (tvin_agree FB A2 (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb |].
           unfold tvin in HN |- *. apply Forall_forall. intros t Ht Hnz.
           destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [apply HsubA; exact X1 | exact X2].
        -- apply (tvd_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HD].
        -- apply (tvz_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HZ].
        -- eapply (keptF_step segs C rho0 FB ML Ai A2 rho rhoL ms s R md _ rho' HP); [intros b Hb; apply HsubA; exact (HP b Hb) | exact HM | exact HM2 | exact (init_kept_top _ _ Hinit2) | exact HRok | exact HK | exact Hkept2 | intros a; eapply call_linkP_rm; exact Hlink]. }

        eapply (XA_transport am Ai A2 rho _ md tv tv (MI1 segs C _ _ _ _ HM) HXA).
        -- intros e He'. symmetry. eapply eval_agree_vals; [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]|].
           exact (am_svs_below _ am e Hamb He').
        -- intros b n Hb _. exact (HsubA _ Hb).
        -- intros z b n Hb _ Hz _. exact (rm_kept_cont Ai A2 rho rhoL rho' ms s R md _ z b n (MI1 segs C _ _ _ _ HM) HM2 Hb (HsubA _ Hb) Hz Hkept2 (fun a => call_linkP_rm _ _ _ _ _ _ _ _ _ a Hlink)).
        -- intros t2 Ht2 Hnz2. left. exists t2.
           assert (Hbt : (sv_below (ss_next Cl) (fst t2) && sv_below (ss_next Cl) (snd t2)) = true) by exact (proj1 (forallb_forall _ _) Hnb t2 Ht2).
           assert (Hag3 : agree_vals (ss_next Cl) rho (rho_patch rho' (patchf rho rho' R))) by (eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]).
           rewrite (tvv_agree (ss_next Cl) rho _ t2 Hag3 Hbt). split; [exact Ht2|]. split; [|reflexivity].
           apply (proj1 (tnz_agree (ss_next Cl) rho _ t2 Hag3 Hbt)). exact Hnz2.
    +
      destruct HJL as (A' & l1 & l2 & HM' & HbA' & HbAi & Hkept & Hinit & _).
      assert (HsubA' : forall b, In b (ma_blocks Ai) -> In b (ma_blocks A')).
      { intros b Hb. rewrite HbA'. apply in_app_mid. rewrite <- HbAi. exact Hb. }
      set (p := bv_unsigned (rw rhoL V_RES)) in *.
      set (n := bv_unsigned (rw (rho_sub (rho_absorb rho R ms) s) 12%positive)) in *.
      assert (Hn12 : bv_unsigned (rw rhoL 12%positive) = n).
      { subst n. f_equal. symmetry. apply (proj1 Hag1). reflexivity. }
      assert (Hnrho : bv_unsigned (eval rho (wsub_get s 12)) = n) by (subst n; rewrite rw_call'; reflexivity).
      assert (HinNew : In (p, n) (ma_blocks A')) by (rewrite HbA'; apply in_or_app; right; left; reflexivity).
      pose proof HM' as HMi'. unfold MInvR in HMi'.
      pose proof (minv_block_geom C A' _ _ _ p n HMi' HinNew) as (G0 & _ & G2 & G3 & G4).
      unfold PGSZ, UNIT, IB in G2, G3. pose proof (topL_range (ma_L A')) as TR3. pose proof (init_kept_top _ _ Hinit) as TK. unfold top_kept in TK.
      assert (NEWFREE : forall a, p <= a < p + n -> caddr segs C Ai None a -> False).
      { intros a Ha [Hc|[Hc|(b & m & Hb & _ & Hr)]].
        - destruct (block_addr_props segs C A' _ _ _ p n a ML HMi' HinNew Ha) as [X _]. lia.
        - destruct Hc as (Hw & _). apply (ml_wseg segs C ML) in Hw.
          rewrite Z_to_bv_unsigned, bv_wrap_small in Hw by (rewrite two64; lia).
          destruct (block_addr_props segs C A' _ _ _ p n a ML HMi' HinNew Ha) as [_ X]. exact (X Hw).
        - pose proof (MallocLaws.new_block_disjoint C A' _ _ _ l1 l2 (p, n) HMi' HbA' (b, m) ltac:(rewrite <- HbAi; exact Hb)) as D.
          unfold MallocInv.ranges_disjoint in D. cbn [fst snd] in D. lia. }
      split.
      * split.
        -- exact (KEPT_step segs C ML Ai A' rho rhoL ms s R md md' (MI1 segs C _ _ _ _ HM) HM' HRok ltac:(intros a; apply (caddr_mono segs C _ _ _ _ (init_kept_top _ _ Hinit)); exact HsubA') Hkept).
        -- intros o' oR Hin' HinR. cbn in Hin'. destruct Hin' as [<-|[]].
           destruct (obj_range rho oR) as [lo hi] eqn:HR2.
           unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi block_obj].
           rewrite soff_lit_small by lia. unfold soff. cbn [eval]. fold p.
           rewrite bv_signed_U, Hn12.
           apply ranges_disjoint_by_points. intros a Ha1 Ha2.
           apply (NEWFREE a).
           ++ destruct (Zsigned_spec n) as [[_ X]|[_ X]]; rewrite X in Ha1; lia.
           ++ apply (HRok oR a HinR). rewrite HR2. cbn [fst snd]. exact Ha2.
      * intros rho' Hlink.
        eapply TR_pre; [ | apply (Tok (rho_patch rho' (patchf rho rho' R)) ltac:(eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]))].
        intros w [Hsm' HJ']. cbn [J_ofP] in HJ'.
        destruct HJ' as (A2 & k1 & k2 & HM2 & HbA2 & HbAi2 & Hkept2 & Hinit2 & Hk2).
        assert (Hag' : agree_vals (ss_next Cl) rho rho') by (destruct Hlink as (A & _); exact A).
        assert (HsubA : forall b, In b (ma_blocks Ai) -> In b (ma_blocks A2)).
        { intros b Hb. rewrite HbA2. apply in_app_mid. rewrite <- HbAi2. exact Hb. }
        assert (E1 : rw rho' (pos_add_nat (ss_next Cl) 10) = rw rhoL V_RES).
        { destruct Hlink as (_ & _ & _ & L4).
          specialize (L4 V_RES). change (ss_next (Pre_malloc E)) with NF in L4.
          rewrite Hres in L4. cbn [eval] in L4. symmetry. apply L4; [reflexivity | cbv; lia]. }
        assert (E2 : bv_unsigned (eval rho' (wsub_get s 12)) = n).
        { rewrite <- Hnrho. f_equal. symmetry. eapply eval_agree_vals; [exact Hag' | exact Hs12]. }
        assert (Enew : tvv (rho_patch rho' (patchf rho rho' R)) (SVar (pos_add_nat (ss_next Cl) 10), wsub_get s 12) = (p, n)).
        { unfold tvv. cbn [fst snd eval]. rewrite !eval_patch. cbn [eval rho_patch rw]. rewrite E1, E2. reflexivity. }
        assert (HMi2 : MInv C A2 (rd_of segs (rm rhoL)) (wok_of segs (rm rhoL)) (m_vmmaps (cfg_model (w_cfg w)))) by exact HM2.
        split; [exact (cont_smatch segs Cl (Pre_malloc E) _ s R rho rho' tr ms md w He Hsm eq_refl Hag' Hsm')|].
        exists A2. split. { split; [|split; [exact Hk2|split; [|split; [|split; [split; [|split]|split; [|exact HP0]]]]]].
        -- eapply agree_vals_trans; [exact Hav|].
           eapply agree_vals_trans; [eapply agree_vals_le; [exact Hnf| exact Hag']| apply agree_vals_patch].
        -- eapply (MInvR_cont segs C _ ML Ai); [exact (conj HM2 (conj (init_kept_init _ _ Hinit2 (proj1 (proj2 HM))) (TPI_kept _ _ _ _ (init_kept_top _ _ Hinit2) (proj2 (proj2 HM))))) | exact HRok | intros a; apply (caddr_mono segs C _ _ _ _ (init_kept_top _ _ Hinit2)); exact HsubA | intros a; eapply call_linkP_rm; exact Hlink].
        -- intros b Hb. apply HsubA. exact (HP b Hb).
        --
           constructor.
           ++ intros _. rewrite Enew. cbn [snd]. split; [lia|]. split; [rewrite HbA2; apply in_or_app; right; left; reflexivity|].
              intros HinFB. apply (fresh_not_old C A2 _ _ _ k1 k2 p n (p, n) HMi2 HbA2 ltac:(lia)); [|reflexivity].
              rewrite <- HbAi2. exact (HP _ HinFB).
           ++ apply (tvin_agree FB A2 (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb |].
              unfold tvin in HN |- *. apply Forall_forall. intros t Ht Hnz.
              destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [apply HsubA; exact X1 | exact X2].
        --
           cbn [tvd]. split.
           ++ intros t' Ht' _ Hnz'. rewrite Enew.
              assert (Hbt : (sv_below (ss_next Cl) (fst t') && sv_below (ss_next Cl) (snd t')) = true) by exact (proj1 (forallb_forall _ _) Hnb t' Ht').
              assert (Hag'' : agree_vals (ss_next Cl) rho (rho_patch rho' (patchf rho rho' R))) by (eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]).
              rewrite (tvv_agree (ss_next Cl) rho _ t' Hag'' Hbt).
              apply (proj1 (tnz_agree (ss_next Cl) rho _ t' Hag'' Hbt)) in Hnz'.
              destruct (proj1 (Forall_forall _ _) HN t' Ht' Hnz') as (_ & X1 & _).
              intros Heq. apply (fresh_not_old C A2 _ _ _ k1 k2 p n (tvv rho t') HMi2 HbA2 ltac:(lia)); [|symmetry; exact Heq].
              rewrite <- HbAi2. exact X1.
           ++ apply (tvd_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HD].
        --
           constructor.
           ++ intros Hz. exfalso. apply Hz. unfold tnz. change (bv_unsigned (eval ?r (fst ?t))) with (fst (tvv r t)). rewrite Enew. cbn [fst]. lia.
           ++ apply (tvz_agree (ss_next Cl) rho); [eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch] | exact Hnb | exact HZ].
        -- eapply (keptF_step segs C rho0 FB ML Ai A2 rho rhoL ms s R md _ rho' HP); [intros b Hb; apply HsubA; exact (HP b Hb) | exact HM | exact HM2 | exact (init_kept_top _ _ Hinit2) | exact HRok | exact HK | exact Hkept2 | intros a; eapply call_linkP_rm; exact Hlink]. }

        assert (Hag3 : agree_vals (ss_next Cl) rho (rho_patch rho' (patchf rho rho' R))) by (eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]).
        eapply (XA_transport am Ai A2 rho _ md tv _ (MI1 segs C _ _ _ _ HM) HXA).
        -- intros e He'. symmetry. eapply eval_agree_vals; [exact Hag3|].
           exact (am_svs_below _ am e Hamb He').
        -- intros b n' Hb _. exact (HsubA _ Hb).
        -- intros z b n' Hb _ Hz _. exact (rm_kept_cont Ai A2 rho rhoL rho' ms s R md _ z b n' (MI1 segs C _ _ _ _ HM) HM2 Hb (HsubA _ Hb) Hz Hkept2 (fun a => call_linkP_rm _ _ _ _ _ _ _ _ _ a Hlink)).
        -- intros t2 [<-|Ht2] Hnz2.
           ++ right. intros bn Hbn Heq. rewrite Enew in Heq. subst bn.
              apply (fresh_not_old C A2 _ _ _ k1 k2 p n (p, n) HMi2 HbA2 ltac:(lia)); [|reflexivity]. rewrite <- HbAi2. exact Hbn.
           ++ left. exists t2.
              assert (Hbt : (sv_below (ss_next Cl) (fst t2) && sv_below (ss_next Cl) (snd t2)) = true) by exact (proj1 (forallb_forall _ _) Hnb t2 Ht2).
              rewrite (tvv_agree (ss_next Cl) rho _ t2 Hag3 Hbt). split; [exact Ht2|]. split; [|reflexivity].
              apply (proj1 (tnz_agree (ss_next Cl) rho _ t2 Hag3 Hbt)). exact Hnz2.
Qed.

Theorem free_callAT : ltac2:(tb__ "0|7|
S1Sb0S41S4A1M0S2S41S3fS0S0A2M1A1S51S4cG1Sa8SacS2VTR;S5dVsegs;Se7Vsegs;VC;R2VKc;A4Se4VE;A1M2R1A4S90Vsegs;S10aR1S45S3fS1S8fA2M3S42S1S8fSe3VE;A1M4Se5Vsegs;VC;R2VKc;A4A4S4bG3A1A3A4A2Frho1;FAi;S36S43G0A1SefRaG2R9A3S46G0R8A2A3S36S3eSbdVC;VNP;RbG2RaR9S45S1G4S4bS1A1A3A7S40A3S36S3eSebVNP;S3RcA1A2S40A3S36S3eSb8S3RdA1R9A2S40A3S36S3eS52S3ReA1R9A2S40A3S36S43G1A1S66G1RbR9A3S46G1R8A2A3SacS8dS6ScReA1S5R11A1A3VP0f;Vrho0;A1S8eVNP;Vrho0;R10A3SbcVFB;R4A2SbeVFB;R5R12R11A4Sc1R13R12A2Sc2R14R13A2S6eR13R8R15R14A4S38S2S2S38S6aS6aSdcVsegs;VC;RbR2R1A5Lmd;A2LrhoM;A2SbfR17Sf7SaeRaA1A1A2S37Sb9R18R14A2S37S36S3fS33S33A2SbaR18R14A2S42S33S33Sb6Q40M5SbR18SafR1aPcA2A2A2M6Sb6G5SbR18SafR1aPdA2A2A2A4A3Sc7Vsegs;VC;RbS46S33G6A2R18R19A6A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S2S8eS3R12A1RfR1A3VTR;S5dVsegs;S6cSc6G1RdRfA3ReA2SbbR13R12R11G4A4R2A4RbA2F_;Frho';VTR;S5dVsegs;S6cReRdA2R12RfA4RaA2F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ft;Fi;Fam;Ftv;Frho;FR;Fs;FCl;").
Proof using ML TR_callP TR_ex TR_facts TR_pre.
  intros Cl s R rho tv am i t Q CALLEE He Hchk Hnf Hnb Hamb Hnth HR Tfree.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex MA (JGAi tv am)). intros Ai.
  eapply (TR_callP (JGAi tv am Ai) (J_free_pre segs C Ai Kc) Cl (Pre_free E) s R
            [(L_free E, JL_free segs C Ai Kc)] Q rho He).
  - exact (call_checkT_P _ _ _ _ _ _ _ Hchk).
  - intros rho1. apply CALLEE.
  -
    intros tr ms md Hsm [(Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0) HXA].
    destruct (HR Ai HF HP0 Hav HP HN HD HZ HXA (ex_intro _ rho (ex_intro _ md (MI1 segs C _ _ _ _ HM))) ltac:(eapply T_of_chk; [exact Hav | exact (proj2 (proj2 HM)) | exact Hchk])) as (Hnz & Ht & HRok).
    destruct (proj1 (Forall_forall _ _) HN t (nth_error_In _ _ Hnth) Hnz) as (Tpos & Tin & Tfb).
    split; [|split; [|split; [exact Hk | split; [exact (tp_of_TPI _ _ _ _ _ _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk) | split; [exact (proj1 (proj2 HM)) | exact (top_of_TPI _ _ _ _ _ _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk)]]]]].
    + eapply MI1. eapply (MInvR_mem segs C _ ML); [exact HM| |reflexivity]. intros a Ha Ho. apply rm_absorb_out.
      exact (R_miss segs C ML Ai (Some _) rho rho md R a (MI1 segs C _ _ _ _ HM) HRok Ha Ho).
    + rewrite !rw_call'. rewrite <- Ht. exact Tin.
  -
    intros L JL tr ms md rhoL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    destruct HJ as [(Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0) HXA].
    destruct (HR Ai HF HP0 Hav HP HN HD HZ HXA (ex_intro _ rho (ex_intro _ md (MI1 segs C _ _ _ _ HM))) ltac:(eapply T_of_chk; [exact Hav | exact (proj2 (proj2 HM)) | exact Hchk])) as (Hnz & Ht & HRok).
    destruct (proj1 (Forall_forall _ _) HN t (nth_error_In _ _ Hnth) Hnz) as (Tpos & Tin & Tfb).
    cbn [In] in HinL. destruct HinL as [HinL|[]]. injection HinL as HL HJLe. subst L JL.
    destruct HJL as (A' & l1 & l2 & HM' & HbAi & HbA' & Hkept & Hinit & _).
    rewrite !rw_call' in HbAi.
    set (x := bv_unsigned (eval rho (wsub_get s 12))) in *.
    set (m := bv_unsigned (eval rho (wsub_get s 13))) in *.
    assert (SUB : forall A2 k1 k2, ma_blocks Ai = k1 ++ (x, m) :: k2 -> ma_blocks A2 = k1 ++ k2 ->
                 forall bn, In bn (ma_blocks Ai) -> bn <> (x, m) -> In bn (ma_blocks A2)).
    { intros A2 k1 k2 E1 E2 bn Hb Hbx. rewrite E2. rewrite E1 in Hb.
      apply in_mid_cases in Hb as [Hb|Hb]; [|exact Hb]. exfalso. exact (Hbx Hb). }
    assert (CADDR : forall A2, top_kept Ai A2 -> (forall bn, In bn (ma_blocks Ai) -> bn <> (x, m) -> In bn (ma_blocks A2)) ->
                   forall a, caddr segs C Ai (Some x) a -> caddr segs C A2 None a).
    { intros A2 HTK HS a [H|[H|(b & n & Hb & Hbx & Hr)]]; [left; unfold top_kept in HTK; rewrite HTK; exact H | right; left; exact H | right; right].
      exists b, n. split; [apply HS; [exact Hb | intros Heq; apply Hbx; injection Heq as -> ->; reflexivity]|].
      split; [discriminate | exact Hr]. }
    assert (FB2 : forall A2, (forall bn, In bn (ma_blocks Ai) -> bn <> (x, m) -> In bn (ma_blocks A2)) ->
                 forall bn, In bn FB -> In bn (ma_blocks A2)).
    { intros A2 HS bn Hbn. apply HS; [exact (HP _ Hbn)|]. intros ->. rewrite <- Ht in Hbn. exact (Tfb Hbn). }
    pose proof (SUB A' l1 l2 HbAi HbA') as HsubA'.
    split.
    + split.
      * intros a Hina.
        apply (robjs_in_ranges segs C Ai (Some x) rho R) in Hina; [|exact HRok].
        rewrite <- (Z_to_bv_bv_unsigned 64 a).
        pose proof (bv_urange a) as Ha.
        destruct (caddr_props segs C Ai (Some x) _ rho md ML (MI1 segs C _ _ _ _ HM) Ha Hina) as (O1 & O2 & O3).
        destruct (caddr_props segs C A' None _ rhoL md' ML HM' Ha (CADDR A' (init_kept_top _ _ Hinit) HsubA' _ Hina)) as (O1' & _).
        apply Hkept; try assumption; [exact (caddr_client segs C _ _ _ Hina) | exact (caddr_client segs C _ _ _ (CADDR A' (init_kept_top _ _ Hinit) HsubA' _ Hina)) |]. intros Hs. apply O3. apply (static_alloc_static C). exact Hs.
      * intros o' oR Hin' _. cbn in Hin'. destruct Hin'.
    + intros rho' Hlink.
      eapply TR_pre; [ | apply (Tfree (rho_patch rho' (patchf rho rho' R)) ltac:(eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]))].
      intros w [Hsm' HJ']. cbn [J_ofP] in HJ'.
      destruct HJ' as (A2 & k1 & k2 & HM2 & HbAi2 & HbA2 & Hkept2 & Hinit2 & Hk2).
      rewrite !rw_call' in HbAi2. fold x in HbAi2. fold m in HbAi2.
      pose proof (SUB A2 k1 k2 HbAi2 HbA2) as HsubA2.
      assert (Hag' : agree_vals (ss_next Cl) rho rho') by (destruct Hlink as (A & _); exact A).
      assert (Hag'' : agree_vals (ss_next Cl) rho (rho_patch rho' (patchf rho rho' R))) by (eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]).
      split; [exact (cont_smatch segs Cl (Pre_free E) _ s R rho rho' tr ms md w He Hsm eq_refl Hag' Hsm')|].
      exists A2. split. { split; [|split; [exact Hk2|split; [|split; [|split; [split; [|split]|split; [|exact HP0]]]]]].
      * eapply agree_vals_trans; [exact Hav|].
        eapply agree_vals_trans; [eapply agree_vals_le; [exact Hnf| exact Hag']| apply agree_vals_patch].
      * eapply (MInvR_mem segs C _ ML); [exact (conj HM2 (conj (init_kept_init _ _ Hinit2 (proj1 (proj2 HM))) (TPI_kept _ _ _ _ (init_kept_top _ _ Hinit2) (proj2 (proj2 HM)))))| |reflexivity]. intros a Ha Ho. cbn [rho_patch rm]. unfold patchf.
        destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi|Hn'].
        -- exfalso. eapply (R_miss segs C ML A2 None rho rhoL _ R a); [exact HM2 | | exact Ha | exact Ho | exact Hi].
           intros o b Ho' Hr'. apply (CADDR A2 (init_kept_top _ _ Hinit2) HsubA2). exact (HRok o b Ho' Hr').
        -- eapply call_linkP_rm. exact Hlink.
      * exact (FB2 A2 HsubA2).
      * apply (tvin_agree FB A2 (ss_next Cl) rho); [exact Hag'' | |].
        { unfold tv_below in *. apply forallb_forall. intros t' Ht'. apply (proj1 (forallb_forall _ _) Hnb). eapply remove_nth_In. exact Ht'. }
        unfold tvin in HN |- *. apply Forall_forall. intros t' Ht' Hnz'.
        destruct (proj1 (Forall_forall _ _) HN t' (remove_nth_In _ _ _ Ht') Hnz') as (X0 & X1 & X2).
        split; [exact X0|]. split; [|exact X2]. apply HsubA2; [exact X1|].
        rewrite <- Ht. exact (tvd_nth_distinct rho tv i t t' HD Hnth Ht' Hnz Hnz').
      * apply (tvd_agree (ss_next Cl) rho); [exact Hag'' | | apply tvd_remove; exact HD].
        unfold tv_below in *. apply forallb_forall. intros t' Ht'. apply (proj1 (forallb_forall _ _) Hnb). eapply remove_nth_In. exact Ht'.
      * apply (tvz_agree (ss_next Cl) rho); [exact Hag'' | |].
        { unfold tv_below in *. apply forallb_forall. intros t' Ht'. apply (proj1 (forallb_forall _ _) Hnb). eapply remove_nth_In. exact Ht'. }
        unfold tvz in HZ |- *. apply Forall_forall. intros t' Ht'. apply (proj1 (Forall_forall _ _) HZ). eapply remove_nth_In. exact Ht'.
      * intros a Ha Hp. cbn [rho_patch rm]. unfold patchf.
        destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi|Hn']; [apply HK; assumption|].
        rewrite (call_linkP_rm _ _ _ _ _ _ _ _ _ _ Hlink).
        pose proof (pclF_caddr segs C rho0 FB Ai a HP (proj2 (proj2 HM)) Hp) as Hc.
        destruct (caddr_props segs C Ai None a rho md ML (MI1 segs C _ _ _ _ HM) Ha Hc) as (O1 & O2 & O3).
        destruct (caddr_props segs C A2 None a rhoL _ ML HM2 Ha (pclF_caddr segs C rho0 FB A2 a (FB2 A2 HsubA2) (TPI_kept _ _ _ _ (init_kept_top _ _ Hinit2) (proj2 (proj2 HM))) Hp)) as (O1' & _).
        transitivity (rm (rho_sub (rho_absorb rho R ms) s) (Z_to_bv 64 a)).
        -- apply Hkept2; try assumption; [exact (caddr_client segs C _ _ _ Hc) | exact (caddr_client segs C _ _ _ (pclF_caddr segs C rho0 FB A2 a (FB2 A2 HsubA2) (TPI_kept _ _ _ _ (init_kept_top _ _ Hinit2) (proj2 (proj2 HM))) Hp)) |]. intros Hs. apply O3. apply (static_alloc_static C). exact Hs.
        -- rewrite rm_absorb_out by exact Hn'. apply HK; assumption. }

      eapply (XA_transport am Ai A2 rho _ md tv _ (MI1 segs C _ _ _ _ HM) HXA).
      * intros e He'. symmetry. eapply eval_agree_vals; [exact Hag''|].
        exact (am_svs_below _ am e Hamb He').
      * intros b n Hb Hut. apply HsubA2; [exact Hb|]. rewrite <- Ht. intros Heq. exact (Hut t (nth_error_In _ _ Hnth) Hnz (eq_sym Heq)).
      * intros z b n Hb Hut Hz _.
        assert (Hb2 : In (b, n) (ma_blocks A2)).
        { apply HsubA2; [exact Hb|]. rewrite <- Ht. intros Heq. exact (Hut t (nth_error_In _ _ Hnth) Hnz (eq_sym Heq)). }
        exact (rm_kept_cont Ai A2 rho rhoL rho' ms s R md _ z b n (MI1 segs C _ _ _ _ HM) HM2 Hb Hb2 Hz Hkept2 (fun a => call_linkP_rm _ _ _ _ _ _ _ _ _ a Hlink)).
      * intros t2 Ht2 Hnz2. left. exists t2. pose proof (remove_nth_In _ _ _ Ht2) as Ht2'.
        assert (Hbt : (sv_below (ss_next Cl) (fst t2) && sv_below (ss_next Cl) (snd t2)) = true) by exact (proj1 (forallb_forall _ _) Hnb t2 Ht2').
        rewrite (tvv_agree (ss_next Cl) rho _ t2 Hag'' Hbt). split; [exact Ht2'|]. split; [|reflexivity].
        apply (proj1 (tnz_agree (ss_next Cl) rho _ t2 Hag'' Hbt)). exact Hnz2.
Qed.

Theorem pure_callAT : ltac2:(tb__ "0|3|
S1S1Sb0S41S4A1M0S41Sf1A1S2S41S3fS0S0A2A1S51Sa8S2VTR;S61Vsegs;S41S6bA1S6aS6cR6R5R7R2R1A5Lmd;Ltr;M1R9R1A4S60Vsegs;G1S3R9A1R1R6A5A2Frho1;S36S43G0A1SefRaR9R8A3S46G0R7A2A3S36S3eS94RbRaR9R8R7A5S40A3S36S3eSebVNP;S3RcA1A2S40A3S36S3eSb8S3RdA1R7A2S40A3S36S3eS52S3ReA1R7A2S40A3S36S3eS67S6S27S3RfA1A1S5RfA1A3S40A3Sf1S2S65Sf1R2ReA3S11S3R13A1M2ReR2A3VTR;S5dVsegs;S6cReRdA2S101S5R14A1S93R12G2Sf3R4A1S3R14A1R11A5A2R3A4RcA2F_;F_;Frho';FL;VTR;S5dVsegs;S6cRbRaA2R11RcA4R9A2F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Ftv;Frho;FPosts;FR;Fs;FPre;FCl;").
Proof using ML TR_callJ TR_facts TR_pre.
  intros Cl Pre s R Posts rho tv am Q Hsum He Hchk Hnf Hnb Hamb Hfb Hcont. apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_callJ (JGA tv am) (liftK (fun tr md => JGA tv am rho tr md)) (liftK (fun tr md => JGA tv am rho tr md))
           (JGA tv am) Cl Pre s R Posts Q rho He Hchk).
  - intros rho1. apply Hsum.
  - intros tr ms md Hsm HJ. exact HJ.
  - intros L rho' rhoL tr ms md tr' md' HinL Hsm HJ HLK HJ'. cbn [liftK] in HJ'.
    eapply (stableJ_JGA (ss_next Cl) tv am Hnf Hnb Hamb); [exact (proj1 HLK) | exact HJ'].
  - intros L rho' HinL Hag. eapply TR_pre; [ | apply (Hcont L rho' HinL Hag)].
    intros w [Hsm' HJ']. split; [|exact HJ'].
    apply smatch_add_facts; [exact Hsm' | |].
    + apply Forall_forall. intros q Hq.
      apply (holds_agree_vals (ss_next Cl) rho rho' q (agree_below_vals _ _ _ Hag)).
      * exact (proj1 (forallb_forall _ _) Hfb q Hq).
      * exact (proj1 (Forall_forall _ _) HF q Hq).
    + apply forallb_forall. intros q Hq.
      eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) Hfb q Hq)].
      unfold import_post. cbn [ss_next set_objs subst_state]. unfold import_next, pos_add_nat. lia.
Qed.

End CallT.

Ltac by_A_safety ok lem :=
  apply (lem (triple segs ok) (TRs_facts segs ok) (TRs_ex segs ok) (TRs_pre segs ok) (call_soundP segs ok)).
Ltac by_A_ex lem :=
  apply (lem (etriple segs) (TRe_facts segs) (TRe_ex segs) (TRe_pre segs) (call_completeP segs)).

Theorem malloc_callA : ltac2:(tb__ "0|9|
Sa9OF_;S1Sb0S41S4A1M0S2S41S3fS0S0A2M1A1S51Sa8Se1Vsegs;R8VKc;A3Sc9Vsegs;VC;VE;A3S36S43G0A1SefR9SdfVE;A1M2R8A3S46G0R7A2A3S36S3eSbdVC;VNP;RaG2R9R8S45S1SddVE;A1M3S45S1SdeVE;A1M4S4bS1A1A3A3A7S40A3S36S3eSebVNP;S3RbA1A2S40A3S36S3eSb8S3RcA1R8A2S40A3S36S3eS52S3RdA1R8A2S40A3S36S3eSdS3ReA1SafRdPcM5A2A2S40A3S36S0SafS92ReS10aG4S3RfA1M6A4Se0A2S9S91G6UaM7A2A1A3SacS8dS6ScReA1S5R11A1A3VP0f;Vrho0;A1S8eVNP;Vrho0;R10A3SbcVFB;R4A2SbeVFB;R5R12R11A4Sc1R13R12A2Sc2R14R13A2S6eR13R8R15R14A4S38S2S2S38S6aS6aSdcVsegs;VC;RbR2R1A5Lmd;A2LrhoM;A2SbfR17Sf7SaeRaA1A1A2S37Sc7Vsegs;VC;RbS4dS33A1R18R19A6S9fZ0Sb6Q40SbR18SafR1aG5A2A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S2S8eS3R12A1RfR1A3SaaVsegs;R14S5dVsegs;S6cRfReA2M8SbbR13R12R11G3A4R2A4RdA4F_;Frho';S2S8eS3R13A1R10R1A3SaaVsegs;R15S5dVsegs;S6cS45G1S42S0S0S9S91S3R14A1G7A2A1SafR13G5A2A4R10A3RfA2SbbR14R13R12G4A4R2A4ReA4F_;Frho';SaaVsegs;R14S5dVsegs;G8R13R10A4RdA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Ftv;Frho;FR;Fs;FCl;Fok;").
Proof using ML.
  intros ok Cl s R rho tv am Q Hok MC. by_A_safety ok malloc_callAT.
  intros Ai rho1. apply (mc_malloc segs C E MC). exact Hok.
Qed.

Theorem malloc_callA_ex : ltac2:(tb__ "0|9|
S1Sb0S41S4A1M0S2S41S3fS0S0A2M1A1S51Sa8Se2VKc;A1ScaVsegs;VC;VE;A3S36S43G0A1SefR9SdfVE;A1M2R8A3S46G0R7A2A3S36S3eSbdVC;VNP;RaG2R9R8S45S1SddVE;A1M3S45S1SdeVE;A1M4S4bS1A1A3A3A7S40A3S36S3eSebVNP;S3RbA1A2S40A3S36S3eSb8S3RcA1R8A2S40A3S36S3eS52S3RdA1R8A2S40A3S36S3eSdS3ReA1SafRdPcM5A2A2S40A3S36S0SafS92ReS10aG4S3RfA1M6A4Se0A2S9S91G6UaM7A2A1A3SacS8dS6ScReA1S5R11A1A3VP0f;Vrho0;A1S8eVNP;Vrho0;R10A3SbcVFB;R4A2SbeVFB;R5R12R11A4Sc1R13R12A2Sc2R14R13A2S6eR13R8R15R14A4S38S2S2S38S6aS6aSdcVsegs;VC;RbR2R1A5Lmd;A2LrhoM;A2SbfR17Sf7SaeRaA1A1A2S37Sc7Vsegs;VC;RbS4dS33A1R18R19A6S9fZ0Sb6Q40SbR18SafR1aG5A2A2A2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S2S8eS3R12A1RfR1A3SabVsegs;S5dVsegs;S6cRfReA2M8SbbR13R12R11G3A4R2A4RdA3F_;Frho';S2S8eS3R13A1R10R1A3SabVsegs;S5dVsegs;S6cS45G1S42S0S0S9S91S3R14A1G7A2A1SafR13G5A2A4R10A3RfA2SbbR14R13R12G4A4R2A4ReA3F_;Frho';SabVsegs;S5dVsegs;G8R13R10A4RdA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Ftv;Frho;FR;Fs;FCl;").
Proof using ML.
  intros Cl s R rho tv am Q Hvi MCX. by_A_ex malloc_callAT.
  intros Ai rho1. apply (mcx_malloc segs C E MCX). exact Hvi.
Qed.

Theorem free_callA : ltac2:(tb__ "0|6|
Sa9OF_;S1Sb0S41S4A1M0S2S41S3fS0S0A2M1A1S51S4cG1Sa8Se1Vsegs;RaVKc;A3Sc9Vsegs;VC;VE;A3S36S43G0A1SefRbSe4VE;A1M2RaA3S46G0R9A2A3S36S3eSbdVC;VNP;RcG2RbRaS45S1Se3VE;A1M3S4bS1A1A3A7S40A3S36S3eSebVNP;S3RdA1A2S40A3S36S3eSb8S3ReA1RaA2S40A3S36S3eS52S3RfA1RaA2S40A3S36S43G1A1S66G1RcRaA3S46G1R9A2A3SacS8dS6ScRfA1S5R12A1A3VP0f;Vrho0;A1S8eVNP;Vrho0;R11A3SbcVFB;R4A2SbeVFB;R5R13R12A4Sc1R14R13A2Sc2R15R14A2S6eR14R8R16R15A4S38S2S2S38S6aS6aSdcVsegs;VC;RbR2R1A5Lmd;A2LrhoM;A2SbfR18Sf7SaeRaA1A1A2S37Sb9R19R15A2S37S36S3fS33S33A2SbaR19R15A2S42S33S33Sb6Q40M4SbR19SafR1bPcA2A2A2M5Sb6G4SbR19SafR1bPdA2A2A2A4A3Sc7Vsegs;VC;RbS46S33G5A2R19R1aA6A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S2S8eS3R13A1R10R1A3SaaVsegs;R15S5dVsegs;S6cSc6G1ReR10A3RfA2SbbR14R13R12G3A4R2A4RcA4F_;Frho';SaaVsegs;R14S5dVsegs;S6cRfReA2R13R10A4RbA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ft;Fi;Fam;Ftv;Frho;FR;Fs;FCl;Fok;").
Proof using ML.
  intros ok Cl s R rho tv am i t Q Hok MC. by_A_safety ok free_callAT.
  intros Ai rho1. apply (mc_free segs C E MC). exact Hok.
Qed.

Theorem free_callA_ex : ltac2:(tb__ "0|6|
S1Sb0S41S4A1M0S2S41S3fS0S0A2M1A1S51S4cG1Sa8Se2VKc;A1ScaVsegs;VC;VE;A3S36S43G0A1SefRbSe4VE;A1M2RaA3S46G0R9A2A3S36S3eSbdVC;VNP;RcG2RbRaS45S1Se3VE;A1M3S4bS1A1A3A7S40A3S36S3eSebVNP;S3RdA1A2S40A3S36S3eSb8S3ReA1RaA2S40A3S36S3eS52S3RfA1RaA2S40A3S36S43G1A1S66G1RcRaA3S46G1R9A2A3SacS8dS6ScRfA1S5R12A1A3VP0f;Vrho0;A1S8eVNP;Vrho0;R11A3SbcVFB;R4A2SbeVFB;R5R13R12A4Sc1R14R13A2Sc2R15R14A2S6eR14R8R16R15A4S38S2S2S38S6aS6aSdcVsegs;VC;RbR2R1A5Lmd;A2LrhoM;A2SbfR18Sf7SaeRaA1A1A2S37Sb9R19R15A2S37S36S3fS33S33A2SbaR19R15A2S42S33S33Sb6Q40M4SbR19SafR1bPcA2A2A2M5Sb6G4SbR19SafR1bPdA2A2A2A4A3Sc7Vsegs;VC;RbS46S33G5A2R19R1aA6A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FAi;S2S8eS3R13A1R10R1A3SabVsegs;S5dVsegs;S6cSc6G1ReR10A3RfA2SbbR14R13R12G3A4R2A4RcA3F_;Frho';SabVsegs;S5dVsegs;S6cRfReA2R13R10A4RbA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ft;Fi;Fam;Ftv;Frho;FR;Fs;FCl;").
Proof using ML.
  intros Cl s R rho tv am i t Q Hvi MCX. by_A_ex free_callAT.
  intros Ai rho1. apply (mcx_free segs C E MCX). exact Hvi.
Qed.

Theorem pure_callA : ltac2:(tb__ "0|2|
Sa9OF_;S1S1Sb0S41S4A1M0S41Sf1A1S2S41S3fS0S0A2A1S51Sa8S41S6bA1S6aOF_;F_;S2S5fVsegs;RcR2A3SaaVsegs;RdS61Vsegs;R3RbR2A4S60Vsegs;R3S3RbA1R2R8A5A4F_;Frho1;FK;S5fVsegs;RbVKc;A3S36S43G0A1SefRbRaR9A3S46G0R8A2A3S36S3eS94RcRbRaR9R8A5S40A3S36S3eSebVNP;S3RdA1A2S40A3S36S3eSb8S3ReA1R8A2S40A3S36S3eS52S3RfA1R8A2S40A3S36S3eS67S6S27S3R10A1A1S5R10A1A3S40A3Sf1S2S65Sf1R2RfA3S11S3R14A1M1RfR2A3SaaVsegs;R16S5dVsegs;S6cRfReA2S101S5R15A1S93R13G1Sf3R4A1S3R15A1R12A5A2R3A4RdA4F_;F_;Frho';FL;SaaVsegs;R13S5dVsegs;S6cRcRbA2R12RdA4RaA4F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Ftv;Frho;FPosts;FR;Fs;FPre;FCl;Fok;").
Proof using ML.
  intros ok Cl Pre s R Posts rho tv am Q Hsum Hok.
  apply (pure_callAT (triple segs ok) (TRs_facts segs ok) (TRs_pre segs ok) (call_soundJ segs ok)).
  intros rho1. apply (Hsum (fun tr md => JGA tv am rho tr md) rho1).
  eapply ok_frame_imp; [|exact Hok]. intros tr md (Ai & (_ & Hk & _) & _). exact Hk.
Qed.

Theorem pure_callA_ex : ltac2:(tb__ "0|2|
S1S1Sb0S41S4A1M0S41Sf1A1S2S41S3fS0S0A2A1S51Sa8S41S6bA1S6aOF_;F_;S2SabVsegs;S61Vsegs;R2RaR1A4S60Vsegs;R2S3RaA1R1R7A5A3Frho1;FK;S36S43G0A1SefRaR9R8A3S46G0R7A2A3S36S3eS94RbRaR9R8R7A5S40A3S36S3eSebVNP;S3RcA1A2S40A3S36S3eSb8S3RdA1R7A2S40A3S36S3eS52S3ReA1R7A2S40A3S36S3eS67S6S27S3RfA1A1S5RfA1A3S40A3Sf1S2S65Sf1R2ReA3S11S3R13A1M1ReR2A3SabVsegs;S5dVsegs;S6cReRdA2S101S5R14A1S93R12G1Sf3R4A1S3R14A1R11A5A2R3A4RcA3F_;F_;Frho';FL;SabVsegs;S5dVsegs;S6cRbRaA2R11RcA4R9A3F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Ftv;Frho;FPosts;FR;Fs;FPre;FCl;").
Proof using ML.
  intros Cl Pre s R Posts rho tv am Q Hsum.
  apply (pure_callAT (etriple segs) (TRe_facts segs) (TRe_pre segs) (call_completeJ segs)).
  intros rho1. apply Hsum.
Qed.

Definition slot_obj (o : sobj) (ps : sv * sv) : bool := ltac2:(tb__ "0|1|
S3eS3eL_;M0S7S13Vo;A1S44S0S0Vps;A3A2G0S7S16Vo;A1S8Z0A1A2S7S15Vo;A1S48S0S0Vps;A3A2S49X3ex2S49X3ex2").
Definition hdr_obj (am : amode) (o : sobj) : bool := ltac2:(tb__ "0|2|
S51S3eLam;Vam;S49S0S49Lhd;S0S0S0S41S3fS0S0A2M0A1S3eS3eL_;M1G1S7S13Vo;A1R4A2G1S7S16Vo;A1S8Z0A1A2S7S15Vo;A1S8Z18A1A2S49X3ex2S49X3ex2S40S68G0S8bVo;A1R1A3X3ex2Lsl;Lcap;Lnx;Lhd;S0S0S49Lg;Lhd;X51x4").

Lemma hdr_obj_range : ltac2:(tb__ "0|3|
S0S0S0S41S3fS0S0A2A1M0SacS2G0S4S33S6eS54R9R8R7R6A4R5R4R3A4S36S3eS70S54RaR9R8R7A4R3A2S40A3S37S9dS44S33S33SeR6R4A2M1A3R3A2S9fR3S48S33S33G1A3A2A2S37S9dVUv;R7RcA2M2R4A2S9fR4S9eS9eG2S113A2VUv;R7RaA2A2A2A2F_;F_;F_;Fa;Fo;Ftv;Frho;FAi;Fsl;Fcap;Fnx;Fhd;").
Proof using .
  clear_sec. intros hd nx cap sl Ai rho tv o a HX Ho Hr. cbn -[existsb slot_obj] in Ho.
  cbn in HX. destruct HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & _).
  apply lazy_orb_prop in Ho as [Ho|Ho].
  - apply lazy_andb_prop in Ho as [Hb Ho]. apply lazy_andb_prop in Ho as [Hl Hh].
    apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
    unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr. cbn [fst snd] in Hr.
    rewrite !soff_lit_small in Hr by lia. unfold Uv, HDR in *. lia.
  - apply existsb_exists in Ho as (ps & Hps & Ho). unfold slot_obj in Ho.
    apply lazy_andb_prop in Ho as [Hb Ho]. apply lazy_andb_prop in Ho as [Hl Hh].
    apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
    pose proof (proj1 (Forall_forall _ _) X7 ps Hps) as Y. cbv beta in Y.
    unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Hb, Hl, Hh in Hr. cbn [fst snd] in Hr.
    rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite bv_signed_U in Hr.
    unfold Uv, HDR in *. destruct (Zsigned_spec (bv_unsigned (eval rho (snd ps)))) as [[_ E1]|[_ E1]]; rewrite E1 in Hr; lia.
Qed.

Lemma hdr_obj_caddr : ltac2:(tb__ "0|1|
S51SacS2S41S3fS0S0A2A1S4S33S6eR6R5R4R3A4S36S3eS70R7R3A2S40A3S37S9dS44S33S33SeR6R4A2M0A3R3A2S9fR3S48S33S33G0A3A2A2SccVsegs;VC;R8S4dS33A1R4A5F_;F_;F_;Fa;Fo;Ftv;Frho;FAi;Fam;").
Proof using .
  clear_sec. intros am Ai rho tv o a HX Ho Hr. destruct am as [|hd|hd nx cap sl|hd0 g0]; [discriminate|discriminate| |discriminate].
  pose proof (hdr_obj_range hd nx cap sl Ai rho tv o a HX Ho Hr) as R.
  cbn in HX. destruct HX as (X1 & X2 & X3 & _). right; right.
  exists (Uv rho hd), (HDR + Uv rho cap). split; [exact X3|]. split; [discriminate|]. lia.
Qed.

Lemma hdr_obj_caddr_free : ltac2:(tb__ "0|2|
S51SacS2S41S3fS0S0A2M0A1S4S33G0S2S6aSdcVsegs;VC;R8R2R1A5SbeVFB;R9R8R7A4S65G0R5R8A3Sb9RaR6A2S6eRdRcRbRaA4S36S3eS70ReRaA2S40A3S37S9dS44S33S33SeRdRbA2M1A3RaA2S9fRaS48S33S33G1A3A2A2SccVsegs;VC;RfS46S33S44S33S33SbaReRaA2A3A2RbA5F_;F_;F_;F_;F_;F_;F_;Fmd;FrhoM;Ft;Fa;Fo;Ftv;Frho;FAi;Fam;").
Proof using .
  clear - ML HNP. intros am Ai rho tv o a t rhoM md HM HN Ht Hnz HX Ho Hr. destruct am as [|hd|hd nx cap sl|hd0 g0]; [discriminate|discriminate| |discriminate].
  pose proof (hdr_obj_range hd nx cap sl Ai rho tv o a HX Ho Hr) as R.
  cbn in HX. destruct HX as (X1 & X2 & X3 & X4 & X5 & _). right; right.
  exists (Uv rho hd), (HDR + Uv rho cap). split; [exact X3|]. split; [|lia].
  intros Heq. injection Heq as Heq.
  destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (Tpos & Tin & _).
  apply (blocks_bases_differ segs C Ai rhoM md (fst (tvv rho t)) (snd (tvv rho t)) (Uv rho hd) (HDR + Uv rho cap) HM).
  - rewrite <- surjective_pairing. exact Tin.
  - exact X3.
  - rewrite <- surjective_pairing. exact (X5 t Ht Hnz).
  - exact Tpos.
  - unfold HDR. lia.
  - exact Heq.
Qed.

Theorem malloc_site_autoA : ltac2:(tb__ "0|9|
Sa9OF_;S1Sb0S41S4A1M0S2S41S3fS0S0A2M1A1S51Sa8Se1Vsegs;R8VKc;A3Sc9Vsegs;VC;VE;A3S36S43G0A1SefR9SdfVE;A1M2R8A3S46G0R7A2A3S36S3eSbdVC;VNP;RaG2R9R8S45S1SddVE;A1M3S45S1SdeVE;A1M4S4bS1A1A3A3A7S40A3S36S3eSebVNP;S3RbA1A2S40A3S36S3eSb8S3RcA1R8A2S40A3S36S3eS52S3RdA1R8A2S40A3S36S3eSdS3ReA1SafRdPcM5A2A2S40A3S36S0SafS92ReS10aG4S3RfA1M6A4Se0A2S9S91G6UaM7A2A1A3S36S3eSc5S5R10A1RcS4dS4cA1S70RbA1ReA5S40A3S36S3eSf2S5R11A1S8Z1A1Z0SafR10G5A2A4S40A3S2S8eS3R13A1R10R1A3SaaVsegs;R15S5dVsegs;S6cR10RfA2M8SbbR14R13R12G3A4R2A4ReA4F_;Frho';S2S8eS3R14A1R11R1A3SaaVsegs;R16S5dVsegs;S6cS45G1S42S0S0S9S91S3R15A1G7A2A1SafR14G5A2A4R11A3R10A2SbbR15R14R13G4A4R2A4RfA4F_;Frho';SaaVsegs;R15S5dVsegs;G8R14R11A4ReA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Ftv;Frho;FR;Fs;FCl;Fok;").
Proof using ML.
  intros ok Cl s R rho tv am Q Hok MC He Hchk Hnf Hnb Hamb Hs12 Hres Hrc Hpos Tnull Tok.
  apply (malloc_callA ok Cl s R rho tv am Q Hok MC He Hchk Hnf Hnb Hamb Hs12 Hres); [|exact Tnull|exact Tok].
  intros Ai HF HP0 Hav HP HN HD HZ HXA (rhoM & md & HM) HT. split.
  - eapply (robjs_check_sound segs C FB Ai rho (ss_facts Cl) tv None (hdr_obj am) R None rhoM md HM HT HF HN HD HZ Hrc); [|exact I].
    intros o a Ho Hx Hr. exact (hdr_obj_caddr am Ai rho tv o a HXA Hx Hr).
  - pose proof (uleq_sound rho (ss_facts Cl) _ 0 _ HF Hpos) as U1. unfold U in U1. rewrite U_lit in U1.
    unfold M64v in U1. rewrite Z.mod_small in U1 by lia. lia.
Qed.

Theorem malloc_site_autoA_ex : ltac2:(tb__ "0|9|
S1Sb0S41S4A1M0S2S41S3fS0S0A2M1A1S51Sa8Se2VKc;A1ScaVsegs;VC;VE;A3S36S43G0A1SefR9SdfVE;A1M2R8A3S46G0R7A2A3S36S3eSbdVC;VNP;RaG2R9R8S45S1SddVE;A1M3S45S1SdeVE;A1M4S4bS1A1A3A3A7S40A3S36S3eSebVNP;S3RbA1A2S40A3S36S3eSb8S3RcA1R8A2S40A3S36S3eS52S3RdA1R8A2S40A3S36S3eSdS3ReA1SafRdPcM5A2A2S40A3S36S0SafS92ReS10aG4S3RfA1M6A4Se0A2S9S91G6UaM7A2A1A3S36S3eSc5S5R10A1RcS4dS4cA1S70RbA1ReA5S40A3S36S3eSf2S5R11A1S8Z1A1Z0SafR10G5A2A4S40A3S2S8eS3R13A1R10R1A3SabVsegs;S5dVsegs;S6cR10RfA2M8SbbR14R13R12G3A4R2A4ReA3F_;Frho';S2S8eS3R14A1R11R1A3SabVsegs;S5dVsegs;S6cS45G1S42S0S0S9S91S3R15A1G7A2A1SafR14G5A2A4R11A3R10A2SbbR15R14R13G4A4R2A4RfA3F_;Frho';SabVsegs;S5dVsegs;G8R14R11A4ReA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Ftv;Frho;FR;Fs;FCl;").
Proof using ML.
  intros Cl s R rho tv am Q Hvi MCX He Hchk Hnf Hnb Hamb Hs12 Hres Hrc Hpos Tnull Tok.
  apply (malloc_callA_ex Cl s R rho tv am Q Hvi MCX He Hchk Hnf Hnb Hamb Hs12 Hres); [|exact Tnull|exact Tok].
  intros Ai HF HP0 Hav HP HN HD HZ HXA (rhoM & md & HM) HT. split.
  - eapply (robjs_check_sound segs C FB Ai rho (ss_facts Cl) tv None (hdr_obj am) R None rhoM md HM HT HF HN HD HZ Hrc); [|exact I].
    intros o a Ho Hx Hr. exact (hdr_obj_caddr am Ai rho tv o a HXA Hx Hr).
  - pose proof (uleq_sound rho (ss_facts Cl) _ 0 _ HF Hpos) as U1. unfold U in U1. rewrite U_lit in U1.
    unfold M64v in U1. rewrite Z.mod_small in U1 by lia. lia.
Qed.

Theorem free_site_autoA : ltac2:(tb__ "0|4|
Sa9OF_;S1Sb0S41S4A1M0S2S41S3fS0S0A2M1A1S51S4cG1Sa8Se1Vsegs;RaVKc;A3Sc9Vsegs;VC;VE;A3S36S43G0A1SefRbSe4VE;A1M2RaA3S46G0R9A2A3S36S3eSbdVC;VNP;RcG2RbRaS45S1Se3VE;A1M3S4bS1A1A3A7S40A3S36S3eSebVNP;S3RdA1A2S40A3S36S3eSb8S3ReA1RaA2S40A3S36S3eS52S3RfA1RaA2S40A3S36S43G1A1S66G1RcRaA3S46G1R9A2A3S36S3eS7S44S0S0RaA3SafR10PcA2A2S40A3S36S3eS7S48S0S0RbA3SafR11PdA2A2S40A3S36S3eS68S6S1aS1dS1cS118S44S0S0RcA3S8Z0A1A3A1A1S5R13A1A3S40A3S36S3eSc5S5R14A1R10S46S4cReA2S70RfA1R12A5S40A3S2S8eS3R16A1R13R1A3SaaVsegs;R18S5dVsegs;S6cSc6G1R11R13A3R12A2SbbR17R16R15G3A4R2A4RfA4F_;Frho';SaaVsegs;R17S5dVsegs;S6cR12R11A2R16R13A4ReA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ft;Fi;Fam;Ftv;Frho;FR;Fs;FCl;Fok;").
Proof using ML.
  intros ok Cl s R rho tv am i t Q Hok MC He Hchk Hnf Hnb Hamb Hnth H12 H13 Hnz Hrc Tfree.
  apply sv_eqb_sound in H12. apply sv_eqb_sound in H13.
  apply (free_callA ok Cl s R rho tv am i t Q Hok MC He Hchk Hnf Hnb Hamb Hnth); [|exact Tfree].
  intros Ai HF HP0 Hav HP HN HD HZ HXA (rhoM & md & HM) HT.
  apply existsb_exists in Hnz as (f & Hf & Hfe). apply sprop_eqb_sound in Hfe. subst f.
  pose proof (proj1 (Forall_forall _ _) HF _ Hf) as Hnz.
  assert (Tnz : tnz rho t) by (rewrite (surjective_pairing t); apply (tnz_of_fact rho (fst t) (snd t)); exact Hnz).
  rewrite <- H12, <- H13. split; [exact Tnz|]. split; [reflexivity|].
  eapply (robjs_check_sound segs C FB Ai rho (ss_facts Cl) tv (Some i) (hdr_obj am) R _ rhoM md HM HT HF HN HD HZ Hrc).
  - intros o a Ho Hx Hr. change (bv_unsigned (eval rho (fst t))) with (fst (tvv rho t)).
    exact (hdr_obj_caddr_free am Ai rho tv o a t rhoM md HM HN (nth_error_In _ _ Hnth) Tnz HXA Hx Hr).
  - exists t. split; [exact Hnth|]. split; [exact Tnz|reflexivity].
Qed.

Theorem free_site_autoA_ex : ltac2:(tb__ "0|4|
S1Sb0S41S4A1M0S2S41S3fS0S0A2M1A1S51S4cG1Sa8Se2VKc;A1ScaVsegs;VC;VE;A3S36S43G0A1SefRbSe4VE;A1M2RaA3S46G0R9A2A3S36S3eSbdVC;VNP;RcG2RbRaS45S1Se3VE;A1M3S4bS1A1A3A7S40A3S36S3eSebVNP;S3RdA1A2S40A3S36S3eSb8S3ReA1RaA2S40A3S36S3eS52S3RfA1RaA2S40A3S36S43G1A1S66G1RcRaA3S46G1R9A2A3S36S3eS7S44S0S0RaA3SafR10PcA2A2S40A3S36S3eS7S48S0S0RbA3SafR11PdA2A2S40A3S36S3eS68S6S1aS1dS1cS118S44S0S0RcA3S8Z0A1A3A1A1S5R13A1A3S40A3S36S3eSc5S5R14A1R10S46S4cReA2S70RfA1R12A5S40A3S2S8eS3R16A1R13R1A3SabVsegs;S5dVsegs;S6cSc6G1R11R13A3R12A2SbbR17R16R15G3A4R2A4RfA3F_;Frho';SabVsegs;S5dVsegs;S6cR12R11A2R16R13A4ReA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Ft;Fi;Fam;Ftv;Frho;FR;Fs;FCl;").
Proof using ML.
  intros Cl s R rho tv am i t Q Hvi MCX He Hchk Hnf Hnb Hamb Hnth H12 H13 Hnz Hrc Tfree.
  apply sv_eqb_sound in H12. apply sv_eqb_sound in H13.
  apply (free_callA_ex Cl s R rho tv am i t Q Hvi MCX He Hchk Hnf Hnb Hamb Hnth); [|exact Tfree].
  intros Ai HF HP0 Hav HP HN HD HZ HXA (rhoM & md & HM) HT.
  apply existsb_exists in Hnz as (f & Hf & Hfe). apply sprop_eqb_sound in Hfe. subst f.
  pose proof (proj1 (Forall_forall _ _) HF _ Hf) as Hnz.
  assert (Tnz : tnz rho t) by (rewrite (surjective_pairing t); apply (tnz_of_fact rho (fst t) (snd t)); exact Hnz).
  rewrite <- H12, <- H13. split; [exact Tnz|]. split; [reflexivity|].
  eapply (robjs_check_sound segs C FB Ai rho (ss_facts Cl) tv (Some i) (hdr_obj am) R _ rhoM md HM HT HF HN HD HZ Hrc).
  - intros o a Ho Hx Hr. change (bv_unsigned (eval rho (fst t))) with (fst (tvv rho t)).
    exact (hdr_obj_caddr_free am Ai rho tv o a t rhoM md HM HN (nth_error_In _ _ Hnth) Tnz HXA Hx Hr).
  - exists t. split; [exact Hnth|]. split; [exact Tnz|reflexivity].
Qed.

Lemma JGA_tv_facts : ltac2:(tb__ "0|1|
S41S3fS0S0A2M0A1S51S2S41S6bA1S6aG0S6cR6R5R4R3R2A5S65G0R2R7A3Sb9R6R3A2S8dS6ScR7A1SdbR4A1A3F_;F_;F_;Ft;Fmd;Ftr;Frho;Fam;Ftv;").
Proof using . intros tv am rho tr md t [Ai [H _]] Hin Hnz. eapply (tv_facts_hold segs C NP Kc rho0 P0f FB); eauto. Qed.

Theorem malloc_site_extA : ltac2:(tb__ "0|a|
Sa9OF_;S1Sb0S41S4A1M0S2S41S3fS0S0A2M1A1S51S4S3eFx;Sa8Se1Vsegs;R9VKc;A3Sc9Vsegs;VC;VE;A3S36S43G0A1SefRaSdfVE;A1M2R9A3S46G0R8A2A3S36S3eSbdVC;VNP;RbG2RaR9S45S1SddVE;A1M3S45S1SdeVE;A1M4S4bS1A1A3A3A7S40A3S36S3eSebVNP;S3RcA1A2S40A3S36S3eSb8S3RdA1R9A2S40A3S36S3eS52S3ReA1R9A2S40A3S36S3eSdS3RfA1SafRePcM5A2A2S40A3S36S0SafS92RfS10aG4S3R10A1M6A4Se0A2S9S91G6UaM7A2A1A3S36S3eSc5S5R11A1RdS4dS4cA1S4S3eS3eL_;S70RdR1A2S40RcR1A1X3ex2Lo;RfA5S40A3S4S33S65S4R2R12A3S36S3eRfR3A1S40A3VP0f;Vrho0;A1S8eVNP;Vrho0;R14A3S8dS6ScR15A1S5R18A1A3S37S9dS44S33S33SeR16R7A2M8A3R6A2S9fR6S48S33S33G8A3A2A2Sc0Vsegs;VC;Vrho0;VFB;R7A5F_;F_;F_;F_;F_;F_;Fa;Fo;S36S3eSf2S5R13A1S8Z1A1Z0SafR12G5A2A4S40A3S2S8eS3R15A1R12R1A3SaaVsegs;R17S5dVsegs;S6cR12R11A2M9SbbR16R15R14G3A4R2A4RfA4F_;Frho';S2S8eS3R16A1R13R1A3SaaVsegs;R18S5dVsegs;S6cS45G1S42S0S0S9S91S3R17A1G7A2A1SafR16G5A2A4R13A3R12A2SbbR17R16R15G4A4R2A4R10A4F_;Frho';SaaVsegs;R17S5dVsegs;G9R16R13A4RfA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fextra;Fam;Ftv;Frho;FR;Fs;FCl;Fok;").
Proof using ML.
  intros ok Cl s R rho tv am extra Q Hok MC He Hchk Hnf Hnb Hamb Hs12 Hres Hrc Hext Hpos Tnull Tok.
  apply (malloc_callA ok Cl s R rho tv am Q Hok MC He Hchk Hnf Hnb Hamb Hs12 Hres); [|exact Tnull|exact Tok].
  intros Ai HF HP0 Hav HP HN HD HZ HXA (rhoM & md & HM) HT. split.
  - eapply (robjs_check_sound segs C FB Ai rho (ss_facts Cl) tv None _ R None rhoM md HM HT HF HN HD HZ Hrc); [|exact I].
    intros o a Ho Hx Hr. apply lazy_orb_prop in Hx as [Hx|Hx].
    + exact (hdr_obj_caddr am Ai rho tv o a HXA Hx Hr).
    + apply (pclF_caddr_chk _ _ _ _ _ rho Ai a Hav Hchk HT HP). exact (Hext o a Ho Hx HP0 Hav HF Hr).
  - pose proof (uleq_sound rho (ss_facts Cl) _ 0 _ HF Hpos) as U1. unfold U in U1. rewrite U_lit in U1.
    unfold M64v in U1. rewrite Z.mod_small in U1 by lia. lia.
Qed.

Theorem malloc_site_extA_ex : ltac2:(tb__ "0|a|
S1Sb0S41S4A1M0S2S41S3fS0S0A2M1A1S51S4S3eFx;Sa8Se2VKc;A1ScaVsegs;VC;VE;A3S36S43G0A1SefRaSdfVE;A1M2R9A3S46G0R8A2A3S36S3eSbdVC;VNP;RbG2RaR9S45S1SddVE;A1M3S45S1SdeVE;A1M4S4bS1A1A3A3A7S40A3S36S3eSebVNP;S3RcA1A2S40A3S36S3eSb8S3RdA1R9A2S40A3S36S3eS52S3ReA1R9A2S40A3S36S3eSdS3RfA1SafRePcM5A2A2S40A3S36S0SafS92RfS10aG4S3R10A1M6A4Se0A2S9S91G6UaM7A2A1A3S36S3eSc5S5R11A1RdS4dS4cA1S4S3eS3eL_;S70RdR1A2S40RcR1A1X3ex2Lo;RfA5S40A3S4S33S65S4R2R12A3S36S3eRfR3A1S40A3VP0f;Vrho0;A1S8eVNP;Vrho0;R14A3S8dS6ScR15A1S5R18A1A3S37S9dS44S33S33SeR16R7A2M8A3R6A2S9fR6S48S33S33G8A3A2A2Sc0Vsegs;VC;Vrho0;VFB;R7A5F_;F_;F_;F_;F_;F_;Fa;Fo;S36S3eSf2S5R13A1S8Z1A1Z0SafR12G5A2A4S40A3S2S8eS3R15A1R12R1A3SabVsegs;S5dVsegs;S6cR12R11A2M9SbbR16R15R14G3A4R2A4RfA3F_;Frho';S2S8eS3R16A1R13R1A3SabVsegs;S5dVsegs;S6cS45G1S42S0S0S9S91S3R17A1G7A2A1SafR16G5A2A4R13A3R12A2SbbR17R16R15G4A4R2A4R10A3F_;Frho';SabVsegs;S5dVsegs;G9R16R13A4RfA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fextra;Fam;Ftv;Frho;FR;Fs;FCl;").
Proof using ML.
  intros Cl s R rho tv am extra Q Hvi MCX He Hchk Hnf Hnb Hamb Hs12 Hres Hrc Hext Hpos Tnull Tok.
  apply (malloc_callA_ex Cl s R rho tv am Q Hvi MCX He Hchk Hnf Hnb Hamb Hs12 Hres); [|exact Tnull|exact Tok].
  intros Ai HF HP0 Hav HP HN HD HZ HXA (rhoM & md & HM) HT. split.
  - eapply (robjs_check_sound segs C FB Ai rho (ss_facts Cl) tv None _ R None rhoM md HM HT HF HN HD HZ Hrc); [|exact I].
    intros o a Ho Hx Hr. apply lazy_orb_prop in Hx as [Hx|Hx].
    + exact (hdr_obj_caddr am Ai rho tv o a HXA Hx Hr).
    + apply (pclF_caddr_chk _ _ _ _ _ rho Ai a Hav Hchk HT HP). exact (Hext o a Ho Hx HP0 Hav HF Hr).
  - pose proof (uleq_sound rho (ss_facts Cl) _ 0 _ HF Hpos) as U1. unfold U in U1. rewrite U_lit in U1.
    unfold M64v in U1. rewrite Z.mod_small in U1 by lia. lia.
Qed.

Lemma block_geom : ltac2:(tb__ "0|3|
SacS2S6aS33S33SdcVsegs;VC;R5R4R3A5S65S3fS33S33A2S42S33S33R3R2A4SadR6A1A3S37S9dZ0M0R3A2S37S36S33Sa5R4Z10M1A2G0A3S37S9dS9eZ1000G1A2R4A2S37S37S9dS9eS9eR4R3A2Z4A2Sf7SaeR7A1A1M2A2S9dG2Z7fffff800000A2A2S33S37S9dR5R1A2S9fR1S9eR5R4A2A2A2S39S37S9dSf9VC;A1R2A2S9fR2Sf8VC;A1A2A2A1F_;Fa;A2A2A2A2F_;F_;Fn;Fb;Fmd;Frho;FAi;").
Proof using ML.
  clear - ML HNP Uv. intros Ai rho md b n HM Hin. unfold MInvR in HM.
  pose proof (minv_block_geom C Ai _ _ _ b n HM Hin) as (G0 & G1 & G2 & G3 & G4).
  pose proof (topL_range (ma_L Ai)) as TRg. unfold PGSZ, UNIT, IB in *.
  split; [exact G0|]. split; [exact G1|]. split; [lia|]. split; [lia|].
  intros a Ha. exact (proj2 (block_addr_props segs C Ai _ _ _ b n a ML HM Hin Ha)).
Qed.

Lemma block_byte_overlay : ltac2:(tb__ "0|3|
SacS2S6aS33S33S33Sb5Q40M0A1S43Sb5Q8A1M1A1M2F_;SdcVsegs;VC;R7R6R5A5S65S3fS33S33A2S42S33S33R5R4A4SadR8A1A3S37S9dR6R4A2S9fR4S9eR6R5A2A2A2S39S36G2Sf6Vsegs;R4Sb7G0R5A2A3S4dG1A1A3A1S38G1G1S36G2R6Sb7G0R7A2A1S46G1R1A2A3Lx;A2F_;F_;F_;F_;Fm;Fa;Fn;Fb;Fmd;Frho;FAi;").
Proof using ML.
  clear - ML HNP Uv. intros Ai rho md b n a m HM Hin Ha Hw.
  pose proof (block_geom Ai rho md b n HM Hin) as (G0 & _ & G2 & G3 & G4).
  unfold wview in Hw. destruct (m (Z_to_bv 64 a)) as [x|] eqn:Hm; [exists x; reflexivity|]. exfalso.
  destruct (find_segment segs (bv_unsigned (Z_to_bv 64 a)) 1) as [seg|] eqn:Hf; [|exact (Hw eq_refl)].
  destruct (seg_writable seg) eqn:Hsw; [|exact (Hw eq_refl)].
  assert (W : wseg_addr segs (Z_to_bv 64 a) = true) by (unfold wseg_addr; rewrite Hf; exact Hsw).
  apply (ml_wseg segs C ML) in W. rewrite u64_of_sum in W by (unfold aceil in G3; lia). exact (G4 a Ha W).
Qed.

Lemma pclF_not_block : ltac2:(tb__ "0|1|
SacS2S6aS33S33S33SdcVsegs;VC;R6R5R4A5Sc4VC;Vrho0;R7A3SbcVFB;R8A2S65S3fS33S33A2M0S42S33S33R6R5A4SadR9A1A3S39S65G0S42S33S33R7R6A4VFB;A3A1S37S9dR8R6A2S9fR6S9eR8R7A2A2A2Sc0Vsegs;VC;Vrho0;VFB;R7A5S3cF_;F_;F_;F_;F_;F_;F_;Fa;Fn;Fb;Fmd;Frho;FAi;").
Proof using ML.
  clear - ML HNP Uv. intros Ai rho md b n a HM HT HP Hin Hnfb Ha Hp.
  pose proof (block_geom Ai rho md b n HM Hin) as (G0 & _ & G2 & G3 & G4).
  destruct Hp as [H|[H|(b' & n' & Hin' & Hr')]].
  - pose proof (TPI_top _ _ _ HT) as ET. unfold T0 in H, ET. rewrite <- ET in H. lia.
  - destruct H as (W & _). apply (ml_wseg segs C ML) in W. rewrite u64_of_sum in W by (unfold aceil in G3; lia). exact (G4 a Ha W).
  - apply (blocks_disjoint Ai rho md b n b' n' a HM Hin (HP _ Hin')); [|exact Ha|exact Hr'].
    intros Heq. rewrite Heq in Hnfb. exact (Hnfb Hin').
Qed.

Lemma pclFx_not_block : ltac2:(tb__ "0|1|
SacS2S6aS41S3fS0S0A2A1S33S33S33SdcVsegs;VC;R7R6R5A5Sc4VC;Vrho0;R8A3SbcVFB;R9A2SbeVFB;RaR9R7A4S65S3fS33S33A2M0S42S33S33R7R6A4SadRbA1A3S39S65G0S42S33S33R8R7A4VFB;A3A1S7cRcRaS42S33S33R9R8A4A3S37S9dRaR8A2S9fR8S9eRaR9A2A2A2Sc0Vsegs;VC;Vrho0;Sc3VFB;ReRcA3R9A5S3cF_;F_;F_;F_;F_;F_;F_;F_;F_;Fa;Fn;Fb;Ftv;Fmd;Frho;FAi;").
Proof using ML.
  clear - ML HNP Uv. intros Ai rho md tv b n a HM HT HP HN Hin Hnfb Hut Ha Hp.
  destruct Hp as [H|[H|(b' & n' & Hin' & Hr')]].
  - exact (pclF_not_block Ai rho md b n a HM HT HP Hin Hnfb Ha (or_introl H)).
  - exact (pclF_not_block Ai rho md b n a HM HT HP Hin Hnfb Ha (or_intror (or_introl H))).
  - apply In_FBx in Hin' as [Hin'|(t & Ht & Hnz & Htv)].
    + apply (pclF_not_block Ai rho md b n a HM HT HP Hin Hnfb Ha). right; right. exists b', n'. auto.
    + destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (_ & Hbl & _). rewrite Htv in Hbl.
      apply (blocks_disjoint Ai rho md b n b' n' a HM Hin Hbl); [|exact Ha|exact Hr'].
      intros Heq. apply (Hut t Ht Hnz). rewrite Htv. symmetry. exact Heq.
Qed.

Lemma pclF_FBx : ltac2:(tb__ "0|0|
S2S41S3fS0S0A2A1S33Sc0Vsegs;VC;Vrho0;VFB;R1A5Sc0Vsegs;VC;Vrho0;Sc3VFB;R4R3A3R2A5F_;Fa;Fkept;Frho;").
Proof using .
  clear -Uv. intros rho kept a [H|[H|(b & n & Hin & Hr)]]; [left; exact H | right; left; exact H | right; right].
  exists b, n. split; [|exact Hr]. apply In_FBx. left. exact Hin.
Qed.

Lemma robjs_okF_disjoint : ltac2:(tb__ "0|1|
SacS2S6aS41S3fS0S0A2A1S41S4A1S33S33S33S33SdcVsegs;VC;R9R8R7A5Sc4VC;Vrho0;RaA3SbcVFB;RbA2SbeVFB;RcRbR9A4S65S3fS33S33A2M0S42S33S33R8R7A4SadRdA1A3S39S65G0S42S33S33R9R8A4VFB;A3A1S7cReRcS42S33S33RaR9A4A3ScdVsegs;VC;Vrho0;VFB;RfRdRcA7S9dRcRaA2S9dRaS9eRdRcA2A2S8dS4S4S29SeR13R1A2S42S33S33RdRcA4A2Lo';RfA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fhi;Flo;Fn;Fb;Fobjs;Ftv;Fmd;Frho;FAi;").
Proof using ML.
  clear - ML HNP Uv. intros Ai rho md tv objs b n lo hi HM HT HP HN Hin Hnfb Hut HR Hlo Hhi.
  apply Forall_forall. intros o Ho. destruct (obj_range rho o) as [l h] eqn:E.
  apply ranges_disjoint_by_points. cbn [fst snd]. intros a Ha1 Ha2.
  apply (pclFx_not_block Ai rho md tv b n a HM HT HP HN Hin Hnfb Hut); [lia|].
  apply (HR o a Ho). rewrite E. exact Ha1.
Qed.

Lemma swf_facts_suffix : ltac2:(tb__ "0|2|
S33S41S0A1M0G0S32S43S0A1S41S4A1S41S6A1M1G1S34S3eS36S3eS12S14RaR9R8R7R6R5S47S6R4R3A3R2R1A9A1S40A3S36S3eS12S14RbRaR9R8R7R6R4R3R2A9A1S40A3F_;Flm;Fnx;FG;FF;Fobjs;Fresv;Ffcsr;Ffregs;Fregs;Fpc;").
Proof using .
  clear -Uv. intros pc regs fregs fcsr resv objs F G nx lm H. unfold swf in *.
  cbn [ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts] in *.
  apply andb_prop in H as [H HF]. rewrite H. cbn [andb]. rewrite forallb_app in HF. apply andb_prop in HF as [_ HG]. exact HG.
Qed.

Lemma holds_fact_in : ltac2:(tb__ "0|0|
S2S1S3fS41S6bA1SfaA2S6SfVsegs;R4R3R2A4S36S3eS68S6S1aR2A1S5R4A1A3S40A3ScR6R3A2F_;F_;Ff;Fw;FS;Frho;").
Proof using .
  clear -Uv. intros rho S w f Hsm Hex. apply existsb_exists in Hex as (f' & Hf' & Hfe). apply sprop_eqb_sound in Hfe. subst f'.
  exact (proj1 (Forall_forall _ _) (smatch_facts_hold segs _ _ _ Hsm) _ Hf').
Qed.

Definition hdr_cells (n : positive) : list (Z * nat * sv) := ltac2:(tb__ "0|3|
S45S3fS3fS33S4cA2M0S0A2M1S42G0S0S42S33S4cZ0U8M2A4S9Vn;A1A4S45G1S42G0S0S42S33S4cZ8G2A4S9SecVn;P1A2A1A4S45G1S42G0S0S42S33S4cZ10G2A4S9SecVn;P2A2A1A4S4bG1A1A3A3A3").
Definition open_facts (hd : sv) (n : positive) : list sprop := ltac2:(tb__ "0|6|
S47S6S45S6S18S9SecVn;P2A2A1S9SecVn;P1A2A1M0A2S45S6S18S1bS117S1bS117Vhd;S8Z20A1A3G0A3S8Z7fffff800000A1M1A2S45S6S18G0G1A2S45S6S18Vhd;G1A2S45S6S18S8Z1000A1Vhd;A2S4bS6A1M2A3A3A3A3A3S0S41S6A1Lhd;Vhd;S33G2Lz;S34S45S6S2bR1Z4A2G2A3Lv;S119S0S0G2Lb;La;M3Lop;M4G4S11aG3Lop;M5G5S3eS35S0G2La;Lw;Lsgn;S34S0S33G2Lk;Li;Ll;X0x8A3").
Definition open_state (S : sstate) (hd : sv) : sstate := ltac2:(tb__ "0|0|
S3VS;A1S34S14S22VS;A1S23VS;A1S21VS;A1S20VS;A1S24VS;A1S47S4S10VS;A1S45S4S122Vhd;Z0Z18S88R1A1A4S4bS4A1A3A3S47S6S8aVhd;R1A2S5VS;A1A3SecR1P3A2S17VS;A1A9Tn;").

Lemma rw_set3 : ltac2:(tb__ "0|3|
S2S34Sb5Q40A1M0G0G0S11dS11dS11dR5R4R3A3SecR4P1M1A2R2A3SecR4P2M2A2R1A3S2S37S36G0S26R1R5A2R4A3S37S36G0S26R1SecR5G1A2A2R3A3S37S36G0S26R1SecR5G2A2A2R2A3S11R5R6R1A3A2A2A2Trho';Fz;Fy;Fx;Fn;Frho;").
Proof using .
  clear -Uv. intros rho n x y z. unfold rho_set_rw. cbn [rw].
  assert (E1 : Pos.eqb n (n + 2) = false) by (apply Pos.eqb_neq; lia).
  assert (E2 : Pos.eqb n (n + 1) = false) by (apply Pos.eqb_neq; lia).
  assert (E3 : Pos.eqb (n + 1) (n + 2) = false) by (apply Pos.eqb_neq; lia).
  rewrite E1, E2, E3, !Pos.eqb_refl. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [|split; [intros; reflexivity | intros; reflexivity]].
  intros i Hi. cbn [rw].
  assert (F1 : Pos.eqb i (n + 2) = false) by (apply Pos.eqb_neq; lia).
  assert (F2 : Pos.eqb i (n + 1) = false) by (apply Pos.eqb_neq; lia).
  assert (F3 : Pos.eqb i n = false) by (apply Pos.eqb_neq; lia).
  rewrite F1, F2, F3. reflexivity.
Qed.

Lemma JGA_open : ltac2:(tb__ "0|3|
S41S3fS0S0A2M0A1S0S1S4S3eF_;S2Sa9S36S3eS12S84R4R5A2A1S40A3S36S3eSebVNP;S3R5A1A2S40A3S36S3eSb8S3R6A1R8A2S40A3S36S3eSdS3R7A1R8A2S40A3S36S3eSc5S5R8A1RaS4dS4cA1R7S10R8A1A5S40A3S4S33S65S4R2S10RbA1A3S36S3eRbR3A1S40A3VP0f;Vrho0;A1S8eVNP;Vrho0;RcA3S8dS6ScRdA1S5RfA1A3S37S9dS44S33S33SeReR7A2M1A3R6A2S9fR6S48S33S33G1A3A2A2Sc0Vsegs;VC;Vrho0;VFB;R7A5F_;F_;F_;F_;F_;F_;Fa;Fo;S36S3eS68S6S1aS1dS1cS118RbS8Z0A1A3A1A1S5RaA1A3S40A3S5dVsegs;S6cRdS55RcA1A2RbR9R8A5S38S2S2S37S11S3RdA1M2RbR1A3S5dVsegs;S6cRfS54ReS9G2A1S9SecG2P1A2A1S4bG0A1A4A2S84RdReA2R1RaA5A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;Fw;Frho;Fextra;FS;Fhd;Ftv;").
Proof using ML HNP.
  intros tv hd S extra rho w Hwf Hnp Htb Hhb Hrc Hext Hnz [Hsm [Ai [HJ HX]]].
  destruct w as [tr [ms md]]. apply Pos.leb_le in Hnp.
  pose proof HJ as (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
  pose proof (MI1 segs C _ _ _ _ HM) as HMr.
  pose proof (smatch_facts_hold segs _ _ _ Hsm) as HF.
  cbn in HX. destruct HX as (ns & HA & HNS). unfold Uv in HA.
  assert (Hh : bv_unsigned (eval rho hd) <> 0).
  { exact (tnz_of_fact rho hd (SLit 0) (holds_fact_in rho S _ _ Hsm Hnz)). }
  destruct (achain_cons (rm rho) _ ns HA Hh) as (cap & r & ->).
  cbn [achain] in HA. destruct HA as (_ & _ & Hcap0 & Hrd8 & (u & Hrd16 & Hu) & Hdef & (nx & Hrd0 & HAr)).
  set (h := bv_unsigned (eval rho hd)) in *.
  destruct HNS as [HF1 HND]. pose proof (Forall_inv HF1) as (Hblk & Hnfb & Hut). cbn [fst snd] in Hblk, Hnfb, Hut.
  pose proof (Forall_inv_tail HF1) as HFr.
  pose proof (block_geom Ai rho md h (HDR + cap) HMr Hblk) as (G0 & G1 & G2 & G3 & G4). unfold HDR in G3.
  pose proof (rd64_range _ _ _ Hrd0) as Rnx. pose proof (rd64_range _ _ _ Hrd8) as Rcap. pose proof (rd64_range _ _ _ Hrd16) as Ru.
  set (n := ss_next S) in *.
  destruct (rw_set3 rho n (Z_to_bv 64 nx) (Z_to_bv 64 cap) (Z_to_bv 64 u)) as (R0 & R1 & R2 & Hag).
  set (rho' := rho_set_rw (rho_set_rw (rho_set_rw rho n (Z_to_bv 64 nx)) (n + 1) (Z_to_bv 64 cap)) (n + 2) (Z_to_bv 64 u)) in *.
  exists rho'. split; [exact Hag|].
  assert (Hrm : rm rho' = rm rho) by reflexivity.
  assert (Ehd : eval rho' hd = eval rho hd) by (symmetry; apply (eval_agree n); [exact Hag | exact Hhb]).
  clearbody rho'.
  pose proof (agree_below_vals _ _ _ Hag) as Hagv.

  assert (HRF : robjs_okF segs C rho0 FB rho tv (ss_objs S)).
  { eapply (robjs_checkF_sound segs C rho0 FB rho (ss_facts S) tv extra (ss_objs S) HF (T_ok_T0 rho Ai Hav (proj2 (proj2 HM))) HZ Hrc).
    intros o a Ho Hx Hr. apply pclF_FBx. exact (Hext o a Ho Hx HP0 Hav HF Hr). }

  pose proof (smatch_agree segs rho rho' S _ Hag Hsm) as Hsm'.
  assert (Hwf1 : swf (mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S)
                            (ss_objs S ++ [carved hd 0 24 (hdr_cells n)]) (ss_facts S) (n + 3) (ss_lenient S)) = true).
  { unfold open_state in Hwf. eapply swf_facts_suffix. exact Hwf. }
  pose proof (smatch_carve_obj segs rho' S (tr, mkCfg ms md) hd 0 24 (hdr_cells n) (n + 3) Hsm' Hwf1) as CARVE.
  cbv zeta in CARVE. rewrite Ehd in CARVE. fold h in CARVE.
  assert (Hsm1 : smatch segs rho' (mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S)
                            (ss_objs S ++ [carved hd 0 24 (hdr_cells n)]) (ss_facts S) (n + 3) (ss_lenient S)) (tr, mkCfg ms md)).
  { unfold aceil in G3. apply CARVE; clear CARVE; try lia.
    - unfold hdr_cells, cells_inside. repeat apply Forall_cons; try apply Forall_nil; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    - apply Forall_forall. intros o Ho. rewrite (obj_range_agree_vals n rho rho' o Hagv (proj1 (forallb_forall _ _) (swf_objs _ (smatch_swf segs _ _ _ Hsm)) o Ho)).
      eapply (proj1 (Forall_forall _ _) (robjs_okF_disjoint Ai rho md tv (ss_objs S) h (HDR + cap) (h + 0) (h + 24) HMr (proj2 (proj2 HM)) HP HN Hblk Hnfb Hut HRF ltac:(lia) ltac:(unfold HDR; lia))). exact Ho.
    - intros off Hoff. rewrite Hrm. unfold wok_of, rd_of.
      destruct (rm rho (Z_to_bv 64 (h + off))) as [x|] eqn:Ex; [split; [reflexivity | exists x; reflexivity]|].
      exfalso. apply (Hdef (h + off)); [unfold HDR; lia | exact Ex].
    - unfold hdr_cells, cells_in_view. rewrite Hrm.
      repeat constructor; intros j Hj; cbn [eval]; rewrite ?R0, ?R1, ?R2; unfold rd_of.
      + rewrite Z.add_0_r. rewrite (rd64_enc_bytes (rm rho) h nx Hrd0 j Hj). reflexivity.
      + rewrite (rd64_enc_bytes (rm rho) (h + 8) cap Hrd8 j Hj). reflexivity.
      + rewrite (rd64_enc_bytes (rm rho) (h + 16) u Hrd16 j Hj). reflexivity. }
  clear CARVE.

  assert (Ucap : bv_unsigned (eval rho' (SVar (n + 1))) = cap) by (cbn [eval]; rewrite R1; apply u64_of_sum; lia).
  assert (Uu : bv_unsigned (eval rho' (SVar (n + 2))) = u) by (cbn [eval]; rewrite R2; apply u64_of_sum; lia).
  assert (Uhd : bv_unsigned (eval rho' hd) = h) by (rewrite Ehd; reflexivity).
  assert (HOF : Forall (holds rho') (open_facts hd n)).
  { unfold open_facts. apply Forall_app. split.
    - constructor. { cbn [holds]. rewrite Ucap, Uu. exact Hu. }
      constructor. { cbn [holds]. rewrite !U_add, U_lit, Ucap, Uhd, U_lit. unfold M64v, aceil in *. rewrite !Z.mod_small by lia. lia. }
      constructor. { cbn [holds]. rewrite Ucap, U_lit. unfold M64v, aceil in *. rewrite Z.mod_small by lia. lia. }
      constructor. { cbn [holds]. rewrite Uhd, U_lit. unfold M64v, aceil in *. rewrite Z.mod_small by lia. lia. }
      constructor. { cbn [holds]. rewrite Uhd, U_lit. unfold M64v, aceil in *. rewrite Z.mod_small by lia. lia. }
      constructor.
    - destruct hd as [|v| | | | | |]; try apply Forall_nil. constructor; [|apply Forall_nil].
      cbn [holds]. split; [lia|]. cbn [eval] in Uhd. rewrite Uhd. change (2 ^ 4) with 16. exact G1. }
  split.
  - unfold open_state. fold n.
    change (smatch segs rho' (add_facts (open_facts hd n) (mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S)
                            (ss_objs S ++ [carved hd 0 24 (hdr_cells n)]) (ss_facts S) (n + 3) (ss_lenient S))) (tr, mkCfg ms md)).
    apply smatch_add_facts; [exact Hsm1 | exact HOF |].
    unfold open_state in Hwf. unfold swf in Hwf. cbn [ss_regs ss_fregs ss_next ss_fcsr ss_resv ss_objs ss_facts] in Hwf.
    apply andb_prop in Hwf as [_ Hwf]. rewrite forallb_app in Hwf. apply andb_prop in Hwf as [Hwf _]. exact Hwf.
  -
    exists Ai. split.
    + split; [eapply agree_vals_trans; [exact Hav | eapply agree_vals_le; [exact Hnp | exact Hagv]]|].
      split; [exact Hk|]. split; [unfold MInvR; rewrite Hrm; exact HM|]. split; [exact HP|]. split; [|split; [rewrite Hrm; exact HK | exact HP0]].
      split; [exact (tvin_agree FB Ai n rho rho' tv Hagv Htb HN)|].
      split; [exact (tvd_agree n rho rho' tv Hagv Htb HD) | exact (tvz_agree n rho rho' tv Hagv Htb HZ)].
    + cbn -[HDR]. unfold Uv. cbn [eval]. cbn [eval] in Ucap, Uhd. rewrite Uhd, Ucap, Hrm, R0. rewrite u64_of_sum by lia.
      split; [exact Hh|]. split; [lia|]. split; [exact Hblk|]. split; [exact Hnfb|]. split.
      * intros t Ht Hnz'. pose proof (proj1 (forallb_forall _ _) Htb t Ht) as Hbt.
        rewrite (tvv_agree n rho rho' t Hagv Hbt). apply (Hut t Ht). apply (proj1 (tnz_agree n rho rho' t Hagv Hbt)). exact Hnz'.
      * split; [intros z Hz; apply Hdef; unfold HDR in *; lia|]. split; [constructor|].
        exists r. split; [exact HAr|]. split.
        -- split; [|inversion HND; assumption].
           apply Forall_forall. intros bc Hbc. destruct (proj1 (Forall_forall _ _) HFr bc Hbc) as (Y1 & Y2 & Y3).
           split; [exact Y1|]. split; [exact Y2|]. intros t Ht Hnz'. pose proof (proj1 (forallb_forall _ _) Htb t Ht) as Hbt.
           rewrite (tvv_agree n rho rho' t Hagv Hbt). apply (Y3 t Ht). apply (proj1 (tnz_agree n rho rho' t Hagv Hbt)). exact Hnz'.
        -- inversion HND; subst. intros Hin. apply H1. apply list_elem_of_In. exact Hin.
Qed.

Lemma tvv_set_rm : ltac2:(tb__ "0|0|
S2Sb5Q40A1S43Sb5Q8A1A1F_;S3fS0S0A2S36S3fS33S33A2SbaS116R3R2A2R1A2SbaR3R1A2A3Ft;Fm;Frho;").
Proof using . clear -Uv. intros. unfold tvv. rewrite !eval_set_rm. reflexivity. Qed.
Lemma tnz_set_rm : ltac2:(tb__ "0|0|
S2Sb5Q40A1S43Sb5Q8A1A1F_;S3fS0S0A2S3bSb9S116R3R2A2R1A2Sb9R3R1A2A2Ft;Fm;Frho;").
Proof using . clear -Uv. intros. unfold tnz. rewrite eval_set_rm. tauto. Qed.
Lemma map_tvv_set_rm : ltac2:(tb__ "0|2|
S2Sb5Q40A1S43Sb5Q8A1A1F_;S41S3fS0S0A2M0A1S36S41S3fS33S33A2M1A1S8cG0G1SbaS116R3R2A2A1R1A4S8cG0G1SbaR3A1R1A4A3Ftv;Fm;Frho;").
Proof using . clear -Uv. intros. apply map_ext. intros t. apply tvv_set_rm. Qed.
Lemma nth_tnz_set_rm : ltac2:(tb__ "0|3|
S2Sb5Q40A1S43Sb5Q8A1A1F_;S41S3fS0S0A2M0A1S4cG0G0S36S43G0A1M1S66G0R4R3A3S46G0R2A2M2A3S36G1S66G0R5R4A3G2A3S3bSb9S116R8R7A2R3A2Sb9R8R4A2A2F_;F_;Ft';Ft;Fk;Ftv;Fm;Frho;").
Proof using . clear -Uv. intros rho m tv k t t' H1 H2. rewrite H1 in H2. injection H2 as <-. apply tnz_set_rm. Qed.
Lemma tvs_set_rm : ltac2:(tb__ "0|1|
SacS2Sb5Q40A1S43Sb5Q8A1A1F_;S41S3fS0S0A2A1S37SbeVFB;R4R3R1A4S37Sc1R3R1A2Sc2R3R1A2A2A2S37SbeVFB;R5S116R4R3A2M0R2A4S37Sc1G0R2A2Sc2G0R2A2A2A2F_;Ftv;Fm;Frho;FAi;").
Proof using .
  clear -Uv. intros Ai rho m tv (HN & HD & HZ). split; [|split].
  - eapply tvin_map; [apply map_tvv_set_rm | apply nth_tnz_set_rm | exact HN].
  - eapply tvd_map; [apply map_tvv_set_rm | apply nth_tnz_set_rm | exact HD].
  - eapply tvz_map; [apply map_tvv_set_rm | apply nth_tnz_set_rm | exact HZ].
Qed.
Lemma nodes_ok_set_rm : ltac2:(tb__ "0|0|
SacS2Sb5Q40A1S43Sb5Q8A1A1F_;S41S3fS0S0A2A1S41S3fS33S33A2A1S78R5R4R2R1A4S78R6S116R5R4A2R3R2A4F_;Fns;Ftv;Fm;Frho;FAi;").
Proof using .
  clear -Uv. intros Ai rho m tv ns [HF HD]. split; [|exact HD]. apply Forall_forall. intros bc Hin.
  destruct (proj1 (Forall_forall _ _) HF bc Hin) as (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
  intros t Ht Hnz. rewrite tvv_set_rm. apply (H3 t Ht). apply (proj1 (tnz_set_rm rho m t)). exact Hnz.
Qed.

Lemma J_set_rm_block : ltac2:(tb__ "0|6|
SacS2S6aS33S33S33S33Sb5Q40M0A1M1S43Sb5Q8A1A1M2F_;S37SdcVsegs;VC;R8R7R6A5S37Sd1R8A1Sc4VC;Vrho0;R8A3A2A2SbcVFB;R9A2S65S3fS33S33A2M3S42S33S33R7R6A4SadRaA1A3S39S65G3S42S33S33R8R7A4VFB;A3A1S9dR9R7A2S9dR7S9eRaR9A2A2G1S39S37S9dRaSb6G0R1A2M4A2S9fG4R9A2A2A1S36G2R9R2A1SaRfR2A2A3F_;Fa;Sd2Vsegs;VC;Vrho0;VFB;SaVrho0;A1M5SaReA1A6S37S37SdcVsegs;VC;R10S116RfR9A2ReA5S37Sd1R10A1Sc4VC;Vrho0;R10A3A2A2Sd2Vsegs;VC;Vrho0;VFB;G5R9A6A2F_;F_;F_;F_;F_;F_;F_;F_;Fm';Fhi;Flo;Fn;Fb;Fmd;Frho;FAi;").
Proof using ML.
  clear - ML HNP Uv. intros Ai rho md b n lo hi m' HM HP Hin Hnfb Hlo Hhi Hout HK.
  pose proof (block_geom Ai rho md b n (MI1 segs C _ _ _ _ HM) Hin) as (G0 & _ & G2 & G3 & _). unfold aceil in G3.
  split.
  - eapply (MInvR_mem segs C _ ML); [exact HM| |reflexivity]. intros a Ha Ho. cbn [set_rm rm]. apply Hout.
    rewrite u64_of_sum by exact Ha. intros Hr.
    assert (Hc : caddr segs C Ai None a) by (right; right; exists b, n; split; [exact Hin|]; split; [discriminate|lia]).
    destruct (caddr_props segs C Ai None a rho md ML (MI1 segs C _ _ _ _ HM) Ha Hc) as (O1 & O2 & O3).
    destruct Ho as [Ho|Ho]; [exact (O1 Ho) | exact (O3 Ho)].
  - intros a Ha Hp. rewrite Hout; [exact (HK a Ha Hp)|]. rewrite u64_of_sum by exact Ha. intros Hr.
    exact (pclF_not_block Ai rho md b n a (MI1 segs C _ _ _ _ HM) (proj2 (proj2 HM)) HP Hin Hnfb ltac:(lia) Hp).
Qed.

Lemma released_bytes : ltac2:(tb__ "0|8|
SacS2S6aSf4S33S33S4Sb5Q40M0A1M1S43Sb5Q8A1M2A1M3F_;SdcVsegs;VC;R8R7R6A5S65S3fS33S33A2S42S33S33R5R4A4SadR9A1A3S9dR6S44S33S33SeR9R4A2A3A2S9dS48S33S33SeRaR5A2A3S9eR7R6A2A2S30Vsegs;RbR9R6A4S36S3eS1eS1fR7A1A1S40A3G1S123SeReR9A2Sb6G0R1A2A2S36G3R9R2A1Sf5RdR2A2A3F_;Fa;S37S33S37S9dS44S33S33SeRfRaA2M4A3R1A2S9fR1S48S33S33G4A3A2A2S38G2G2S37S36G3RbSb7G0R3A2M5A1S46G2R1A2M6A3S36G3S31RfG5A2G6A3A2Lx;A2F_;Fz;S33S0S65S19S28S8R2A1Z8R1A3S25RbA1A3S37S9dSa7Sa0Z2Z3fA2M7A1R3A2S9fR3G7A2A2S36S43S33A1S115RcS9eSb6G0SbR12S13RdA1A2A2R4A2A2S46S33Sb6G0SbR12R3A2A2A2A3F_;F_;Fv;Foff;A2F_;F_;F_;F_;F_;F_;F_;Fm';Fo;Fn;Fb;Fms;Fmd;Frho;FAi;").
Proof using ML.
  clear - ML HNP Uv. intros Ai rho md ms b n o m' HM Hin Hlo Hhi Hoh Hdw Hm'.
  pose proof (block_geom Ai rho md b n HM Hin) as (G0 & _ & G2 & G3 & _). unfold aceil in G3.
  unfold obj_range in *. cbn [fst snd] in *.
  set (bb := bv_unsigned (eval rho (ob_base o))) in *.
  destruct Hoh as (Hrng & Hwv & Hcells & _ & _).
  assert (BY : forall z, bb + obj_lo_of rho o <= z < bb + obj_hi_of rho o ->
               exists x, m' (Z_to_bv 64 z) = Some x /\ rd ms (Z_to_bv 64 z) = Some x).
  { intros z Hz.
    pose proof (Hwv (z - bb) ltac:(lia) Hdw) as W. fold bb in W. replace (bb + (z - bb)) with z in W by lia.
    destruct (block_byte_overlay Ai rho md b n z (ms_mem ms) HM Hin ltac:(lia) W) as [x Hx].
    exists x. split.
    - rewrite Hm'; [exact Hx|]. unfold in_rng. cbn [fst snd]. rewrite u64_of_sum by lia. lia.
    - unfold rd, ms_read_byte. rewrite Hx. reflexivity. }
  split; [exact BY|].
  intros off v Hc Hoff. pose proof (proj1 (Forall_forall _ _) Hcells _ Hc) as CH.
  unfold cell_holds in CH. cbn [c_off c_width c_val] in CH. rewrite soff_lit_small in CH by lia.
  destruct CH as (C1 & C2 & C3). change (Z.to_nat 8) with 8%nat in C3.
  apply rd64_of_bytes. intros j Hj.
  assert (Hz : bb + obj_lo_of rho o <= bb + off + Z.of_nat j < bb + obj_hi_of rho o) by lia.
  destruct (BY _ Hz) as (x & Hx1 & Hx2). rewrite Hx1.
  pose proof (rd_bytes_nth ms 8 (oaddr rho (ob_base o) off) _ j C3 Hj) as RB.
  rewrite oaddr_unsigned in RB by lia. fold bb in RB.
  rewrite <- Hx2. symmetry. rewrite <- RB; [reflexivity|]. lia.
Qed.

Definition has_cell8 (o : sobj) (off : Z) (v : sv) : bool := ltac2:(tb__ "0|1|
S68S19S19S3eS3eL_;M0S7S2cR1A1S8Voff;A1A2G0Sa1S2eR1A1Z8A2S7S2dR1A1Vv;A2S49X3ex2S49X3ex2Lc;S25Vo;A1A3").
Lemma has_cell8_In : ltac2:(tb__ "0|0|
S4S33S0S36S3eS7bR3R2R1A3S40A3S65S19S28S8R3A1Z8R2A3S25R4A1A3F_;Fv;Foff;Fo;").
Proof using .
  clear - Uv. intros o off v H. unfold has_cell8 in H. apply existsb_exists in H as ([co cw cv] & Hin & Hc).
  apply lazy_andb_prop in Hc as [H1 Hc]. apply lazy_andb_prop in Hc as [H2 H3].
  apply sv_eqb_sound in H1. apply Z.eqb_eq in H2. apply sv_eqb_sound in H3. cbn in H1, H2, H3. subst. exact Hin.
Qed.
Definition hdr_shape (o : sobj) (hd nx cap u : sv) : bool := ltac2:(tb__ "0|2|
S3eS3eL_;M0S7S13Vo;A1Vhd;A2G0S7S16Vo;A1S8Z0M1A1A2G0S7S15Vo;A1S8Z18A1A2G0S1eS1fVo;A1A1G0S7bVo;G1Vnx;A3G0S7bVo;Z8Vcap;A3S7bVo;Z10Vu;A3S49X3ex2S49X3ex2S49X3ex2S49X3ex2S49X3ex2S49X3ex2").

Definition drop_last_state (S : sstate) (objs : list sobj) : sstate := ltac2:(tb__ "0|0|
S14S22VS;A1S23VS;A1S21VS;A1S20VS;A1S24VS;A1Vobjs;S5VS;A1S3VS;A1S17VS;A1A9").

Lemma JGA_close : ltac2:(tb__ "0|2|
S41S3fS0S0A2M0A1S0S0S0S0S1S41S4A1M1S4S2Sa9S36G1S10R5A1S47S4R4S45S4R3S4bS4A1A3A3A3S36S3eS83R4RaR9R8R7A5S40A3S36S3eSf2S5R7A1R8Z0R9A4S40A3S36S3eS12S73R8R7A2A1S40A3S5dVsegs;S6cReS54RdRcRbS4bG0A1A4A2R9R6R5A5S38S2S2S37S8eS3RbA1R8R1A3S5dVsegs;S6cR10S55RfA1A2S73RbRaA2R1R7A5A2Lrho';A2F_;F_;F_;F_;F_;Fw;Frho;Fo;Fobjs;FS;Fu;Fcap;Fnx;Fhd;Ftv;").
Proof using ML.
  intros tv hd nx cap u S objs o rho w Hobjs Hsh Hule Hwf [Hsm [Ai [HJ HX]]].
  destruct w as [tr [ms md]].
  pose proof HJ as (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
  pose proof (MI1 segs C _ _ _ _ HM) as HMr.
  pose proof (smatch_facts_hold segs _ _ _ Hsm) as HF.
  unfold hdr_shape in Hsh.
  apply lazy_andb_prop in Hsh as [Hb Hsh]. apply lazy_andb_prop in Hsh as [Hl Hsh]. apply lazy_andb_prop in Hsh as [Hh Hsh].
  apply lazy_andb_prop in Hsh as [Hdw Hsh]. apply lazy_andb_prop in Hsh as [Hc0 Hsh]. apply lazy_andb_prop in Hsh as [Hc8 Hc16].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  apply has_cell8_In in Hc0. apply has_cell8_In in Hc8. apply has_cell8_In in Hc16.
  cbn -[HDR] in HX. unfold Uv in HX. destruct HX as (X1 & X2 & X3 & X4 & X5 & X6 & _ & ns & HA & HNS & Hnin).
  set (h := bv_unsigned (eval rho hd)) in *. set (c := bv_unsigned (eval rho cap)) in *.
  pose proof (block_geom Ai rho md h (HDR + c) HMr X3) as (G0 & G1 & G2 & G3 & G4). unfold HDR, aceil in G3.
  assert (Hrng : obj_range rho o = (h, h + 24)).
  { unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb, Hl, Hh. rewrite !soff_lit_small by lia. fold h. f_equal; lia. }
  destruct (smatch_release_obj segs rho S (tr, mkCfg ms md) objs o (ss_next S) Hsm Hobjs Hwf) as (m' & Hsm' & Mout & Min & Hoh & _).
  cbn [cfg_ms w_cfg snd] in Min, Hoh.
  exists (set_rm rho m'). split; [split; intros; reflexivity|].
  split; [exact Hsm'|].
  destruct (released_bytes Ai rho md ms h (HDR + c) o m' HMr X3 ltac:(rewrite Hrng; cbn; lia) ltac:(rewrite Hrng; cbn; unfold HDR; lia) Hoh Hdw Min) as [BY CELLS].
  rewrite Hrng in BY. cbn [fst snd] in BY. rewrite Hb in CELLS. fold h in CELLS.
  assert (Mout' : forall a, ~ (h <= bv_unsigned a < h + 24) -> m' a = rm rho a).
  { intros a Ha. apply Mout. rewrite Hrng. unfold in_rng. cbn [fst snd]. exact Ha. }
  destruct (J_set_rm_block Ai rho md h (HDR + c) h (h + 24) m' HM HP X3 X4 ltac:(lia) ltac:(unfold HDR; lia) Mout' HK) as [HM' HK'].
  exists Ai. split.
  - split; [exact Hav|]. split; [exact Hk|]. split; [exact HM'|]. split; [exact HP|]. split; [|split; [exact HK' | exact HP0]].
    apply tvs_set_rm. exact (conj HN (conj HD HZ)).
  - cbn -[HDR]. unfold Uv. rewrite !eval_set_rm. fold h. exists ((h, c) :: ns). split.
    + cbn [achain]. split; [reflexivity|]. split; [exact X1|]. split; [exact X2|]. split.
      { apply (CELLS 8 cap Hc8). lia. }
      split.
      { exists (bv_unsigned (eval rho u)). split; [apply (CELLS 16 u Hc16); lia|].
        pose proof (uleq_sound rho (ss_facts S) u 0 cap HF Hule) as U1. unfold U in U1. fold c in U1. lia. }
      split.
      { intros z Hz. unfold HDR in *. destruct (Z_lt_dec z (h + 24)) as [Hlt|Hge].
        - destruct (BY z ltac:(lia)) as (x & Hx & _). rewrite Hx. discriminate.
        - cbn [set_rm rm]. rewrite Mout' by (rewrite u64_of_sum by lia; lia). apply X6. lia. }
      exists (bv_unsigned (eval rho nx)). split; [rewrite <- (Z.add_0_r h); apply (CELLS 0 nx Hc0); lia|].

      destruct HNS as [HFns _].
      eapply achain_frame; [exact HA| |].
      * intros z (b & cp & Hinb & Hz). cbn [set_rm rm]. apply Mout'. rewrite u64_of_sum.
        2:{ destruct (proj1 (Forall_forall _ _) HFns _ Hinb) as (B1 & _). cbn [fst snd] in B1.
            pose proof (block_geom Ai rho md b (HDR + cp) HMr B1) as (_ & _ & B2 & B3 & _). unfold aceil, HDR in B3.
            pose proof (proj1 (Forall_forall _ _) (achain_caps _ _ _ HA) _ Hinb) as [Bc _]. cbn in Bc. lia. }
        intros Hz'. destruct (proj1 (Forall_forall _ _) HFns _ Hinb) as (B1 & _). cbn [fst snd] in B1.
        apply (blocks_disjoint Ai rho md h (HDR + c) b (HDR + cp) z HMr X3 B1); [|unfold HDR; lia|].
        -- intros Heq. injection Heq as E1 E2. apply Hnin. apply in_map_iff. exists (b, cp). split; [cbn; lia | exact Hinb].
        -- pose proof (proj1 (Forall_forall _ _) (achain_caps _ _ _ HA) _ Hinb) as [Bc _]. cbn in Bc. unfold HDR. lia.
      * intros z (b & cp & Hinb & Hz) Hdef. cbn [set_rm rm].
        destruct (proj1 (Forall_forall _ _) HFns _ Hinb) as (B1 & _). cbn [fst snd] in B1.
        pose proof (block_geom Ai rho md b (HDR + cp) HMr B1) as (_ & _ & B2 & B3 & _). unfold aceil, HDR in B3.
        pose proof (proj1 (Forall_forall _ _) (achain_caps _ _ _ HA) _ Hinb) as [Bc _]. cbn in Bc.
        rewrite Mout'; [exact Hdef|]. rewrite u64_of_sum by (unfold HDR in Hz; lia). intros Hz'.
        apply (blocks_disjoint Ai rho md h (HDR + c) b (HDR + cp) z HMr X3 B1); [|unfold HDR; lia| lia].
        intros Heq. injection Heq as E1 E2. apply Hnin. apply in_map_iff. exists (b, cp). split; [cbn; lia | exact Hinb].
    + pose proof (nodes_ok_set_rm Ai rho m' tv ns HNS) as [HNS1 HNS2]. split.
      * constructor; [|exact HNS1]. cbn [fst snd]. split; [exact X3|]. split; [exact X4|].
        intros t Ht Hnz. rewrite tvv_set_rm. apply (X5 t Ht). apply (proj1 (tnz_set_rm rho m' t)). exact Hnz.
      * cbn [map fst]. constructor; [|exact HNS2]. intros Hin. apply Hnin. apply list_elem_of_In. exact Hin.
Qed.

Definition plain_obj (base hi : sv) : sobj := ltac2:(tb__ "0|0|
S2fVbase;S8Z0A1Vhi;S4bS19A1S2aA5").

Lemma smatch_carve_plain : ltac2:(tb__ "0|3|
S2S1S3fS41S6bA1SfaA2S0S0S34SfVsegs;R6R5R4A4S14S22R6A1S23R6A1S21R6A1S20R6A1S24R6A1S47S4S10R6A1S45S4S85R4R3A2S4bS4A1A3A3S5R6A1R2S17R6A1A9S1S36S3eS12R1A1S40A3Sb6Q40M0SbR9R6A2A2S33Sb6G0SbRaR6A2A2S33S9fR1Sa0Z2M1Z3fA2A2S9dS9eR3R2A2Sa0G1Z40A2A2S8dS4S4S29SeReR1A2S42S33S33R5S9eR5R4A2A4A2Lo';S10RcA1A3S33S37S9dR6R1A2S9fR1S9eR6R5A2A2A2S38Sb5Q8A1M2G2S36S43G2A1SaR11Sb7G0R3A2A2S46G2R1A2A3Lx;A2F_;Fz;SfVsegs;RfR8RdA4F_;F_;F_;F_;Th;Tb;F_;TS';F_;Fnx;Fhi;Fbase;Fw;FS;Frho;").
Proof using .
  clear -Uv. intros rho S [tr [ms md]] base hi nx Hsm S' Hwf b h Hh Hbh Hdisj Hdef.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & Hm & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  destruct Hm as (Hall & Hpd & Hfr).
  pose proof (urange (eval rho base)) as Rb. pose proof (urange (eval rho hi)) as Rh. fold b in Rb. fold h in Rh.
  assert (Hsoff : soff rho hi = h).
  { unfold soff. rewrite bv_signed_U. fold h. destruct (Zsigned_spec h) as [[_ X]|[X _]]; [exact X | lia]. }
  assert (RNG : obj_range rho (plain_obj base hi) = (b, b + h)).
  { unfold obj_range, obj_lo_of, obj_hi_of, plain_obj. cbn [ob_base ob_lo ob_hi]. fold b.
    rewrite soff_lit_small by lia. rewrite Hsoff. f_equal. lia. }
  assert (OUT : forall z, b <= z < b + h -> outside_all rho (ss_objs S) (Z_to_bv 64 z)).
  { intros z Hz. eapply ranges_disjoint_outside; [exact Hdisj|]. rewrite u64_of_sum by lia. lia. }
  assert (MEM : forall z, b <= z < b + h -> exists x, ms_mem ms (Z_to_bv 64 z) = Some x /\ rm rho (Z_to_bv 64 z) = Some x).
  { intros z Hz. destruct (Hdef z Hz) as [x Hx]. exists x. split; [|exact Hx]. rewrite (Hfr _ (OUT z Hz)). exact Hx. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|].
  split; [exact Hrom|]. split; [exact Hro|]. split; [exact Hr|]. split; [exact Hf|].
  split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs]. split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [|constructor].
    unfold obj_holds, obj_lo_of, obj_hi_of, plain_obj. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. fold b.
    rewrite soff_lit_small by lia. rewrite Hsoff.
    split; [lia|]. split.
    { intros off Hoff _. destruct (MEM (b + off) ltac:(lia)) as (x & Hx & _). unfold wview. rewrite Hx. discriminate. }
    split; [constructor|]. split; [|exact I].
    intros off Hoff _. cbn [dflt_holds]. destruct (MEM (b + off) ltac:(lia)) as (x & Hx & _).
    exists x. unfold rd, ms_read_byte. rewrite Hx. reflexivity.
  - apply pairwise_disjoint_app1; [exact Hpd|]. rewrite RNG. exact Hdisj.
  - intros a Ha. apply Hfr. apply outside_all_app in Ha as [Ha _]. exact Ha.
Qed.

Definition carve_state (S : sstate) (p sz : sv) : sstate := ltac2:(tb__ "0|0|
S14S22VS;A1S23VS;A1S21VS;A1S20VS;A1S24VS;A1S47S4S10VS;A1S45S4S85Vp;Vsz;A2S4bS4A1A3A3S5VS;A1S3VS;A1S17VS;A1A9").

Lemma JGA_carve : ltac2:(tb__ "0|6|
S41S3fS0S0A2M0A1S0S0S0S0S0S1S4S3eFx;S2Sa9S36S3eS12S81R4R6R5A3A1S40A3S36S3eSebVNP;S3R5A1A2S40A3S36S3eSc5S5R6A1RcS4dS4cA1S4S3eS3eL_;S70S54RcRbRaS4bG0A1M1A4R1A2S40R6R1A1X3ex2Lo;S10R6A1A5S40A3S4S33S65S4R2S10R9A1A3S36S3eR9R3A1S40A3VP0f;Vrho0;A1M2S8eVNP;Vrho0;RaA3S8dS6ScRbA1S5RdA1A3S37S9dS44S33S33SeRcR7A2M3A3R6A2S9fR6S48S33S33G3A3A2A2Sc0Vsegs;VC;Vrho0;VFB;R7A5F_;F_;F_;F_;F_;F_;Fa;Fo;G2S8eVNP;Vrho0;R7A3S8dS6ScR8A1S5RaA1A3S37S9dS9eVUv;R9R10A2M4Z18A2VUv;R9RdA2M5A2S9dS9eG5VUv;R9RcA2A2S9eS9eG4S113A2VUv;R9ReA2A2A2A2F_;F_;F_;S5dVsegs;S6cRfS54ReRdRcG1A4A2R9R7R6A5S5dVsegs;S6cR10S54RfReRdS45G0S42S0S0RcRbA4G1A3A4A2S81RaRcRbA3R8R7A5F_;F_;F_;F_;F_;F_;Fw;Frho;Fextra;FS;Fsz;Fp;Fcap;Fnx;Fhd;Ftv;").
Proof using ML HNP.
  intros tv hd nx cap p sz S extra rho w Hwf Hnp Hrc Hext Hside [Hsm [Ai [HJ HX]]].
  destruct w as [tr [ms md]]. apply Pos.leb_le in Hnp.
  pose proof HJ as (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
  pose proof (MI1 segs C _ _ _ _ HM) as HMr.
  pose proof (smatch_facts_hold segs _ _ _ Hsm) as HF.
  destruct (Hside HP0 Hav HF) as [S1 S2]. unfold Uv in S1, S2.
  pose proof HX as HX0. cbn -[HDR] in HX. unfold Uv in HX. destruct HX as (X1 & X2 & X3 & X4 & X5 & X6 & _ & ns & HA & HNS & Hnin).
  set (h := bv_unsigned (eval rho hd)) in *. set (c := bv_unsigned (eval rho cap)) in *.
  set (pp := bv_unsigned (eval rho p)) in *. set (z := bv_unsigned (eval rho sz)) in *.
  pose proof (block_geom Ai rho md h (HDR + c) HMr X3) as (G0 & G1 & G2 & G3 & G4). unfold HDR, aceil in G3. unfold HDR in S2.
  pose proof (urange (eval rho sz)) as Rz. fold z in Rz.
  split.
  - unfold carve_state. apply (smatch_carve_plain rho S _ p sz (ss_next S) Hsm Hwf); fold pp z; [lia|lia| |].
    +
      apply Forall_forall. intros o Ho.
      unfold robjs_check in Hrc. pose proof (proj1 (forallb_forall _ _) Hrc o Ho) as Hco. cbv beta in Hco.
      assert (CL : (robj_stack (ss_facts S) o ||| (robj_tracked tv None o ||| extra o)) = true \/ hdr_obj (AOpen hd nx cap []) o = true).
      { destruct (robj_stack (ss_facts S) o); [left; reflexivity|]. destruct (robj_tracked tv None o); [left; reflexivity|].
        destruct (hdr_obj (AOpen hd nx cap []) o); [right; reflexivity|]. left. exact Hco. }
      destruct CL as [CL|CL].
      * assert (HRF : robjs_okF segs C rho0 FB rho tv [o]).
        { eapply (robjs_checkF_sound segs C rho0 FB rho (ss_facts S) tv extra [o] HF (T_ok_T0 rho Ai Hav (proj2 (proj2 HM))) HZ).
          - unfold robjs_check. cbn [forallb]. rewrite CL. reflexivity.
          - intros o' a [<-|[]] Hx Hr. apply pclF_FBx. exact (Hext o a Ho Hx HP0 Hav HF Hr). }
        exact (Forall_inv (robjs_okF_disjoint Ai rho md tv [o] h (HDR + c) pp (pp + z) HMr (proj2 (proj2 HM)) HP HN X3 X4 X5 HRF ltac:(lia) ltac:(unfold HDR; lia))).
      *         destruct (obj_range rho o) as [lo hi] eqn:Er. apply ranges_disjoint_by_points. cbn [fst snd]. intros a Ha1 Ha2.

        cbn -[sv_eqb] in CL.
        destruct (sv_eqb (ob_base o) hd) eqn:Hb; [|discriminate]. destruct (sv_eqb (ob_lo o) (SLit 0)) eqn:Hl; [|discriminate].
        destruct (sv_eqb (ob_hi o) (SLit 24)) eqn:Hh; [|discriminate].
        apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
        unfold obj_range, obj_lo_of, obj_hi_of in Er. rewrite Hb, Hl, Hh in Er. rewrite !soff_lit_small in Er by lia.
        injection Er as E1 E2. fold h in E1, E2. lia.
    + intros q Hq. destruct (rm rho (Z_to_bv 64 q)) as [x|] eqn:Ex; [exists x; reflexivity|].
      exfalso. apply (X6 q); [unfold HDR; lia | exact Ex].
  - exists Ai. split; [exact HJ|].
    cbn -[HDR]. unfold Uv. fold h c pp z. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
    split; [exact X6|]. split.
    + constructor; [|constructor]. cbn [fst snd]. fold pp z. unfold HDR in *. lia.
    + exists ns. split; [exact HA|]. split; [exact HNS | exact Hnin].
Qed.

Lemma JGA_unslot : ltac2:(tb__ "0|4|
S41S3fS0S0A2M0A1S0S0S0S0S0S1S41S4A1M1S4S2Sa9S36G1S10R5A1S47S4R4S45S4R3S4bS4A1A3A3A3S36S3eS3eS3eL_;M2S7S13R4A1R8A2G2S7S16R4A1S8Z0A1A2G2S7S15R4A1R7A2S1eS1fR4A1A1S49X3ex2S49X3ex2S49X3ex2S40A3S36S3eS12S73R7R6A2A1S40A3S5dVsegs;S6cReS54RdRcRbS45G0S42S0S0RaR9A4S4bG0A1M3A3A4A2R8R5R4A5S38S2S2S37S8eS3RaA1R7R1A3S5dVsegs;S6cR10S54RfReRdG3A4A2S73RaR9A2R1R6A5A2Lrho';A2F_;F_;F_;F_;Fw;Frho;Fo;Fobjs;FS;Fsz;Fp;Fcap;Fnx;Fhd;Ftv;").
Proof using ML.
  intros tv hd nx cap p sz S objs o rho w Hobjs Hsh Hwf [Hsm [Ai [HJ HX]]].
  destruct w as [tr [ms md]].
  pose proof HJ as (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
  pose proof (MI1 segs C _ _ _ _ HM) as HMr.
  apply lazy_andb_prop in Hsh as [Hb Hsh]. apply lazy_andb_prop in Hsh as [Hl Hsh]. apply lazy_andb_prop in Hsh as [Hh Hdw].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  cbn -[HDR] in HX. unfold Uv in HX. destruct HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & ns & HA & HNS & Hnin).
  pose proof (Forall_inv X7) as [S1 S2]. cbn [fst snd] in S1, S2.
  set (h := bv_unsigned (eval rho hd)) in *. set (c := bv_unsigned (eval rho cap)) in *.
  set (pp := bv_unsigned (eval rho p)) in *. set (z := bv_unsigned (eval rho sz)) in *.
  pose proof (block_geom Ai rho md h (HDR + c) HMr X3) as (G0 & G1 & G2 & G3 & G4). unfold HDR, aceil in G3. unfold HDR in S2.
  pose proof (urange (eval rho sz)) as Rz. fold z in Rz.
  assert (Hrng : obj_range rho o = (pp, pp + z)).
  { unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb, Hl, Hh. rewrite soff_lit_small by lia. fold pp.
    unfold soff. rewrite bv_signed_U. fold z. destruct (Zsigned_spec z) as [[_ X]|[X _]]; [rewrite X; f_equal; lia | lia]. }
  destruct (smatch_release_obj segs rho S (tr, mkCfg ms md) objs o (ss_next S) Hsm Hobjs Hwf) as (m' & Hsm' & Mout & Min & Hoh & _).
  cbn [cfg_ms w_cfg snd] in Min, Hoh.
  exists (set_rm rho m'). split; [split; intros; reflexivity|].
  split; [exact Hsm'|].
  destruct (released_bytes Ai rho md ms h (HDR + c) o m' HMr X3 ltac:(rewrite Hrng; cbn; lia) ltac:(rewrite Hrng; cbn; unfold HDR; lia) Hoh Hdw Min) as [BY _].
  rewrite Hrng in BY. cbn [fst snd] in BY.
  assert (Mout' : forall a, ~ (pp <= bv_unsigned a < pp + z) -> m' a = rm rho a).
  { intros a Ha. apply Mout. rewrite Hrng. unfold in_rng. cbn [fst snd]. exact Ha. }
  destruct (J_set_rm_block Ai rho md h (HDR + c) pp (pp + z) m' HM HP X3 X4 ltac:(lia) ltac:(unfold HDR; lia) Mout' HK) as [HM' HK'].
  exists Ai. split.
  - split; [exact Hav|]. split; [exact Hk|]. split; [exact HM'|]. split; [exact HP|]. split; [|split; [exact HK' | exact HP0]].
    apply tvs_set_rm. exact (conj HN (conj HD HZ)).
  - cbn -[HDR]. unfold Uv. rewrite !eval_set_rm. fold h c. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split.
    + intros t Ht Hnz. rewrite tvv_set_rm. apply (X5 t Ht). apply (proj1 (tnz_set_rm rho m' t)). exact Hnz.
    + split.
      { intros q Hq. cbn [set_rm rm]. unfold HDR in *. destruct (Z_lt_dec q pp) as [|Hge]; [|destruct (Z_lt_dec q (pp + z)) as [Hlt|]].
        - rewrite Mout' by (rewrite u64_of_sum by lia; lia). apply X6. lia.
        - destruct (BY q ltac:(lia)) as (x & Hx & _). rewrite Hx. discriminate.
        - rewrite Mout' by (rewrite u64_of_sum by lia; lia). apply X6. lia. }
      split; [constructor|].
      exists ns. split; [|split; [apply nodes_ok_set_rm; exact HNS | exact Hnin]].
      destruct HNS as [HFns _].
      eapply achain_frame; [exact HA| |].
      * intros q (b & cp & Hinb & Hq). cbn [set_rm rm].
        destruct (proj1 (Forall_forall _ _) HFns _ Hinb) as (B1 & _). cbn [fst snd] in B1.
        pose proof (block_geom Ai rho md b (HDR + cp) HMr B1) as (_ & _ & B2 & B3 & _). unfold aceil, HDR in B3.
        pose proof (proj1 (Forall_forall _ _) (achain_caps _ _ _ HA) _ Hinb) as [Bc _]. cbn in Bc.
        apply Mout'. rewrite u64_of_sum by lia. intros Hq'.
        apply (blocks_disjoint Ai rho md h (HDR + c) b (HDR + cp) q HMr X3 B1); [|unfold HDR; lia|unfold HDR; lia].
        intros Heq. injection Heq as E1 E2. apply Hnin. apply in_map_iff. exists (b, cp). split; [cbn; lia | exact Hinb].
      * intros q (b & cp & Hinb & Hq) Hdef. cbn [set_rm rm].
        destruct (proj1 (Forall_forall _ _) HFns _ Hinb) as (B1 & _). cbn [fst snd] in B1.
        pose proof (block_geom Ai rho md b (HDR + cp) HMr B1) as (_ & _ & B2 & B3 & _). unfold aceil, HDR in B3.
        pose proof (proj1 (Forall_forall _ _) (achain_caps _ _ _ HA) _ Hinb) as [Bc _]. cbn in Bc.
        rewrite Mout'; [exact Hdef|]. rewrite u64_of_sum by (unfold HDR in Hq; lia). intros Hq'.
        apply (blocks_disjoint Ai rho md h (HDR + c) b (HDR + cp) q HMr X3 B1); [|unfold HDR; lia|lia].
        intros Heq. injection Heq as E1 E2. apply Hnin. apply in_map_iff. exists (b, cp). split; [cbn; lia | exact Hinb].
Qed.

Lemma JGA_push_open : ltac2:(tb__ "0|6|
S41S3fS0S0A2M0A1S4cG0S0S0S0S1S41S4A1M1S4S4S2Sa9S36G1S10R6A1S47S4S47S4R5S45S4R4S4bS4A1M2A3A3S45S4R3G2A3A3A3S36S43G0A1S66G0RdRcA3S46G0RbA2A3S36S3eS83R6S44S0S0RcA3RbRaR9A5S40A3S36S3eS3eS3eL_;M3S7S13R6A1S44S0S0RdA3A2G3S7S16R6A1S8Z18A1A2G3S7S15R6A1S48S0S0RdA3A2S1eS1fR6A1A1S49X3ex2S49X3ex2S49X3ex2S40A3S36S3eSf2S5RaA1S48S0S0ReA3Z0M4S1bS117RcS8Z20A1M5A3A4S40A3S36S3eSf2S5RbA1S1bS117RdG5A3G4S48S0S0RfA3A4S40A3S36S3eSf2S5RcA1ReG4S8Z7fffff800000A1A4S40A3S36S3eS68S6S1aS1dS1cS118S44S0S0R11A3S8G4A1A3A1A1S5RdA1A3S40A3S36S3eS12S73ReS47S4RdS45S4RcG2A3A3A2A1S40A3S5dVsegs;S6cR15S55R12A1A2RfRbRaA5S38S2S2S37S8eS3R11A1RdR1A3S5dVsegs;S6cSc6G0R16R17A3S54S44S0S0R15A3R14R13S4bG0A1A4A2S73R11S47S4R10S45S4RfG2A3A3A2R1RcA5A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Frho;Fot;Foh;Fobjs;FS;FuE;FcapE;Fhd;Ft;Fi;Ftv;").
Proof using ML.
  intros tv i t hd capE uE S objs oh ot rho w Hobjs Hnth Hsh Hot Hu1 Hu2 Hu3 Hnz Hwf [Hsm [Ai [HJ HX]]].
  destruct w as [tr [ms md]].
  pose proof HJ as (Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0).
  pose proof (MI1 segs C _ _ _ _ HM) as HMr.
  pose proof (smatch_facts_hold segs _ _ _ Hsm) as HF.
  apply lazy_andb_prop in Hot as [Hb Hot]. apply lazy_andb_prop in Hot as [Hl Hot]. apply lazy_andb_prop in Hot as [Hh Hdw].
  apply sv_eqb_sound in Hb. apply sv_eqb_sound in Hl. apply sv_eqb_sound in Hh.
  cbn -[HDR] in HX. unfold Uv in HX. destruct HX as (ns & HA & HNS).
  destruct t as [d tot]. cbn [fst snd] in *.
  set (dd := bv_unsigned (eval rho d)) in *. set (tt := bv_unsigned (eval rho tot)) in *. set (c := bv_unsigned (eval rho capE)) in *.
  pose proof (tnz_of_fact rho d tot (holds_fact_in rho S _ _ Hsm Hnz)) as Tnz.
  pose proof (nth_error_In _ _ Hnth) as Tin.
  destruct (proj1 (Forall_forall _ _) HN _ Tin Tnz) as (Tpos & Tblk & Tnfb). unfold tvv in Tpos, Tblk, Tnfb. cbn [fst snd] in Tpos, Tblk, Tnfb. fold dd tt in Tpos, Tblk, Tnfb.
  pose proof (uleq_sound rho (ss_facts S) _ 0 _ HF Hu1) as U1. pose proof (uleq_sound rho (ss_facts S) _ 0 _ HF Hu2) as U2.
  pose proof (uleq_sound rho (ss_facts S) _ 0 _ HF Hu3) as U3. unfold U in U1, U2, U3.
  rewrite U_add, U_lit in U1, U2. rewrite U_lit in U3. fold tt c in U1, U2, U3. unfold M64v, aceil in U1, U2, U3.
  rewrite (Z.mod_small 32) in U1, U2 by lia. rewrite (Z.mod_small 0x7fffff800000) in U3 by lia.
  pose proof (urange (eval rho capE)) as Rc. fold c in Rc. pose proof (urange (eval rho tot)) as Rt. fold tt in Rt.
  rewrite Z.mod_small in U1, U2 by lia.
  assert (Htt : tt = HDR + c) by (unfold HDR; lia).
  pose proof (block_geom Ai rho md dd tt HMr Tblk) as (G0 & G1 & G2 & G3 & G4). unfold aceil in G3.
  assert (Hrng : obj_range rho ot = (dd + 24, dd + tt)).
  { unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb, Hl, Hh. rewrite soff_lit_small by lia. fold dd.
    unfold soff. rewrite bv_signed_U. fold tt. destruct (Zsigned_spec tt) as [[_ X]|[X _]]; [rewrite X; f_equal; lia | lia]. }
  destruct (smatch_release_obj segs rho S (tr, mkCfg ms md) (objs ++ [oh]) ot (ss_next S) Hsm Hobjs Hwf) as (m' & Hsm' & Mout & Min & Hoh & _).
  cbn [cfg_ms w_cfg snd] in Min, Hoh.
  exists (set_rm rho m'). split; [split; intros; reflexivity|].
  split; [exact Hsm'|].
  destruct (released_bytes Ai rho md ms dd tt ot m' HMr Tblk ltac:(rewrite Hrng; cbn; lia) ltac:(rewrite Hrng; cbn; lia) Hoh Hdw Min) as [BY _].
  rewrite Hrng in BY. cbn [fst snd] in BY.
  assert (Mout' : forall a, ~ (dd + 24 <= bv_unsigned a < dd + tt) -> m' a = rm rho a).
  { intros a Ha. apply Mout. rewrite Hrng. unfold in_rng. cbn [fst snd]. exact Ha. }
  destruct (J_set_rm_block Ai rho md dd tt (dd + 24) (dd + tt) m' HM HP Tblk Tnfb ltac:(lia) ltac:(lia) Mout' HK) as [HM' HK'].

  assert (UT : forall t', In t' (remove_nth i tv) -> tnz rho t' -> tvv rho t' <> (dd, tt)).
  { intros t' Ht' Hnz'. change (dd, tt) with (tvv rho (d, tot)). exact (tvd_nth_distinct rho tv i (d, tot) t' HD Hnth Ht' Tnz Hnz'). }
  exists Ai. split.
  - split; [exact Hav|]. split; [exact Hk|]. split; [exact HM'|]. split; [exact HP|]. split; [|split; [exact HK' | exact HP0]].
    apply tvs_set_rm. split; [|split; [apply tvd_remove; exact HD|]].
    + unfold tvin in *. apply Forall_forall. intros t' Ht'. apply (proj1 (Forall_forall _ _) HN). eapply remove_nth_In. exact Ht'.
    + unfold tvz in *. apply Forall_forall. intros t' Ht'. apply (proj1 (Forall_forall _ _) HZ). eapply remove_nth_In. exact Ht'.
  - cbn -[HDR]. unfold Uv. rewrite !eval_set_rm. fold dd c. rewrite <- Htt.
    split; [exact Tnz|]. split; [pose proof (urange (eval rho capE)); lia|]. split; [exact Tblk|]. split; [exact Tnfb|]. split.
    + intros t' Ht' Hnz'. rewrite tvv_set_rm. apply (UT t' Ht'). apply (proj1 (tnz_set_rm rho m' t')). exact Hnz'.
    + split.
      { intros q Hq. destruct (BY q ltac:(lia)) as (x & Hx & _). rewrite Hx. discriminate. }
      split; [constructor|].
      exists ns. destruct HNS as [HFns HNDns]. split; [|split].
      * eapply achain_frame; [exact HA| |].
        -- intros q (b & cp & Hinb & Hq). cbn [set_rm rm].
           destruct (proj1 (Forall_forall _ _) HFns _ Hinb) as (B1 & _ & B3). cbn [fst snd] in B1, B3.
           pose proof (block_geom Ai rho md b (HDR + cp) HMr B1) as (_ & _ & B2 & B4 & _). unfold aceil, HDR in B4.
           pose proof (proj1 (Forall_forall _ _) (achain_caps _ _ _ HA) _ Hinb) as [Bc _]. cbn in Bc.
           apply Mout'. rewrite u64_of_sum by lia. intros Hq'.
           apply (blocks_disjoint Ai rho md dd tt b (HDR + cp) q HMr Tblk B1); [|lia|unfold HDR; lia].
           intros Heq. apply (B3 (d, tot) Tin Tnz). unfold tvv. cbn [fst snd]. fold dd tt. first [exact Heq | symmetry; exact Heq].
        -- intros q (b & cp & Hinb & Hq) Hdef. cbn [set_rm rm].
           destruct (proj1 (Forall_forall _ _) HFns _ Hinb) as (B1 & _ & B3). cbn [fst snd] in B1, B3.
           pose proof (block_geom Ai rho md b (HDR + cp) HMr B1) as (_ & _ & B2 & B4 & _). unfold aceil, HDR in B4.
           pose proof (proj1 (Forall_forall _ _) (achain_caps _ _ _ HA) _ Hinb) as [Bc _]. cbn in Bc.
           rewrite Mout'; [exact Hdef|]. rewrite u64_of_sum by (unfold HDR in Hq; lia). intros Hq'.
           apply (blocks_disjoint Ai rho md dd tt b (HDR + cp) q HMr Tblk B1); [|lia|lia].
           intros Heq. apply (B3 (d, tot) Tin Tnz). unfold tvv. cbn [fst snd]. fold dd tt. first [exact Heq | symmetry; exact Heq].
      * apply nodes_ok_set_rm. split; [|exact HNDns]. apply Forall_forall. intros bc Hbc.
        destruct (proj1 (Forall_forall _ _) HFns bc Hbc) as (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|].
        intros t' Ht' Hnz'. apply B3; [eapply remove_nth_In; exact Ht' | exact Hnz'].
      * intros Hin. apply in_map_iff in Hin as ([b cp] & Hb' & Hinb). cbn in Hb'. subst b.
        destruct (proj1 (Forall_forall _ _) HFns _ Hinb) as (B1 & _ & B3). cbn [fst snd] in B1, B3.
        pose proof (proj1 (Forall_forall _ _) (achain_caps _ _ _ HA) _ Hinb) as [Bc _]. cbn in Bc.
        apply (blocks_bases_differ segs C Ai rho md dd tt dd (HDR + cp) HMr Tblk B1); [|lia|unfold HDR; lia|reflexivity].
        intros Heq. apply (B3 (d, tot) Tin Tnz). unfold tvv. cbn [fst snd]. fold dd tt. first [exact Heq | symmetry; exact Heq].
Qed.

End Sum.

Section PostsA.
Variable NP : positive.
Variable Kc : ltac2:(tb__ "0|0|
S41S6bA1S6aOF_;F_;").
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).

Definition JLGA (tv : list (sv * sv)) (am : amode) : jpost := ltac2:(tb__ "0|0|
S2S2S41S6bA1S6aS38SacSacS37S37VKc;R3R2A2S37S37SdcVsegs;VC;R1R4R2A5S37Sd1R1A1Sc4VC;R5R1A3A2A2S37SbcVFB;R1A2S37S37SbeVFB;R1R4Vtv;A4S37Sc1R4Vtv;A2Sc2R4Vtv;A2A2A2S37Sd2Vsegs;VC;R5VFB;SaR5A1SaR4A1A6VP0f;R5A1A2A2A2A2A2S10cVFB;Vam;R1R4Vtv;A5A2LAi;A2Lmd;Ltr;Lrho;Lr0;").

Lemma JLGA_JLG : ltac2:(tb__ "0|0|
S41S3fS0S0A2A1S51S2S2S41S6bA1S6aS11bR6R5R4R3R2R1A6Sd7Vsegs;VC;VKc;VP0f;VFB;R7R5R4R3R2AaF_;Fmd;Ftr;Frho;Fr0;Fam;Ftv;").
Proof using . intros tv am r0 rho tr md (Ai & (Hk & HM & HP & HN & HK & HP0) & _). split; [exact Hk|]. exists Ai. auto 10. Qed.

Lemma exit_postGA : ltac2:(tb__ "0|1|
Sa9OF_;S2S41S3fS0S0A2A1S51S41S3fS1S8fA2M0A1S1Sa8S65G0S42S1S8fR2S11bR5R4A2A4R3A3S2SaaVsegs;R9S5dVsegs;S10bVNP;VKc;R8VP0f;VFB;R7R6A7R4R1A4Sa9S3aR4R1A1S90Vsegs;VNP;R9R6R1A5A2Lw;A4Frho;F_;FX;FP;FPosts;Fam;Ftv;Frho0;Fok;").
Proof using .
  intros ok rho0 tv am Posts P X Hin. apply (exit_postP segs ok _ NP rho0 Posts P (JLGA tv am) X Hin).
  intros rho tr md (Ai & (Hav & Hk & HM & HP & HN & HK & HP0) & HX). split; [exact Hav|].
  exists Ai. split; [|exact HX]. auto 10.
Qed.

Lemma eexit_postGA : ltac2:(tb__ "0|1|
S2S41S3fS0S0A2A1S51S41S3fS1S8fA2M0A1S1Sa8S65G0S42S1S8fR2S11bR5R4A2A4R3A3S2SabVsegs;S5dVsegs;S10bVNP;VKc;R8VP0f;VFB;R7R6A7R4R1A4Sa9S3aR4R1A1S90Vsegs;VNP;R9R6R1A5A2Lw;A3Frho;F_;FX;FP;FPosts;Fam;Ftv;Frho0;").
Proof using .
  intros rho0 tv am Posts P X Hin. apply (eexit_postP segs _ NP rho0 Posts P (JLGA tv am) X Hin).
  intros rho tr md (Ai & (Hav & Hk & HM & HP & HN & HK & HP0) & HX). split; [exact Hav|].
  exists Ai. split; [|exact HX]. auto 10.
Qed.

Definition JGA_pre (tv : list (sv * sv)) (am : amode) : jpred := ltac2:(tb__ "0|0|
S2S41S6bA1S6aS11bVtv;Vam;R3R3R2R1A6Lmd;Ltr;Lrho;").

Lemma JGA_pre_intro : ltac2:(tb__ "0|0|
S2S41S3fS0S0A2A1S51S1Sa9S5dVsegs;S11cR4R3A2R2R5R1A5S5dVsegs;S10bVNP;VKc;R6VP0f;VFB;R5R4A7R3R6R2A5F_;Fw;FS;Fam;Ftv;Frho0;").
Proof using .
  intros rho0 tv am S w [Hsm (Ai & (Hk & HM & HP & HN & HK & HP0) & HX)]. split; [exact Hsm|].
  exists Ai. split; [|exact HX]. split; [apply agree_vals_refl|]. auto 10.
Qed.

Lemma JGA_pre_none : ltac2:(tb__ "0|0|
S41S3fS0S0A2A1S2S41S6bA1S6aS3bS11cR4S57R3R2R1A5ScbVsegs;VC;VKc;VP0f;VFB;R4R3R2R1A9A2Fmd;Ftr;Frho;Ftv;").
Proof using .
  intros tv rho tr md. split.
  - intros (Ai & (Hk & H) & _). split; [exact Hk|]. exists Ai. exact H.
  - intros (Hk & Ai & H). exists Ai. split; [|exact I]. split; [exact Hk|]. exact H.
Qed.
End PostsA.

Section ClientA.
Variable NP : positive.
Variable Kc : ltac2:(tb__ "0|0|
S41S6bA1S6aOF_;F_;").
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Hypothesis ML : malloc_laws segs C.
Hypothesis HNP : NP_ok NP.

Variable P0c : ltac2:(tb__ "0|0|
S41S3fS33S33A2A1S2OF_;F_;").
Variable PreC : sstate.
Variable tvC : list (sv * sv).
Variable amC : amode.
Variable PDA : ltac2:(tb__ "0|0|
S41S3fS1S3fS41S3fS0S0A2A1S51A2A2A1").
Definition PostsCA (FBc : list (Z * Z)) : list (sstate * jpost) := ltac2:(tb__ "0|4|
S8cS3fS1S3fS41S3fS0S0A2A1M0S51A2M1A2M2S3fS1S8fA2G2S42S1S8fS44S1G1R1A3S110VKc;VP0c;VFBc;A1VFBc;S44G0S51S48S1G1R1A3M3A3S48G0S51G3A3A5A4Ld;VPDA;A4").
Variable NPc : positive.
Hypothesis HnextPre : ltac2:(tb__ "0|0|
S36S34S3VPreC;A1VNPc;A3").

Let Uv (rho : valuation) (e : sv) : Z := bv_unsigned (eval rho e).

Definition new_objs_okA (L : sstate) (tvL : list (sv * sv)) (amL : amode) : bool := ltac2:(tb__ "0|1|
S67S4S4S4fS68S3fS0S0A2M0G0S4aS4aS7S13R2A1S44S0S0R1A3A2S7S16R2A1S8Z0A1A2A2S7S15R2A1S48S0S0R1A3A2A2Lt;VtvL;A3S111VamL;R1A2A2Lo';S9bVPreC;VL;A2A3").
Definition amL_ok (s : wsub) (nc : positive) (L : sstate) (amL : amode) : bool := ltac2:(tb__ "0|0|
S67S0S9cSd8VNPc;Vs;Vnc;VL;A4A1S10fVamL;A1A3").

Lemma pclF_mono : ltac2:(tb__ "0|2|
S2S41S3fS33S33A2M0A1M1G1S33G0S65G0R1R4A3S65G0R2R4A3F_;Fbn;Sc0Vsegs;VC;R5R4R2A5Sc0Vsegs;VC;R6R4R3A5F_;F_;Fa;FF2;FF1;Fr;").
Proof using .
  clear. intros r F1 F2 a Hs [H|[H|(b & n & Hin & Hr)]]; [left; exact H | right; left; exact H | right; right].
  exists b, n. split; [exact (Hs _ Hin) | exact Hr].
Qed.
Lemma FBx_kept_sub : ltac2:(tb__ "0|3|
S2S41S3fS0S0A2M0A1M1G1S3fS33S33A2M2S65G2R1Sc3VFB;R4R3A3A3S65G2R2Sc3VFB;R5S47G0R4R3A3A3A3F_;Fbn;Fpassed;Fkept;Frho;").
Proof using .
  clear. intros rho kept passed bn H. apply In_FBx in H as [H|(t & Ht & Hnz & Heq)]; apply In_FBx; [left; exact H|right].
  exists t. split; [apply in_or_app; left; exact Ht|]. auto.
Qed.

Lemma XA_import : ltac2:(tb__ "0|8|
S41S3fS33S33A2M0A1M1S51SacS2S2S6aS41S3fS0S0A2M2A1M3G3G3Sb0SdcVsegs;VC;R8R7R5A5SbcRbR9A2G0S65G0R1VFB;A3S65G0R2ReA3F_;Fbn;S10cRdRcRbRaR7A5S0S65S0R1S10fReA1A3S36Sb5Q40M4A1SbRcSb3R7R2A2A2SbRdR2A2A3F_;Fe;S36G1S8cG2G0SbaRbA1R8A4S8cG2G0SbaRcA1R9A4A3S4cG2G2S36S43G2A1M5S66G2RdR3A3S46G2R2A2M6A3S36G5S66G2RdR4A3G6A3S3bSb9R11R3A2Sb9R12R4A2A2F_;F_;Ft';Ft;Fk;G2S65G2R1RaA3Sb9RfR2A2S65G0SbaR10R3A2R14A3F_;F_;Ft;S33S33S33S65G0S42S33S33R2R1A4SadR13A1A3S39S65G0S42S33S33R3R2A4R16A3A1S37S9dR4R5A2S9fR5S9eR4R3A2A2A2S36S43Sb5Q8A1A1SaR14Sb7G4R6A2M7A2SaR15G7A2A3F_;F_;F_;Fn;Fb;Fz;S10cVFB;S53RaR12A2R11RfS47G2RbRcA3A5F_;F_;F_;F_;F_;F_;F_;F_;F_;Fisub;Fkept;Ftv2;FtvL;Fmd;Frho2;FrhoL;FA2;Fam;FFBc;").
Proof using .
  clear - ML HNP Uv. intros FBc am A2 rhoL rho2 md tvL tv2 kept isub HM HPc Hsub HX Hvals M1 M2 Hkept Hrm.
  assert (UT : forall b n, ~ In (b, n) FBc -> (forall t, In t tvL -> tnz rhoL t -> tvv rhoL t <> (b, n)) ->
               forall t, In t (kept ++ tv2) -> tnz rho2 t -> tvv rho2 t <> (b, n)).
  { intros b n Hnfb Hut t Ht Hnz. apply in_app_or in Ht as [Ht|Ht].
    - intros Heq. apply Hnfb. rewrite <- Heq. exact (Hkept t Ht Hnz).
    - destruct (In_nth_error _ _ Ht) as [k Hk'].
      assert (exists t0, nth_error tvL k = Some t0) as [t0 Hk].
      { pose proof (Forall2_map_eq _ _ _ _ M1) as L. destruct (nth_error tvL k) eqn:En; [eexists; reflexivity|].
        exfalso. apply nth_error_None in En. assert (k < length tv2)%nat by (apply nth_error_Some; congruence). lia. }
      rewrite (map_nth2 _ _ _ _ k t0 t M1 Hk Hk'). apply (Hut t0 (nth_error_In _ _ Hk)). apply (proj1 (M2 k t0 t Hk Hk')). exact Hnz. }
  assert (NOK : forall ns, nodes_ok FBc A2 rhoL tvL ns -> nodes_ok FB A2 rho2 (kept ++ tv2) ns).
  { intros ns [HF HD]. split; [|exact HD]. apply Forall_forall. intros [b cap] Hin.
    destruct (proj1 (Forall_forall _ _) HF _ Hin) as (H1 & H2 & H3). cbn [fst snd] in *.
    split; [exact H1|]. split; [intros Hin'; exact (H2 (Hsub _ Hin'))|]. exact (UT _ _ H2 H3). }
  assert (ACH : forall ns h, nodes_ok FBc A2 rhoL tvL ns -> achain (rm rhoL) h ns -> achain (rm rho2) h ns).
  { intros ns h [HF _] HA. eapply achain_frame; [exact HA| |].
    - intros z (b & cap & Hin & Hz). destruct (proj1 (Forall_forall _ _) HF _ Hin) as (H1 & H2 & _). cbn [fst snd] in *.
      pose proof (proj1 (Forall_forall _ _) (achain_caps _ _ _ HA) _ Hin) as [Hc _]. cbn in Hc.
      apply (Hrm z b (HDR + cap) H1 H2). unfold HDR. lia.
    - intros z (b & cap & Hin & Hz) Hdef. destruct (proj1 (Forall_forall _ _) HF _ Hin) as (H1 & H2 & _). cbn [fst snd] in *.
      rewrite (Hrm z b (HDR + cap) H1 H2 ltac:(lia)). exact Hdef. }
  destruct am as [|hd|hd nx cap sl|hd g]; cbn -[HDR flat_map pl_subst] in HX |- *.
  - exact I.
  - rewrite (Hvals hd ltac:(left; reflexivity)). destruct HX as (ns & HA & HN). exists ns. split; [exact (ACH ns _ HN HA) | exact (NOK ns HN)].
  - cbn -[HDR flat_map] in Hvals.
    rewrite (Hvals hd ltac:(auto)), (Hvals nx ltac:(auto)), (Hvals cap ltac:(auto)).
    destruct HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & ns & HA & HN & Hnin).
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [intros Hin'; exact (X4 (Hsub _ Hin'))|].
    split; [exact (UT _ _ X4 X5)|]. split.
    + intros z Hz. rewrite (Hrm z _ _ X3 X4); [exact (X6 z Hz) | unfold HDR in *; lia].
    + split.
      * unfold pl_subst. apply Forall_map. apply Forall_forall. intros ps Hps. cbn [fst snd].
        pose proof (proj1 (Forall_forall _ _) X7 ps Hps) as Y. cbv beta in Y.
        assert (Hin2 : forall e, In e [fst ps; snd ps] -> In e ([hd; nx; cap] ++ flat_map (fun ps0 => [fst ps0; snd ps0]) sl)).
        { intros e He. apply in_or_app. right. apply in_flat_map. exists ps. split; [exact Hps | exact He]. }
        rewrite (Hvals (fst ps) (Hin2 _ ltac:(left; reflexivity))), (Hvals (snd ps) (Hin2 _ ltac:(right; left; reflexivity))). exact Y.
      * exists ns. split; [exact (ACH ns _ HN HA)|]. split; [exact (NOK ns HN) | exact Hnin].
  - rewrite (Hvals hd ltac:(left; reflexivity)), (Hvals g ltac:(right; left; reflexivity)).
    destruct HX as (ns & HA & HN & HL). exists ns. split; [exact (ACH ns _ HN HA) |]. split; [exact (NOK ns HN) | exact HL].
Qed.

Lemma XA_export : ltac2:(tb__ "0|7|
S51Sb0SacS2S2S6aS41S3fS0S0A2M0A1M1G1G1SdcVsegs;VC;R7R6R4A5SbcVFB;R8A2SbeVFB;R9R8S47G0R5R4A3A4S10cVFB;S53RbRcA2RaR9S47G0R6R5A3A5S0S36Sb5Q40M2A1SbRaR1A2SbRbSb3RdR1A2A2A3Fe;S36S41S3fS33S33A2M3A1S8cG0G3SbaRaA1R6A4S8cG0G3SbaRbA1R7A4A3S4cG0G0S36S43G0A1M4S66G0RbR3A3S46G0R2A2M5A3S36G4S66G0RbR4A3G5A3S3bSb9R10R3A2Sb9R11R4A2A2F_;F_;Ft';Ft;Fk;S33S33S33S65G3S42S33S33R2R1A4SadR11A1A3S39S65G3S42S33S33R3R2A4VFB;A3A1S112R12S47G0RfReA3S42S33S33R4R3A4A3S37S9dR5R6A2S9fR6S9eR5R4A2A2A2S36S43Sb5Q8A1A1SaR13Sb7G2R7A2M6A2SaR14G6A2A3F_;F_;F_;F_;Fn;Fb;Fz;S10cSc3VFB;ReRbA3R11RfRdR9A5F_;F_;F_;F_;F_;F_;F_;F_;FtvCe;Fpassed;Fkept;Fmd;Frho1;Frho;FAi;Fs;FamCe;").
Proof using .
  clear - ML HNP Uv. intros amCe s Ai rho rho1 md kept passed tvCe HM HP HN HX EV M1 M2 Hrm.
  assert (NFX : forall b n, ~ In (b, n) FB -> untracked rho (kept ++ passed) (b, n) -> ~ In (b, n) (FBx FB rho kept)).
  { intros b n Hnfb Hut Hin. apply In_FBx in Hin as [Hin|(t & Ht & Hnz & Heq)]; [exact (Hnfb Hin)|].
    exact (Hut t ltac:(apply in_or_app; left; exact Ht) Hnz Heq). }
  assert (UT : forall b n, untracked rho (kept ++ passed) (b, n) -> forall t, In t tvCe -> tnz rho1 t -> tvv rho1 t <> (b, n)).
  { intros b n Hut t Ht Hnz. destruct (In_nth_error _ _ Ht) as [k Hk'].
    assert (exists tp, nth_error passed k = Some tp) as [tp Hk].
    { pose proof (Forall2_map_eq _ _ _ _ M1) as L. destruct (nth_error passed k) eqn:En; [eexists; reflexivity|].
      exfalso. apply nth_error_None in En. assert (k < length tvCe)%nat by (apply nth_error_Some; congruence). lia. }
    rewrite (map_nth2 _ _ _ _ k tp t M1 Hk Hk'). apply (Hut tp ltac:(apply in_or_app; right; exact (nth_error_In _ _ Hk))).
    apply (proj1 (M2 k tp t Hk Hk')). exact Hnz. }
  assert (NOK : forall ns, nodes_ok FB Ai rho (kept ++ passed) ns -> nodes_ok (FBx FB rho kept) Ai rho1 tvCe ns).
  { intros ns [HF HD]. split; [|exact HD]. apply Forall_forall. intros [b cap] Hin.
    destruct (proj1 (Forall_forall _ _) HF _ Hin) as (H1 & H2 & H3). cbn [fst snd] in *.
    split; [exact H1|]. split; [exact (NFX _ _ H2 H3)|]. exact (UT _ _ H3). }
  assert (ACH : forall ns h, nodes_ok FB Ai rho (kept ++ passed) ns -> achain (rm rho) h ns -> achain (rm rho1) h ns).
  { intros ns h [HF _] HA. eapply achain_frame; [exact HA| |].
    - intros z (b & cap & Hin & Hz). destruct (proj1 (Forall_forall _ _) HF _ Hin) as (H1 & H2 & H3). cbn [fst snd] in *.
      pose proof (proj1 (Forall_forall _ _) (achain_caps _ _ _ HA) _ Hin) as [Hc _]. cbn in Hc.
      apply (Hrm z b (HDR + cap) H1 H2 H3). unfold HDR. lia.
    - intros z (b & cap & Hin & Hz) Hdef. destruct (proj1 (Forall_forall _ _) HF _ Hin) as (H1 & H2 & H3). cbn [fst snd] in *.
      rewrite (Hrm z b (HDR + cap) H1 H2 H3 ltac:(lia)). exact Hdef. }
  destruct amCe as [|hd|hd nx cap sl|hd g]; cbn -[HDR flat_map pl_subst] in HX |- *.
  - exact I.
  - rewrite EV. destruct HX as (ns & HA & HNS). exists ns. split; [exact (ACH ns _ HNS HA) | exact (NOK ns HNS)].
  - rewrite !EV. destruct HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & ns & HA & HNS & Hnin).
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact (NFX _ _ X4 X5)|].
    split; [exact (UT _ _ X5)|]. split.
    + intros z Hz. rewrite (Hrm z _ _ X3 X4 X5); [exact (X6 z Hz) | unfold HDR in *; lia].
    + split.
      * apply Forall_forall. intros ps Hps. unfold pl_subst in X7. rewrite Forall_map in X7.
        pose proof (proj1 (Forall_forall _ _) X7 ps Hps) as Y. cbv beta in Y. cbn [fst snd] in Y. rewrite !EV. exact Y.
      * exists ns. split; [exact (ACH ns _ HNS HA)|]. split; [exact (NOK ns HNS) | exact Hnin].
  - rewrite !EV. destruct HX as (ns & HA & HNS & HL). exists ns. split; [exact (ACH ns _ HNS HA)|]. split; [exact (NOK ns HNS) | exact HL].
Qed.

Section CallTCA.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S5eS1S2Sa8S8dS6ScR2A1S5R3A1A3VTR;S5dVsegs;R5R4R3A4R2A2M0F_;G0F_;FQ;Frho;FS;FJ;").
Hypothesis TR_ex : forall (A : Type) (J : A -> jpred) S rho (Q : assn),
  (forall x, TR (SPJ segs (J x) S rho) Q) -> TR (SPJ segs (fun r t m => exists x, J x r t m) S rho) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sa8Sa8Sa8Sa9R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|3|
S5eS5eS1S1Sb0S41S4A1M0S41S3fS1S8fA2M1A1Sa8S2S36S43G0A1SefR7R6R5A3S46G0R4A2A3S36S3eS97R8R7R6R5S8cG1S1S44S1S8fA2R4A4A5S40A3S2VTR;S5dVsegs;RbR9R1A4S90Vsegs;S3R9A1R1R6A4A2Frho1;S41S6bA1M2Sf4S6aSfVsegs;R7RdS42G2SfaR3SfbR2R1A2A4A4R10R8R4R2A3R10Sb1Sb2R9RcR4A3RdA2R5R3A3F_;F_;Fmd;Fms;Ftr;S1S8fG2Sf4S6aS2G2Sf4S6aS65G1S42S1S8fR9R8A4R10A3SfVsegs;RfR15S42G2SfaR8SfbR7R6A2A4A4R18R10R9R7A3S8eS3R16A1Sb1Sb2R11R14R9A3R15A2R7A3SfVsegs;R8RdS42G2SfaR7SfbR6R5A2A4A4RdSb1Sb2R13R16RbA3R17A2R9R8R6A4S37S99R14RcR17R18R19RfRaA7S2S98R15RdR18R19R1aR1bR10R1RbA9VTR;S5dVsegs;S96R10Sb1Sb2R16R19ReA3R1aA2RcA3S93R1aS3R1bA1R11S3R1cA1R19A5R2A4R17A2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S5dVsegs;ReRcR6A4R7A2F_;F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;FPre;FC0;FJp;FJ;").

Hypothesis SUMT : ltac2:(tb__ "0|0|
S41S3fS33S33A2A1S2VTR;S5dVsegs;S10dVKc;VP0c;R2A1R2VtvC;VamC;A5VPreC;R1A4S90Vsegs;VNPc;R1S11eR2A1A4A2Frho1;FFBc;").

Theorem client_callAT : ltac2:(tb__ "0|d|
S1Sb0S41S4A1M0S2S41S3fS0S0A2M1A1M2G2S51Sa8S36S43G0A1SefR8VPreC;R7A3S46G0R6A2A3S36S3eSbdVC;VNP;R9VPreC;R8R7S8cS3fS1S3fG2S51A2M3A2M4S1S44S1G3A2VPDA;A4A7S40A3S36S3eS95R9VNPc;A2S40A3S36S3eSebVNP;S3RbA1A2S40A3S36S3eSb8S3RcA1S47G1R8R7A3A2S40A3S36S3eS52S3RdA1R7A2S40A3S36S3eSc8RdR9VtvC;A3S40A3S36S3eS56S53ReVamC;A2R9A2S40A3S36S3eS67G4G4S4aS4aSd3VNPc;R10S3R11A1M5S44S1G3R1A3M6S44G2S51S48S1G3R1A3M7A3M8A5S11fR10G5G6S48G2S51G7A3M9A4A2S120G6G8G9A3A2Ld;VPDA;A3S40A3SacSf4S8dS6ScR10A1S5R13A1A3VP0f;Vrho0;A1S8eVNP;Vrho0;R12A3SbcVFB;R5A2SbeVFB;R6R14S47G1R13R12A3A4Sc1R15S47G1R14R13A3A2Sc2R16S47G1R15R14A3A2S10cVFB;R14R9R17S47G1R16R15A3A5S38S2S2S38S6aS6aSdcVsegs;VC;RcR2R1A5Lmd;A2LrhoM;A2SbfR19Sf7SaeRbA1A1A2S37ScdVsegs;VC;Vrho0;VFB;R1aR19R1bA7VP0c;Sc3VFB;R1aR19A3Sb1Sb2R1aR1bRbA3R1cA2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;G4S2S65G4R2VPDA;A3S8eS3R15A1R12R2A3VTR;S5dVsegs;S10bVNP;VKc;Vrho0;VP0f;VFB;S47G1R12Sd0S92R15VNPc;S44S1G3R4A3MaS3R16A1A4MbS44G2S51S48S1G3R4A3McA3A2A3S53GbS48G2S51GcA3A2A7ScfVNPc;R16R15R14GaA5R3A4RfA2F_;F_;Frho';Fd;VTR;S5dVsegs;S10bVNP;VKc;Vrho0;VP0f;VFB;S47G1RfReA3RdA7R13R10A4RcA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Fpassed;Fkept;Frho;FR;Fs;FCl;").
Proof using HnextPre ML SUMT TR_callP TR_ex TR_facts TR_pre.
  intros Cl s R rho kept passed am Q He Hchk Hdom Hnf Hnb Hamb Hpass Hameq Hpd HIN Tcont.
  apply Pos.leb_le in Hnf. apply am_eqb_sound in Hameq.
  apply TR_facts. intros HF.
  apply (TR_ex MA (JGAi NP Kc rho0 P0f FB (kept ++ passed) am)). intros Ai.

  assert (PASS : forall ms, map (tvv (rho_sub (rho_absorb rho R ms) s)) tvC = map (tvv rho) passed
                 /\ forall k t t', nth_error passed k = Some t -> nth_error tvC k = Some t' -> (tnz (rho_sub (rho_absorb rho R ms) s) t' <-> tnz rho t)).
  { intros ms. destruct (tv_sub_eqb_sound s passed tvC (rho_absorb rho R ms) Hpass) as [M1 M2].
    assert (EA : forall l, map (tvv (rho_absorb rho R ms)) l = map (tvv rho) l).
    { intros l. apply map_ext. intros t. unfold tvv. rewrite !eval_absorb. reflexivity. }
    split; [rewrite M1; apply EA|]. intros k t t' Ht Ht'. rewrite (M2 k t t' Ht Ht'). unfold tnz. rewrite eval_absorb. tauto. }
  eapply (TR_callP (JGAi NP Kc rho0 P0f FB (kept ++ passed) am Ai) (JGA_pre Kc (P0c (FBx FB rho kept)) (FBx FB rho kept) tvC amC) Cl PreC s R
            (PostsCA (FBx FB rho kept)) Q rho He).
  - unfold PostsCA. rewrite map_map. exact (call_checkT_P _ _ _ _ _ _ _ Hchk).
  - intros rho1. rewrite HnextPre. apply SUMT.
  -
    intros tr ms md Hsm [(Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0) HXA].
    destruct (HIN Ai ms HF HP0 Hav HP HN HD HZ HXA (ex_intro _ rho (ex_intro _ md (MI1 segs C _ _ _ _ HM))) ltac:(eapply T_of_chk; [exact Hav | exact (proj2 (proj2 HM)) | exact Hchk])) as [HRok HPc]. destruct (PASS ms) as [PM PZ].
    assert (FBX : fbin (FBx FB rho kept) Ai).
    { intros bn Hbn. apply In_FBx in Hbn as [Hbn|(t & Ht & Hnz & <-)]; [exact (HP _ Hbn)|].
      destruct (proj1 (Forall_forall _ _) HN t ltac:(apply in_or_app; left; exact Ht) Hnz) as (_ & X & _). exact X. }
    assert (HMa : MInvR segs C Ai (rho_sub (rho_absorb rho R ms) s) md /\ (inited Ai /\ TPI C (rho_sub (rho_absorb rho R ms) s) Ai)).
    { split; [| split; [exact (proj1 (proj2 HM)) | split; [exact (tp_of_TPI _ _ _ _ _ _ _ _ _ _ _ _ Hav (proj2 (proj2 HM)) Hchk)
                                                          | rewrite (T0_callee C NP rho0 PreC _ _ _ _ _ _ _ Hav Hchk); exact (TPI_top _ _ _ (proj2 (proj2 HM)))]]].
      eapply MI1. eapply (MInvR_mem segs C _ ML); [exact HM| |reflexivity].
      intros a Ha Ho. apply rm_absorb_out. eapply (R_miss segs C ML Ai None rho rho md R a (MI1 segs C _ _ _ _ HM)); [|exact Ha|exact Ho].
      intros o b Ho' Hr'. apply (pclF_caddr segs C rho0 (FBx FB rho kept) Ai b FBX (proj2 (proj2 HM))). exact (HRok o b Ho' Hr'). }
    exists Ai. split.
    + split; [exact Hk|]. split; [exact HMa|]. split; [exact FBX|]. split; [split; [|split]|split; [intros a _ _; reflexivity| exact HPc]].
      * unfold tvin. apply Forall_forall. intros tc Htc Hnz.
        destruct (In_nth_error _ _ Htc) as [k Hk'].
        assert (exists tp, nth_error passed k = Some tp) as [tp Htp].
        { pose proof (Forall2_map_eq _ _ _ _ PM) as L. destruct (nth_error passed k) eqn:En; [eexists; reflexivity|].
          exfalso. apply nth_error_None in En. assert (k < length tvC)%nat by (apply nth_error_Some; congruence). lia. }
        rewrite (map_nth2 _ _ _ _ k tp tc PM Htp Hk'). apply (proj1 (PZ k tp tc Htp Hk')) in Hnz.
        pose proof (nth_error_In _ _ Htp) as HinP.
        destruct (proj1 (Forall_forall _ _) HN tp ltac:(apply in_or_app; right; exact HinP) Hnz) as (X0 & X1 & X2).
        split; [exact X0|]. split; [exact X1|]. intros Hin. apply In_FBx in Hin as [Hin|(t & Ht & Hnzt & Heq)]; [exact (X2 Hin)|].
        exact (tvd_app_cross rho kept passed t tp HD Ht HinP Hnzt Hnz Heq).
      * eapply tvd_map; [exact PM | exact PZ | exact (tvd_app_r rho kept passed HD)].
      * eapply tvz_map; [exact PM | exact PZ |]. unfold tvz in HZ |- *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. right. exact Ht.
    +
      destruct (PASS ms) as [PM' PZ'].
      eapply (XA_export amC s Ai rho _ md kept passed tvC (MI1 segs C _ _ _ _ HM) HP HN); [rewrite Hameq; exact HXA| |exact PM'|exact PZ'|].
      * intros e. rewrite <- eval_subst. apply eval_absorb.
      * intros z b n Hb Hnfb Hut Hz. apply rm_absorb_out.
        intros (o & Ho & Hr). apply (pclFx_not_block rho0 FB ML Ai rho md (kept ++ passed) b n (bv_unsigned (Z_to_bv 64 z)) (MI1 segs C _ _ _ _ HM) (proj2 (proj2 HM)) HP HN Hb Hnfb Hut).
        -- rewrite u64_of_sum; [exact Hz|]. pose proof (block_geom ML Ai rho md b n (MI1 segs C _ _ _ _ HM) Hb) as (_ & _ & G2 & G3 & _). unfold aceil in G3. lia.
        -- apply (pclF_mono _ (FBx FB rho kept)); [apply FBx_kept_sub|]. exact (HRok o _ Ho Hr).
  -
    intros L JL tr ms md rhoL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    destruct HJ as [(Hav & Hk & HM & HP & (HN & HD & HZ) & HK & HP0) HXA].
    unfold PostsCA in HinL. apply in_map_iff in HinL as ([Ld [tvL amL]] & Heq & Hd). cbn [fst snd] in Heq. injection Heq as HL HJLe. subst L JL.
    destruct (HIN Ai ms HF HP0 Hav HP HN HD HZ HXA (ex_intro _ rho (ex_intro _ md (MI1 segs C _ _ _ _ HM))) ltac:(eapply T_of_chk; [exact Hav | exact (proj2 (proj2 HM)) | exact Hchk])) as [HRok HPc].
    pose proof (proj1 (forallb_forall _ _) Hpd _ Hd) as Hpdd. cbn [fst snd] in Hpdd.
    apply andb_prop in Hpdd as [Hpdd Hnew]. apply andb_prop in Hpdd as [HtvL HamL].
    destruct HJL as (A' & (HkL & HM' & HP' & (HNc & HDc & HZc) & HKc & HP0c) & HXL).
    assert (HsubA' : forall bn, In bn (FBx FB rho kept) -> In bn (ma_blocks A')) by exact HP'.
    pose proof (MI1 segs C _ _ _ _ HM') as HMr'.
    assert (HT' : TPI C rho0 A').
    { split; [exact (TPI_tp _ _ _ (proj2 (proj2 HM)))|].
      pose proof (TPI_top _ _ _ (proj2 (proj2 HM'))) as TK. rewrite (T0_callee C NP rho0 PreC _ _ _ _ _ _ _ Hav Hchk) in TK. exact TK. }
    split.
    + split.
      *   intros a Hina. rewrite <- (Z_to_bv_bv_unsigned 64 a).
        apply HKc; [apply bv_urange |]. destruct Hina as (o & Ho & Hr). exact (pclF_reT _ _ _ _ _ _ (T0_callee C NP rho0 PreC _ _ _ _ _ _ _ Hav Hchk) (HRok o _ Ho Hr)).
      *
        intros o' oR Hin' HinR.
        unfold new_objs_okA in Hnew. pose proof (proj1 (forallb_forall _ _) Hnew o' Hin') as Ho'.
        destruct (obj_range rho oR) as [lo hi] eqn:HR2.
        assert (HcR : forall a, lo <= a < hi -> pclF segs C rho0 (FBx FB rho kept) a).
        { intros a Ha. apply (HRok oR a HinR). rewrite HR2. exact Ha. }
        apply orb_prop in Ho'. destruct Ho' as [Ho'|Ho'].
        -- apply existsb_exists in Ho' as ([vd vsz] & Hvn & Heqs). cbn [fst snd] in Heqs.
           apply andb_prop in Heqs as [Heqs E3]. apply andb_prop in Heqs as [E1 E2].
           apply sv_eqb_sound in E1. apply sv_eqb_sound in E2. apply sv_eqb_sound in E3.
           destruct o' as [ob olo ohi oc od]. cbn [ob_base ob_lo ob_hi] in E1, E2, E3. subst ob olo ohi.
           unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
           rewrite soff_lit_small by lia. unfold soff. rewrite bv_signed_U.
           set (p := bv_unsigned (eval rhoL vd)). set (n' := bv_unsigned (eval rhoL vsz)).
           apply ranges_disjoint_by_points. intros a Ha1 Ha2.
           assert (Ha : p <= a < p + n') by (destruct (Zsigned_spec n') as [[_ X]|[_ X]]; rewrite X in Ha1; lia).
           assert (Hnz : tnz rhoL (vd, vsz)).
           { intros Hz. pose proof (proj1 (Forall_forall _ _) HZc _ Hvn (fun H => H Hz)) as Z0. unfold tvv in Z0. cbn [fst snd] in Z0. fold n' in Z0. lia. }
           destruct (proj1 (Forall_forall _ _) HNc _ Hvn Hnz) as (Npos & HinN & HninF). unfold tvv in HinN, HninF. cbn [fst snd] in HinN, HninF. fold p n' in HinN. fold p n' in HninF.
           exact (pclF_not_block rho0 (FBx FB rho kept) ML A' rhoL md' p n' a HMr' HT' HP' HinN HninF Ha (HcR a Ha2)).
        -- destruct amL as [| |hdL nxL capL slL|hdL gL]; [discriminate|discriminate| |discriminate].
           apply ranges_disjoint_by_points. intros a Ha1 Ha2.
           pose proof (hdr_obj_range (FBx FB rho kept) hdL nxL capL slL A' rhoL tvL o' a HXL Ho' Ha1) as Hr'.
           cbn -[HDR] in HXL. destruct HXL as (X1 & X2 & X3 & X4 & _).
           apply (pclF_not_block rho0 (FBx FB rho kept) ML A' rhoL md' _ _ a HMr' HT' HP' X3 X4); [|exact (HcR a Ha2)].
           cbv beta in Hr'. lia.
    + intros rho' Hlink.
      eapply TR_pre; [ | apply (Tcont (Ld, (tvL, amL)) (rho_patch rho' (patchf rho rho' R)) Hd)].
      2:{ destruct Hlink as (A & _). eapply agree_vals_trans; [exact A | apply agree_vals_patch]. }
      intros w [Hsm' HJ']. cbn [J_ofP fst snd] in HJ' |- *.
      destruct HJ' as (A2 & (Hk2 & HM2 & HP2 & (HN2 & HD2 & HZ2) & HK2 & _) & HX2).
      assert (Hag' : agree_vals (ss_next Cl) rho rho') by (destruct Hlink as (A & _); exact A).
      set (rho'' := rho_patch rho' (patchf rho rho' R)).
      assert (Hag'' : agree_vals (ss_next Cl) rho rho'') by (eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]).
      assert (Hnbk : tv_below (ss_next Cl) kept = true).
      { unfold tv_below in *. rewrite forallb_app in Hnb. apply andb_prop in Hnb as [A _]. exact A. }
      set (isub := import_sub s NPc Ld (ss_next Cl)).
      destruct Hlink as (L1 & L2 & L3 & L4). rewrite HnextPre in L4.
      assert (EI : forall e, sv_vars_all (ivar_ok NPc s (ss_next Cl) Ld) e = true -> eval rho'' (sv_subst isub e) = eval rhoL e).
      { intros e Hev. subst rho''. rewrite eval_patch, eval_subst. symmetry.
        apply (eval_agree_vars (ivar_ok NPc s (ss_next Cl) Ld) rhoL (rho_sub rho' isub) e); [| |exact Hev].
        - intros u Hu. unfold ivar_ok in Hu. apply andb_prop in Hu as [Hu1 Hu2]. apply Pos.ltb_lt in Hu2.
          cbn [rho_sub rw]. apply L4; [exact Hu1 | lia].
        - intros l. cbn [rho_sub rl]. rewrite <- (proj2 L3 l). cbn [rho_sub rho_absorb rl]. exact (proj2 L1 l). }
      assert (IM : map (tvv rho'') (import_tv isub tvL) = map (tvv rhoL) tvL
                   /\ forall k t t', nth_error tvL k = Some t -> nth_error (import_tv isub tvL) k = Some t' -> (tnz rho'' t' <-> tnz rhoL t)).
      { unfold tvL_ok in HtvL. clear - HtvL EI. induction tvL as [|t r IH]; [split; [reflexivity | intros [|k] ? ? H; discriminate]|].
        cbn in HtvL. apply andb_prop in HtvL as [Ht Hr]. apply andb_prop in Ht as [Ht1 Ht2]. destruct (IH Hr) as [IH1 IH2].
        split.
        - cbn [map import_tv]. f_equal; [|exact IH1]. unfold tvv. cbn [fst snd]. rewrite (EI _ Ht1), (EI _ Ht2). reflexivity.
        - intros [|k] a b Ha Hb; cbn in Ha, Hb; [|exact (IH2 k a b Ha Hb)].
          injection Ha as <-. injection Hb as <-. unfold tnz. cbn [fst]. rewrite (EI _ Ht1). tauto. }
      destruct IM as [IM1 IM2].
      assert (HT2 : TPI C rho0 A2).
      { split; [exact (TPI_tp _ _ _ (proj2 (proj2 HM)))|].
        pose proof (TPI_top _ _ _ (proj2 (proj2 HM2))) as TK. rewrite (T0_callee C NP rho0 PreC _ _ R _ _ R ms Hav Hchk) in TK. exact TK. }
      split; [exact (cont_smatchN segs NPc Cl PreC _ s R rho rho' tr ms md w He Hsm HnextPre Hag' Hsm')|].

      assert (RM2 : forall z b n, In (b, n) (ma_blocks A2) -> ~ In (b, n) (FBx FB rho kept) -> b <= z < b + n ->
                     rm rho'' (Z_to_bv 64 z) = rm rhoL (Z_to_bv 64 z)).
      { intros z b n Hb Hnfb Hz. subst rho''. cbn [rho_patch rm]. unfold patchf.
        destruct (in_ranges_dec rho R (Z_to_bv 64 z)) as [Hi|Hn']; [|apply L2].
        exfalso. destruct Hi as (o & Ho & Hr).
        pose proof (block_geom ML A2 _ _ b n (MI1 segs C _ _ _ _ HM2) Hb) as (_ & _ & G2 & G3 & _). unfold aceil in G3.
        rewrite u64_of_sum in Hr by lia.
        exact (pclF_not_block rho0 (FBx FB rho kept) ML A2 _ _ b n z (MI1 segs C _ _ _ _ HM2) HT2 HP2 Hb Hnfb Hz (HRok o z Ho Hr)). }
      exists A2. split.
      * split; [|split; [exact Hk2|split; [|split; [|split; [split; [|split]|split; [|exact HP0]]]]]].
        -- eapply agree_vals_trans; [exact Hav|]. eapply agree_vals_trans; [eapply agree_vals_le; [exact Hnf| exact Hag']| apply agree_vals_patch].
        -- eapply (MInvR_mem segs C _ ML); [exact (conj (proj1 HM2) (conj (proj1 (proj2 HM2)) HT2))| |reflexivity]. intros a Ha Ho. subst rho''. cbn [rho_patch rm]. unfold patchf.
           destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi|Hn'].
           ++ exfalso. eapply (R_miss segs C ML A2 None rho rhoL _ R a); [exact (proj1 HM2) | | exact Ha | exact Ho | exact Hi].
              intros o b Ho' Hr'. apply (pclF_caddr segs C rho0 (FBx FB rho kept) A2 b HP2 HT2). exact (HRok o b Ho' Hr').
           ++ apply L2.
        -- intros bn Hbn. apply HP2. apply In_FBx. left. exact Hbn.
        --
           unfold tvin. apply Forall_app. split.
           ++ apply Forall_forall. intros t Ht Hnz.
              pose proof (proj1 (forallb_forall _ _) Hnbk t Ht) as Hbt.
              rewrite (tvv_agree (ss_next Cl) rho rho'' t Hag'' Hbt) in *. apply (proj1 (tnz_agree (ss_next Cl) rho rho'' t Hag'' Hbt)) in Hnz.
              destruct (proj1 (Forall_forall _ _) HN t ltac:(apply in_or_app; left; exact Ht) Hnz) as (X0 & X1 & X2).
              split; [exact X0|]. split; [|exact X2]. apply HP2. apply In_FBx. right. exists t. auto.
           ++ eapply tvin_map; [exact IM1 | exact IM2 |].
              unfold tvin in HN2 |- *. apply Forall_forall. intros t Ht Hnz. destruct (proj1 (Forall_forall _ _) HN2 t Ht Hnz) as (X0 & X1 & X2).
              split; [exact X0|]. split; [exact X1|]. intros Hin. apply X2. apply In_FBx. left. exact Hin.
        --
           apply tvd_app.
           ++ apply (tvd_agree (ss_next Cl) rho rho'' kept Hag'' Hnbk). exact (tvd_app_l rho kept passed HD).
           ++ eapply tvd_map; [exact IM1 | exact IM2 | exact HD2].
           ++ intros t t' Ht Ht' Hnz Hnz' Heq.
              pose proof (proj1 (forallb_forall _ _) Hnbk t Ht) as Hbt.
              rewrite (tvv_agree (ss_next Cl) rho rho'' t Hag'' Hbt) in Heq. apply (proj1 (tnz_agree (ss_next Cl) rho rho'' t Hag'' Hbt)) in Hnz.
              destruct (In_nth_error _ _ Ht') as [k Hk'].
              assert (exists t0, nth_error tvL k = Some t0) as [t0 Ht0].
              { pose proof (Forall2_map_eq _ _ _ _ IM1) as L. destruct (nth_error tvL k) eqn:En; [eexists; reflexivity|].
                exfalso. apply nth_error_None in En. assert (k < length (import_tv isub tvL))%nat by (apply nth_error_Some; congruence). lia. }
              rewrite (map_nth2 _ _ _ _ k t0 t' IM1 Ht0 Hk') in Heq. apply (proj1 (IM2 k t0 t' Ht0 Hk')) in Hnz'.
              destruct (proj1 (Forall_forall _ _) HN2 t0 (nth_error_In _ _ Ht0) Hnz') as (_ & _ & X2).
              apply X2. apply In_FBx. right. exists t. auto.
        --
           unfold tvz. apply Forall_app. split.
           ++ apply (tvz_agree (ss_next Cl) rho rho'' kept Hag'' Hnbk). unfold tvz in HZ |- *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ). apply in_or_app. left. exact Ht.
           ++ eapply tvz_map; [exact IM1 | exact IM2 | exact HZ2].
        --
           intros a Ha Hp. subst rho''. cbn [rho_patch rm]. unfold patchf.
           destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi|Hn']; [apply HK; assumption|].
           rewrite L2. transitivity (rm (rho_sub (rho_absorb rho R ms) s) (Z_to_bv 64 a)).
           ++ apply HK2; [exact Ha|]. apply (pclF_mono _ FB); [intros bn Hbn; apply In_FBx; left; exact Hbn | exact (pclF_reT _ _ _ _ _ _ (T0_callee C NP rho0 PreC _ _ R _ _ R ms Hav Hchk) Hp)].
           ++ rewrite rm_absorb_out by exact Hn'. apply HK; assumption.
      *
        eapply (XA_import (FBx FB rho kept) amL A2 rhoL rho'' _ tvL (import_tv isub tvL) kept isub (MI1 segs C _ _ _ _ HM2) HP2).
        -- intros bn Hbn. apply In_FBx. left. exact Hbn.
        -- exact HX2.
        -- intros e Hine. apply EI. unfold amL_ok in HamL. exact (proj1 (forallb_forall _ _) HamL e Hine).
        -- exact IM1.
        -- exact IM2.
        -- intros t Ht Hnz. pose proof (proj1 (forallb_forall _ _) Hnbk t Ht) as Hbt.
           rewrite (tvv_agree (ss_next Cl) rho rho'' t Hag'' Hbt). apply (proj1 (tnz_agree (ss_next Cl) rho rho'' t Hag'' Hbt)) in Hnz.
           apply In_FBx. right. exists t. auto.
        -- exact RM2.
Qed.
End CallTCA.

Hypothesis SUM : ltac2:(tb__ "0|0|
Sa9OF_;S41S3fS33S33A2A1S2Se1Vsegs;R3VKc;A3SaaVsegs;R4S5dVsegs;S10dVKc;VP0c;R3A1R3VtvC;VamC;A5VPreC;R2A4S90Vsegs;VNPc;R2S11eR3A1A4A4F_;Frho1;FFBc;Fok;").

Hypothesis SUMX : ltac2:(tb__ "0|0|
S41S3fS33S33A2A1S2Se2VKc;A1SabVsegs;S5dVsegs;S10dVKc;VP0c;R3A1R3VtvC;VamC;A5VPreC;R2A4S90Vsegs;VNPc;R2S11eR3A1A4A3F_;Frho1;FFBc;").

Theorem client_callAA : ltac2:(tb__ "0|d|
Sa9OF_;S1Sb0S41S4A1M0S2S41S3fS0S0A2M1A1M2G2S51Sa8Se1Vsegs;R9VKc;A3S36S43G0A1SefR9VPreC;R8A3S46G0R7A2A3S36S3eSbdVC;VNP;RaVPreC;R9R8S8cS3fS1S3fG2S51A2M3A2M4S1S44S1G3A2VPDA;A4A7S40A3S36S3eS95RaVNPc;A2S40A3S36S3eSebVNP;S3RcA1A2S40A3S36S3eSb8S3RdA1S47G1R9R8A3A2S40A3S36S3eS52S3ReA1R8A2S40A3S36S3eSc8ReRaVtvC;A3S40A3S36S3eS56S53RfVamC;A2RaA2S40A3S36S3eS67G4G4S4aS4aSd3VNPc;R11S3R12A1M5S44S1G3R1A3M6S44G2S51S48S1G3R1A3M7A3M8A5S11fR11G5G6S48G2S51G7A3M9A4A2S120G6G8G9A3A2Ld;VPDA;A3S40A3SacSf4S8dS6ScR11A1S5R14A1A3VP0f;Vrho0;A1S8eVNP;Vrho0;R13A3SbcVFB;R5A2SbeVFB;R6R15S47G1R14R13A3A4Sc1R16S47G1R15R14A3A2Sc2R17S47G1R16R15A3A2S10cVFB;R15R9R18S47G1R17R16A3A5S38S2S2S38S6aS6aSdcVsegs;VC;RcR2R1A5Lmd;A2LrhoM;A2SbfR1aSf7SaeRbA1A1A2S37ScdVsegs;VC;Vrho0;VFB;R1bR1aR1cA7VP0c;Sc3VFB;R1bR1aA3Sb1Sb2R1bR1cRbA3R1dA2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;G4S2S65G4R2VPDA;A3S8eS3R16A1R13R2A3SaaVsegs;R18S5dVsegs;S10bVNP;VKc;Vrho0;VP0f;VFB;S47G1R13Sd0S92R16VNPc;S44S1G3R4A3MaS3R17A1A4MbS44G2S51S48S1G3R4A3McA3A2A3S53GbS48G2S51GcA3A2A7ScfVNPc;R17R16R15GaA5R3A4R10A4F_;F_;Frho';Fd;SaaVsegs;R15S5dVsegs;S10bVNP;VKc;Vrho0;VP0f;VFB;S47G1R10RfA3ReA7R14R11A4RdA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Fpassed;Fkept;Frho;FR;Fs;FCl;Fok;").
Proof using HnextPre ML SUM.
  intros ok Cl s R rho kept passed am Q Hok.
  apply (client_callAT (triple segs ok) (triple_factsJ segs ok) (triple_SPJ_ex segs ok)
           (fun P P' Q' HP H => @triple_conseq segs ok P P' Q' Q' HP (fun w Hw => Hw) H) (call_soundP segs ok)).
  intros FBc rho1. apply SUM. exact Hok.
Qed.

Theorem client_callAA_ex : ltac2:(tb__ "0|d|
S1Sb0S41S4A1M0S2S41S3fS0S0A2M1A1M2G2S51Sa8Se2VKc;A1S36S43G0A1SefR9VPreC;R8A3S46G0R7A2A3S36S3eSbdVC;VNP;RaVPreC;R9R8S8cS3fS1S3fG2S51A2M3A2M4S1S44S1G3A2VPDA;A4A7S40A3S36S3eS95RaVNPc;A2S40A3S36S3eSebVNP;S3RcA1A2S40A3S36S3eSb8S3RdA1S47G1R9R8A3A2S40A3S36S3eS52S3ReA1R8A2S40A3S36S3eSc8ReRaVtvC;A3S40A3S36S3eS56S53RfVamC;A2RaA2S40A3S36S3eS67G4G4S4aS4aSd3VNPc;R11S3R12A1M5S44S1G3R1A3M6S44G2S51S48S1G3R1A3M7A3M8A5S11fR11G5G6S48G2S51G7A3M9A4A2S120G6G8G9A3A2Ld;VPDA;A3S40A3SacSf4S8dS6ScR11A1S5R14A1A3VP0f;Vrho0;A1S8eVNP;Vrho0;R13A3SbcVFB;R5A2SbeVFB;R6R15S47G1R14R13A3A4Sc1R16S47G1R15R14A3A2Sc2R17S47G1R16R15A3A2S10cVFB;R15R9R18S47G1R17R16A3A5S38S2S2S38S6aS6aSdcVsegs;VC;RcR2R1A5Lmd;A2LrhoM;A2SbfR1aSf7SaeRbA1A1A2S37ScdVsegs;VC;Vrho0;VFB;R1bR1aR1cA7VP0c;Sc3VFB;R1bR1aA3Sb1Sb2R1bR1cRbA3R1dA2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;G4S2S65G4R2VPDA;A3S8eS3R16A1R13R2A3SabVsegs;S5dVsegs;S10bVNP;VKc;Vrho0;VP0f;VFB;S47G1R13Sd0S92R16VNPc;S44S1G3R4A3MaS3R17A1A4MbS44G2S51S48S1G3R4A3McA3A2A3S53GbS48G2S51GcA3A2A7ScfVNPc;R17R16R15GaA5R3A4R10A3F_;F_;Frho';Fd;SabVsegs;S5dVsegs;S10bVNP;VKc;Vrho0;VP0f;VFB;S47G1R10RfA3ReA7R14R11A4RdA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fam;Fpassed;Fkept;Frho;FR;Fs;FCl;").
Proof using HnextPre ML SUMX.
  intros Cl s R rho kept passed am Q Hvi.
  apply (client_callAT (etriple segs) (etriple_factsJ segs) (etriple_SPJ_ex segs)
           (fun P P' Q' HP H => @etriple_conseq segs P P' Q' Q' HP (fun w Hw => Hw) H) (call_completeP segs)).
  intros FBc rho1. apply SUMX. exact Hvi.
Qed.
End ClientA.

Section FrameA.
Variable Kc : ltac2:(tb__ "0|0|
S41S6bA1S6aOF_;F_;").
Variable P0c : ltac2:(tb__ "0|0|
S41S3fS33S33A2A1S2OF_;F_;").
Variable PreC : sstate.
Variable tvC : list (sv * sv).
Variable PD : ltac2:(tb__ "0|0|
S41S3fS1S41S3fS0S0A2A1A2A1").
Variable NPc : positive.
Variable h0 : positive.
Hypothesis ML : malloc_laws segs C.
Hypothesis Hh0 : (h0 < NPc)%positive.
Hypothesis P0mono : ltac2:(tb__ "0|2|
S41S3fS33S33A2M0A1M1G1S2G0S65G0R1R4A3S65G0R2R4A3F_;Fbn;VP0c;R4R2A2VP0c;R4R3A2F_;F_;Fr;FF';FF;").

Definition PDAh : list (sstate * (list (sv * sv) * amode)) := ltac2:(tb__ "0|3|
S8cS3fS1S41S3fS0S0A2A1M0A2M1S3fS1S3fG0S51A2M2A2G1S42S1G2S44S1G0R1A3S42G0S51S48S1G0R1A3S55S9Vh0;A1A1A4A4Ld;VPD;A4").

Definition nblk (bc : Z * Z) : Z * Z := ltac2:(tb__ "0|0|
S42S33S33S44S33S33Vbc;A3S9eS113S48S33S33Vbc;A3A2A4").

Section T.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
Sa8Sa8Sa8Sa9R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_post : ltac2:(tb__ "0|0|
Sa8Sa8Sa8Sa9R3R1A1R3R2A1F_;Fw;VTR;R4R3A2VTR;R5R3A2F_;F_;FQ';FQ;FP;").
Hypothesis TR_exw : forall (A : Type) (P : A -> assn) (Q : assn), (forall a, TR (P a) Q) -> TR (fun w => exists a, P a w) Q.
Hypothesis TR_pureh : ltac2:(tb__ "0|0|
OSa8Sa8R3VTR;R3R2A2F_;VTR;Sa9S37R5R4R1A1A2Lw;R2A2F_;FQ;FP;FX;").
Hypothesis SUMT : ltac2:(tb__ "0|0|
S41S3fS33S33A2A1S2VTR;S5dVsegs;ScbVsegs;VC;VKc;VP0c;R2A1R2VtvC;A6VPreC;R1A4S90Vsegs;VNPc;R1SceVsegs;VC;VKc;VP0c;VPD;R2A6A4A2Frho1;FFBc;").

Theorem JGA_frame_sumT : ltac2:(tb__ "0|0|
S41S3fS33S33A2A1S2VTR;S5dVsegs;S10dVKc;VP0c;R2A1R2VtvC;S55S9Vh0;A1A1A5VPreC;R1A4S90Vsegs;VNPc;R1S10eVKc;VP0c;S121R2A4A4A2Frho1;FFBc;").
Proof using Hh0 ML P0mono SUMT TR_exw TR_post TR_pre TR_pureh.
  intros FBc rho1.

  apply (TR_pre (fun w => exists Ai ns,
            (achain (rm rho1) (bv_unsigned (rw rho1 h0)) ns /\ nodes_ok FBc Ai rho1 tvC ns /\ P0c FBc rho1
             /\ (exists md, MInvR segs C Ai rho1 md))
            /\ SPJ segs (JG_pre segs C Kc (P0c (FBc ++ map nblk ns)) (FBc ++ map nblk ns) tvC) PreC rho1 w)).
  { intros [tr [ms md]] [Hsm (Ai & (Hk & HM & HP & (HN & HD & HZ) & HK & HP0) & (ns & HA & HNO))].
    exists Ai, ns. split.
    - split; [exact HA|]. split; [exact HNO|]. split; [exact HP0|]. exists md. exact (MI1 segs C _ _ _ _ HM).
    - split; [exact Hsm|]. split; [exact Hk|]. exists Ai. split; [exact HM|]. split; [|split; [split; [|split; [exact HD|exact HZ]]|split; [intros a _ _; reflexivity|]]].
      + intros bn Hbn. apply in_app_or in Hbn as [Hbn|Hbn]; [exact (HP bn Hbn)|].
        apply in_map_iff in Hbn as (bc & <- & Hbc). exact (proj1 (proj1 (Forall_forall _ _) (proj1 HNO) bc Hbc)).
      + unfold tvin in HN |- *. apply Forall_forall. intros t Ht Hnz. destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2).
        split; [exact X0|]. split; [exact X1|]. intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (X2 Hin)|].
        apply in_map_iff in Hin as (bc & Heq & Hbc).
        exact (proj2 (proj2 (proj1 (Forall_forall _ _) (proj1 HNO) bc Hbc)) t Ht Hnz (eq_sym Heq)).
      + apply (P0mono FBc); [intros bn Hbn; apply in_or_app; left; exact Hbn | exact HP0]. }
  apply TR_exw. intros Ai. apply TR_exw. intros ns. apply TR_pureh. intros (HA & HNO & HP0 & (md0 & HM0)).
  set (FBn := FBc ++ map nblk ns).
  apply (TR_post _ (LQP segs NPc rho1 (PostsC segs C Kc P0c PD FBn))); [|apply SUMT].
  intros [tr [ms md]] (L & JL & rhoL & HinL & Hag & HsmL & HJL).
  unfold PostsC in HinL. apply in_map_iff in HinL as ([Ld tvL] & Heq & Hd). cbn [fst snd] in Heq. injection Heq as HL HJLe. subst L JL.
  exists Ld, (JLGA Kc (P0c FBc) FBc tvL (AHead (SVar h0))), rhoL.
  split; [unfold PostsCA, PDAh; rewrite map_map; apply in_map_iff; exists (Ld, tvL); split; [reflexivity | exact Hd]|].
  split; [exact Hag|]. split; [exact HsmL|].
  cbn [fst snd] in HJL. destruct HJL as (Hk & A' & HM' & HP' & (HN' & HD' & HZ') & HK' & HP0').
  assert (SUB : forall bn, In bn FBc -> In bn FBn) by (intros bn Hbn; unfold FBn; apply in_or_app; left; exact Hbn).
  assert (PCL : forall a, pclF segs C rho1 FBc a -> pclF segs C rho1 FBn a).
  { intros a [X|[X|(b & n & Hb & Hab)]]; [left; exact X | right; left; exact X |]. right; right. exists b, n. split; [apply SUB; exact Hb | exact Hab]. }
  exists A'. split.
  - split; [exact Hk|]. split; [exact HM'|]. split; [intros bn Hbn; apply HP'; apply SUB; exact Hbn|].
    split; [split; [|split; [exact HD'|exact HZ']]|split; [|exact HP0]].
    + unfold tvin in HN' |- *. apply Forall_forall. intros t Ht Hnz. destruct (proj1 (Forall_forall _ _) HN' t Ht Hnz) as (X0 & X1 & X2).
      split; [exact X0|]. split; [exact X1|]. intros Hin. exact (X2 (SUB _ Hin)).
    + intros a Ha Hp. apply HK'; [exact Ha|]. apply PCL. exact Hp.
  -
    cbn -[HDR]. exists ns.
    assert (Eh : rw rhoL h0 = rw rho1 h0) by (symmetry; apply (proj1 Hag); exact Hh0).
    rewrite Eh.
    assert (NODE : forall z, node_addr ns z -> rm rhoL (Z_to_bv 64 z) = rm rho1 (Z_to_bv 64 z)).
    { intros z (b & cap & Hin & Hz).
      pose proof (proj1 (proj1 (Forall_forall _ _) (proj1 HNO) (b, cap) Hin)) as HinA. cbn [fst snd nblk] in HinA.
      pose proof (block_geom ML Ai rho1 md0 b (HDR + cap) HM0 HinA) as (G0 & _ & G2 & G3 & _). unfold aceil in G3.
      apply HK'; [lia|]. right; right. exists b, (HDR + cap). split; [|lia].
      unfold FBn. apply in_or_app. right. apply in_map_iff. exists (b, cap). split; [reflexivity | exact Hin]. }
    split.
    + apply (achain_frame (rm rho1)); [exact HA | |].
      * intros z (b & cap & Hin & Hz). apply NODE. exists b, cap. split; [exact Hin |].
        pose proof (proj1 (Forall_forall _ _) (achain_caps _ _ _ HA) (b, cap) Hin) as [Hc _]. cbn [snd] in Hc. unfold HDR in *. lia.
      * intros z Hz Hdef. rewrite (NODE z Hz). exact Hdef.
    + split; [|exact (proj2 HNO)]. apply Forall_forall. intros bc Hbc.
      destruct (proj1 (Forall_forall _ _) (proj1 HNO) bc Hbc) as (Y0 & Y1 & Y2).
      split; [apply HP'; unfold FBn; apply in_or_app; right; apply in_map_iff; exists bc; split; [reflexivity | exact Hbc]|].
      split; [exact Y1|].
      intros t Ht Hnz Heq. destruct (proj1 (Forall_forall _ _) HN' t Ht Hnz) as (_ & _ & X2). apply X2.
      rewrite Heq. unfold FBn. apply in_or_app. right. apply in_map_iff. exists bc. split; [reflexivity | exact Hbc].
Qed.
End T.

Theorem JGA_frame_sum : ltac2:(tb__ "0|2|
Sa9OF_;S41S3fS33S33A2A1M0S2SaaVsegs;R3S5dVsegs;ScbVsegs;VC;VKc;VP0c;R2A1M1R2VtvC;A6VPreC;R1A4S90Vsegs;VNPc;R1SceVsegs;VC;VKc;VP0c;VPD;R2A6A4A4Frho1;FFBc;G0S2SaaVsegs;R4S5dVsegs;S10dVKc;G1R2VtvC;S55S9Vh0;A1A1A5VPreC;R1A4S90Vsegs;VNPc;R1S10eVKc;VP0c;S121R2A4A4A4Frho1;FFBc;F_;Fok;").
Proof using Hh0 ML P0mono.
  intros ok SUM. apply (JGA_frame_sumT (triple segs ok)).
  - intros P P' Q HP H. eapply triple_conseq; [exact HP | intros w Hw; exact Hw | exact H].
  - intros P Q Q' HQ H. eapply triple_conseq; [intros w Hw; exact Hw | exact HQ | exact H].
  - intros A P Q H. apply triple_ex. exact H.
  - intros X P Q H n Hn w [HX HP]. exact (H HX n Hn w HP).
  - exact SUM.
Qed.
Theorem JGA_frame_sum_ex : ltac2:(tb__ "0|2|
S41S3fS33S33A2A1M0S2SabVsegs;S5dVsegs;ScbVsegs;VC;VKc;VP0c;R2A1M1R2VtvC;A6VPreC;R1A4S90Vsegs;VNPc;R1SceVsegs;VC;VKc;VP0c;VPD;R2A6A4A3Frho1;FFBc;G0S2SabVsegs;S5dVsegs;S10dVKc;G1R2VtvC;S55S9Vh0;A1A1A5VPreC;R1A4S90Vsegs;VNPc;R1S10eVKc;VP0c;S121R2A4A4A3Frho1;FFBc;F_;").
Proof using Hh0 ML P0mono.
  intros SUM. apply (JGA_frame_sumT (etriple segs)).
  - intros P P' Q HP H. eapply etriple_conseq; [exact HP | intros w Hw; exact Hw | exact H].
  - intros P Q Q' HQ H. eapply etriple_conseq; [intros w Hw; exact Hw | exact HQ | exact H].
  - intros A P Q H. apply etriple_ex. exact H.
  - intros X P Q H w [HX HP]. exact (H HX w HP).
  - exact SUM.
Qed.
End FrameA.
End WithSegs.

Lemma NP_ok_NF : NP_ok NF.
Proof. reflexivity. Qed.
