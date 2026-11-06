(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "True"; "False"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "prod"; "pair"; "cons"; "option"; "false"; "Some"; "None"; "snd"; "fst"; "nil"; "app"; "nat"; "andb"; "length"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "ss_next"; "sobj"; "rm"; "SVar"; "ss_facts"; "sprop"; "SLit"; "rw"; "eval"; "holds"; "sv_eqb"; "sv_below"; "obj_range"; "ob_base"; "ob_hi"; "rl"; "ob_lo"; "ss_objs"; "sstate"; "DUnknown"; "SMd"; "cell"; "mkObj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "ax_S"; "ax_base"; "ax_X"; "word_byte"; "shadow_addr"; "xr_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "AA"; "aa_live"; "aa_geom"; "aa_V"; "aa_frames"; "aa_Kf"; "aa_Km"; "cls_keptA"; "topG"; "ageom"; "cls_kept_freeA"; "large_live"; "prim_room"; "sec_room"; "frames_of"; "small_live"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "leb"; "mul"; "div"; "of_nat"; "ltb"; "sub"; "modulo"; "eqb"; "to_nat"; "@Stdlib.Lists.List"; "In"; "nth_error"; "forallb"; "NoDup"; "existsb"; "filter"; "incl"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "smatchA"; "jpredA"; "ok_frameA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub_get"; "wsub"; "rho_absorb"; "rho_sub"; "in_ranges"; "sv_subst"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.BudA"; "uval"; "bitem"; "bd_below"; "KU"; "LARGE_MIN"; "BUD"; "bd_wpos"; "bx2"; "BXok"; "BXok_d"; "bud_pay"; "bxN"; "pay_okF"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJA"; "nd_tv"; "nd_fr"; "NDA"; "nd_am"; "ndesc"; "nd_bd"; "nd_below"; "untracked"; "TPA"; "capK"; "capN"; "JA"; "ok_frameKA"; "fbinA"; "ffinA"; "tvinA"; "frv"; "pclFA"; "bxa"; "frinA"; "JAi"; "apot"; "keptFA"; "ANone"; "JAk"; "pclSA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "jpostA"; "entails_frA"; "call_checkPA"; "import_subA"; "LQPA"; "import_postA"; "xs_framed"; "J_ofPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "assn"; "triple"; "etriple"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM.WithSegs.Sum"; "T_afterA"; "call_checkTA"; "site_okA"; "payA"; "xrs_okA"; "csz"; "robj_stackA"; "ccount"; "xr_in_stack_obj"; "xr_lit_in"; "robj_stackA_p"; "xr_tracked"; "ffpairs"; "lit_in_ranges"; "robjs_checkA"; "robjs_checkA_dg"; "robjs_checkA_ref"; "xr_in_stack_obj_p"; "xr_in_stack_obj_ref"; "xrs_checkA"; "xrs_checkA_dg"; "xrs_checkA_ref"; "XP_memcpy"; "XP_memset"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Pre_malloc"; "ustop"; "ulink"; "Pre_calloc"; "L_malloc_ok"; "unwind_stopJ"; "Pre_stack_malloc"; "L_calloc_ok"; "L_malloc_null"; "V_RES"; "L_stack_malloc"; "L_calloc_null"; "L_memcpy"; "Pre_free"; "Pre_free_null"; "client_addrA"; "mem_keptA"; "Pre_memcpy"; "Pre_memset"; "L_free";
"L_free_null"; "frame_flag"; "alloc_contractsA"; "J_alloc_pre"; "L_memset"; "alloc_contractsA_ex"; "band_free"; "errno_addrA"; "pairwise_disjoint"; "JL_pure"; "client_shadowA"; "V_FLAG"; "V_TOP"; "calloc_size"; "malloc_shape"; "JL_calloc_null"; "JL_calloc_ok"; "JL_malloc_null"; "JL_malloc_ok"; "J_pure_pre"; "KcA"; "Kc_ok"; "Posts_calloc"; "Posts_malloc"; "UStopLe"; "calloc_shape"; "free_shape"; "n_frames"; "JL_free"; "JL_free_null"; "JL_stack_malloc"; "J_free_null_pre"; "J_free_pre"; "J_memcpy_pre"; "J_memset_pre"; "J_stack_malloc_pre"; "alloc_lawsA"; "client_mut_addrA"; "memcpy_contractA"; "memset_contractA"; "top_var"; "tp_ok"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "le"; "ltb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM.WithSegs"; "cmaddrA"; "robjs_okA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "patchf"; "rho_patch"; "T_ok"; "tvv"; "remove_nth"; "tnz"; "tvd"; "tvz"; "tv_below"; "robj_tracked"; "T0"; "robj_stack"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "pos_add_nat"; "agree_vals"; "new_objs"; "call_linkP"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "M_MUL"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.ExampleMemcpy"; "NF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "SHADOW_OFF"; "IMG_HI"; "Sh"; "fs_frame_size"; "HIGH_SHADOW_END"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM.WithSegs.Sum.CallT"; "payA"; "ccount"; "csz"; "site_okA"; "Posts_malloc_sel"; "Posts_calloc_sel"; "Lbl_malloc_sel"; "Lbl_calloc_sel"; "ffpairs"; "is_cls"; "preA"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "in_rangesZ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB.TobjJAM"; "is_shadowZ"; "mem_keptWA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundV"; "U"; "@Corelib.Init.Nat"; "add"; "@Corelib.Init.Peano"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "forallb_lazy"; "existsb_lazy"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "mk_pf"; "pfacts"; "uleq_pf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA"; "mk_pf_f"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "uleq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.XformFast"; "robj_stack_p"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SummaryA3"; "import_okPA3"; "import_postA3"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymSoundW SymFrame SymEntail SymCFG SymSummary ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA GlueA SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue TobjJV.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import Geometry Budget Model RtCells Iface IfaceEx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SummaryA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SummaryA3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import BudA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import CfgGenTA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibB Require Import TobjJA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require XformFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.DigFastA.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.EntailFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition is_shadowZ (a : Z) : Prop := ltac2:(tb__ "0|0|
S4S4bS114Va;A2S4dVa;S118A2A2").

Lemma Sh_is_shadow : ltac2:(tb__ "0|0|
S0S4S4bZ0R1A2S4dR1S4eZ2Z2fA2A2A2S12aS116R2A1A1F_;Fx;").
Proof.
  intros x Hx. unfold is_shadowZ, Sh, SHADOW_OFF, HIGH_SHADOW_END.
  split; [pose proof (Z.div_pos x 8); lia|].
  assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma word_byte_of_shadow : ltac2:(tb__ "0|0|
S0S0S12aR2A1S4S4bZ0R2A2S4dR2Z8A2A2S12aS60Q40S38R4R3A2A2A1F_;F_;Fj;Fz;").
Proof.
  intros z j Hz Hj. unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in *.
  destruct (word_byte_range z j ltac:(lia) Hj) as (_ & -> & _).
  pose proof (Z.div_mod z 8 ltac:(lia)). pose proof (Z.mod_pos_bound z 8 ltac:(lia)).
  split; [|lia].
  assert (2147450880 / 8 * 8 = 2147450880) by reflexivity.
  assert (2147450880 / 8 <= z / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

Definition mem_keptWA (CST XGL : list (Z * Z)) (A A' : AA) (m0 m1 : word -> option byte) : Prop := ltac2:(tb__ "0|4|
S0S0S4S4bZ0M0R2A2S4dR2S4eZ2Z2fA2A2A2S6S4Sc9VCST;VA;R3A3Sc9VCST;VA';R3A3A2S129VXGL;R3A2A2S4S4bG0R3A2S4dR3Z8A2A2S5S3S10S5fQ8A1M1A1M2Vm0;S38S116R5A1R4A2A1S13G1A1M3A3A1S5S3G2Vm1;S38S116R6A1R5A2A1G3A3A1F_;F_;F_;F_;Fj;Fx;").

Section WithSegs.
Variable segs : list Segment.
Variable E : aentry.
Variable AInv : ltac2:(tb__ "0|0|
S3bS1cSbS5fQ40A1A1S6cOF_;F_;F_;F_;").
Variables CST XGL : list (Z * Z).

Hypothesis ALA : ltac2:(tb__ "0|0|
Sf2Vsegs;VAInv;VCST;A3").

Hypothesis HCST : ltac2:(tb__ "0|0|
S0S129VCST;R1A2S4S4bZ0R2A2S4dR2S115A2A2F_;Fa;").
Hypothesis HXGL : ltac2:(tb__ "0|0|
S0S129VXGL;R1A2S4S4bZ0R2A2S4dR2S115A2A2F_;Fa;").

Ltac hcst H := match type of H with _ /\ _ => let H' := fresh in destruct H as [H H']; apply HCST in H | _ => apply HCST in H end.

Lemma HFLAG : ltac2:(tb__ "0|3|
S3bS1cSbS5fQ40A1A1S6cSdS0S0A2M0VAInv;R5R4R3R2A4S58G0R2S3fR6A1A3S4S4bS115ScfS3dR7A1M1R3A2M2A2S4bS4cG2Z1A2S43G1A1A2A2F_;F_;Ffs;Fmd;Ftp;Frho;FA;").
Proof using ALA.
  intros A rho tp md [f sz] HM Hin. destruct (law_blocks _ _ _ ALA A rho tp md HM) as (_ & _ & HFr).
  destruct (HFr f sz Hin) as (_ & _ & _ & _ & _ & G & G' & _). exact (conj G G').
Qed.
Lemma HKW : ltac2:(tb__ "0|1|
S3bS3bS5fQ40A1S10S5fQ8A1A1F_;M0G0ScaVCST;VXGL;R4R3R2R1A6S12bVCST;VXGL;R5R4R3R2A6F_;Fm1;Fm0;FA';FA;").
Proof using . intros A A' m0 m1 [_ H] x j _ Hc Hj. exact (H x j Hc Hj). Qed.

Definition cmaddrA (Ai : AA) (x : option Z) (a : Z) : Prop := ltac2:(tb__ "0|3|
S6S4S4bS43S3dVAi;A1A1Va;A2S4dVa;S4eZ2Z2fA2A2A2S6S4S129VCST;Va;A2S5Sd5Va;A1A1A2S6S7S0S0S7S0S0S4S58SdS0S0A2M0SeS0S0R2R1A4M1S3cVAi;A1A3S4S5S3S10S0A1Vx;S12S0R2A2A3A1S4S4bR2Va;A2S4dVa;S4cR2R1A2A2A2M2A2A2Ln;A2Lb;A2S7S0S0S7S0S0S4S58G0G1S3fVAi;A1A3G2A2Ls;A2Lf;A2A2A2A2").

Lemma cmaddrA_mut : ltac2:(tb__ "0|0|
S3bS10S0A1S0SfbR3R2R1A3Sf3VCST;R4R2A3F_;Fa;Fx;FAi;").
Proof using .
  intros Ai x a [H|[H|[(b & n & Hin & _ & Hr)|(f & s & Hin & Hr)]]].
  - left. exact H.
  - right; right; right. exact (proj1 H).
  - right; left. exists b, n. auto.
  - right; right; left. exists f, s. auto.
Qed.

Lemma cmaddrA_not_errno : ltac2:(tb__ "0|0|
S3bS10S0A1S0S1cSbS5fQ40A1A1S6cVAInv;R6R3R2R1A4SfbR7R6R5A3S5Sd5R6A1A1F_;F_;Fmd;Ftp;Frho;Fa;Fx;FAi;").
Proof using ALA.
  intros Ai x a rho tp md HM [H|[H|[(b & n & Hin & _ & Hr)|(f & s & Hin & Hr)]]] He; unfold errno_addrA, ERRNO_A in He.
  - pose proof (topG_range (aa_geom Ai)) as TG. unfold IMG_HI in *. lia.
  - exact (proj2 H He).
  - destruct (law_blocks _ _ _ ALA Ai rho tp md HM) as (_ & HBl & _). destruct (HBl b n Hin) as (_ & _ & _ & _ & G). unfold IMG_HI in G. lia.
  - destruct (law_blocks _ _ _ ALA Ai rho tp md HM) as (_ & _ & HFr). destruct (HFr f s Hin) as (_ & _ & _ & G & _). unfold IMG_HI in G. lia.
Qed.
Lemma cmaddrA_client : ltac2:(tb__ "0|0|
S3bS10S0A1S0SfbR3R2R1A3Sc9VCST;R4R2A3F_;Fa;Fx;FAi;").
Proof using . intros Ai x a H. left. eapply cmaddrA_mut; eauto. Qed.

Lemma cmaddrA_weaken : ltac2:(tb__ "0|0|
S3bS0S0SfbR3S12S0R2A2R1A3SfbR4S13S0A1R2A3F_;Fa;Fx;FAi;").
Proof using .
  intros Ai x a [H|[H|[(b & n & Hin & _ & Hr)|H]]]; [left; exact H | right; left; exact H | | right; right; right; exact H].
  right; right; left. exists b, n. repeat split; [exact Hin | discriminate | lia | lia].
Qed.

Ltac cm_stack H := first [exact H | match goal with E : aa_geom _ = aa_geom _ |- _ => first [rewrite E; exact H | rewrite <- E; exact H] end].
Ltac top_rng H := match type of H with context [topG ?G] => let TG := fresh "TG" in pose proof (topG_range G) as TG end.

Lemma client_not_shadow : ltac2:(tb__ "0|0|
S3bS0S1cSbS5fQ40A1A1S6cVAInv;R5R3R2R1A4Sc9VCST;R6R5A3S5S12aR6A1A1F_;F_;Fmd;Ftp;Frho;Fa;FAi;").
Proof using ALA HCST.
  intros Ai a rho tp md HM Hc Hs. unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in Hs.
  pose proof (law_client_app _ _ _ ALA Ai rho tp md a HM Hc) as H. pose proof (topG_range (aa_geom Ai)) as TG.
  unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in H. lia.
Qed.
Lemma cmaddrA_not_shadow : ltac2:(tb__ "0|0|
S3bS10S0A1S0S1cSbS5fQ40A1A1S6cVAInv;R6R3R2R1A4SfbR7R6R5A3S5S12aR6A1A1F_;F_;Fmd;Ftp;Frho;Fa;Fx;FAi;").
Proof using ALA HCST.
  intros Ai x a rho tp md HM Hc. eapply client_not_shadow; [exact HM | eapply cmaddrA_client; exact Hc].
Qed.

Lemma client_range : ltac2:(tb__ "0|0|
S3bS0S1cSbS5fQ40A1A1S6cVAInv;R5R3R2R1A4Sc9VCST;R6R5A3S4S4bZ0R6A2S4dR6S4eZ2Z2fA2A2A2F_;F_;Fmd;Ftp;Frho;Fa;FAi;").
Proof using ALA HCST.
  intros Ai a rho tp md HM Hc.
  pose proof (law_client_app _ _ _ ALA Ai rho tp md a HM Hc) as H. pose proof (topG_range (aa_geom Ai)) as TG.
  unfold IMG_HI in H. lia.
Qed.

Lemma live_noshadow : ltac2:(tb__ "0|0|
S3bS1cSbS5fQ40A1A1S6cS0S0VAInv;R6R5R4R3A4S58SdS0S0A2SeS0S0R3R2A4S3cR7A1A3S6S4bS4cR4R3A2Z7fff7000A2S4bZ10007fff8000R4A2A2F_;F_;Fn;Fb;Fmd;Ftp;Frho;FA;").
Proof using ALA HCST.
  intros A rho tp md b n HM Hin.
  destruct (law_blocks _ _ _ ALA A rho tp md HM) as (_ & HBl & _). destruct (HBl b n Hin) as (G1 & _ & G3 & G4 & G5).
  pose proof (topG_range (aa_geom A)) as TG.
  assert (CL : forall a, b <= a < b + n -> client_addrA CST A a) by (intros a Ha; left; right; left; exists b, n; auto).
  destruct (Z_lt_ge_dec b 2147446784) as [Hb|Hb].
  - left. destruct (Z_le_gt_dec (b + n) 2147446784) as [H|H]; [exact H|]. exfalso.
    pose proof (law_client_app _ _ _ ALA A rho tp md 2147446784 HM (CL 2147446784 ltac:(lia))) as X.
    unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in X. lia.
  - right. pose proof (law_client_app _ _ _ ALA A rho tp md b HM (CL b ltac:(lia))) as X.
    unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in X. lia.
Qed.
Lemma frame_noshadow : ltac2:(tb__ "0|3|
S3bS1cSbS5fQ40A1A1S6cS0S0VAInv;R6R5R4R3A4S58SdS0S0A2SeS0S0R3R2A4S3fR7A1A3S4S6S4bS4cR4R3A2Z7fff7000M0A2S4bZ10007fff8000M1R4A2A2S6S4dScfS3dR8A1SeS0S0R4R3A4A2M2G0A2S4bG1G2A2A2A2F_;F_;Fs;Ff;Fmd;Ftp;Frho;FA;").
Proof using ALA HCST.
  intros A rho tp md f s HM Hin.
  destruct (law_blocks _ _ _ ALA A rho tp md HM) as (_ & _ & HFr). destruct (HFr f s Hin) as (_ & _ & F3 & F4 & F5 & F6 & F7 & _).
  pose proof (topG_range (aa_geom A)) as TG.
  assert (CL : forall a, f <= a < f + s -> client_addrA CST A a) by (intros a Ha; left; right; right; left; exists f, s; auto).
  split.
  - destruct (Z_lt_ge_dec f 2147446784) as [Hb|Hb].
    + left. destruct (Z_le_gt_dec (f + s) 2147446784) as [H|H]; [exact H|]. exfalso.
      pose proof (law_client_app _ _ _ ALA A rho tp md 2147446784 HM (CL 2147446784 ltac:(lia))) as X.
      unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in X. lia.
    + right. pose proof (law_client_app _ _ _ ALA A rho tp md f HM (CL f ltac:(lia))) as X.
      unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in X. lia.
  - pose proof (law_client_app _ _ _ ALA A rho tp md _ HM (or_intror (ex_intro _ (f, s) (conj Hin eq_refl)))) as X.
    unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in X. lia.
Qed.

Lemma law_blocks' : ltac2:(tb__ "0|13|
S3bS1cSbS5fQ40A1A1S6cVAInv;R4R3R2R1A4S4Sd6S17SdS0S0A2M0S3cR5A1S3fR5A1A3A1S4S0S0S58G0SeS0S0R2R1A4M1S3cR7A1A3S4S4bZ1M2R2A2S4S3S0S55R3Z10M3A2Z0M4A3S4S4bZ1000M5R3A2S4S4bS4cS4cR3R2A2M6Z800A2S43S3dR8A1M7A1M8A2S4S4S4bS4cS115G5A2R3A2S4bZ644000R3A2A2S4S6S4bG6S114A2S4bS118R3A2A2S4S6S4bG6Z7fff8000M9A2S4bZ10007fff8000MaR3A2A2S4bG8Z7fffff800000A2A2A2MbA2A2A2A2A2F_;Fn;Fb;S0S0S58G0G1S3fR7A1A3S4S3S0S55R3Z40McA2G4A3S4S3S0S55R2GcA2G4A3S4S4bGcR2A2S4S4S4S4bS115R3A2S4bZ643000MdR3A2A2GbA2S4S4bG6G8A2S4S4S4S4bS115ScfG7SeS0S0R3R2A4A2MeA2S4bGdGeA2A2S4S6S4bS4cGeG2A2MfS114A2S4bS118GeA2A2S6S4bGfG9A2S4bGaGeA2A2A2A2S4S4bGfG8A2S4S0S0S58G0G1S3cRaA1A3S6S4bG6ScfS3dRbA1SeS0S0R6R5A4A2M10A2M11S4bS4cG10G2A2M12S54R3G3A2A2A2F_;Fn;Fb;S0S0S58G0G1S3fRaA1A3S6G11S4bG12R3A2A2F_;Fs';Ff';A2A2A2A2A2A2A2A2F_;Fs;Ff;A2A2F_;Fmd;Ftp;Frho;FA;").
Proof using ALA HCST.
  intros A rho tp md HM. destruct (law_blocks _ _ _ ALA A rho tp md HM) as (HPD & HBl & HFr). pose proof (topG_range (aa_geom A)) as TG.
  unfold SHADOW_OFF, HIGH_SHADOW_END, IMG_HI in *.
  split; [exact HPD|]. split.
  - intros b n Hin. destruct (HBl b n Hin) as (G1 & G2 & G3 & G4 & G5). pose proof (live_noshadow A rho tp md b n HM Hin).
    unfold IMG_HI in *. repeat split; try assumption; lia.
  - intros f s Hin. destruct (HFr f s Hin) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9). pose proof (frame_noshadow A rho tp md f s HM Hin) as [X Y].
    unfold IMG_HI in *. repeat split; try assumption; try lia.
Qed.

Definition robjs_okA (Ai : AA) (x : option Z) (rho : valuation) (R : list sobj) : Prop := ltac2:(tb__ "0|1|
S1eS0S58S1eR2VR;A3S4S4bS15S0S0S29Vrho;R3A2M0A3R2A2S4dR2S14S0S0G0A3A2A2SfbVAi;Vx;R3A3F_;F_;Fa;Fo;").

Lemma robjs_okA_weaken : ltac2:(tb__ "0|0|
S3bS0S1cSbS1eA1SfcR4S12S0R3A2R2R1A4SfcR5S13S0A1R3R2A4F_;FR;Frho;Fx;FAi;").
Proof using . intros Ai x rho R H o a Ho Hr. eapply cmaddrA_weaken. exact (H o a Ho Hr). Qed.

Lemma robjs_in_ranges : ltac2:(tb__ "0|1|
S3bS10S0A1S1cSbS1eA1S5fQ40M0A1SfcR5R4R3R2A4S6aR4R3R2A3SfbR7R6S60G0R3A2A3F_;F_;Fa;FR;Frho;Fx;FAi;").
Proof using . intros Ai x rho R a H (o & Hin & Hr). exact (H o _ Hin Hr). Qed.

Lemma AInv_absorb : ltac2:(tb__ "0|0|
S3bS1cSbS5fQ40A1A1S6cSbS1eA1S7bS67VAInv;R7R6R5R4A4SfcR8S13S0A1R7R4A4VAInv;R9S69S68R8R5R4A3R3A2R7R6A4F_;F_;Fsb;Fms;FR;Fmd;Ftp;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho tp md R ms sb HM HR. eapply (law_frame _ _ _ ALA); [exact HM| |].
  - intros a Hnm _. destruct (in_ranges_dec rho R a) as [Hi|Hn]; [|apply rm_absorb_out; exact Hn].
    exfalso. apply Hnm. eapply cmaddrA_mut. eapply robjs_in_ranges; eauto.
  - intros a Hsh Hdef. destruct (in_ranges_dec rho R a) as [Hi|Hn]; [|rewrite rm_absorb_out by exact Hn; exact Hdef].
    exfalso. pose proof (robjs_in_ranges Ai None rho R a HR Hi) as Hc.
    apply (cmaddrA_not_shadow Ai None (bv_unsigned a) rho tp md HM Hc).
    destruct Hsh as (f & sz & Hin & Hr).
    destruct (law_blocks _ _ _ ALA Ai rho tp md HM) as (_ & _ & HFr). destruct (HFr f sz Hin) as (_ & _ & G64 & Ghs & Gce & _).
    pose proof (topG_range (aa_geom Ai)) as TG.
    pose proof (Sh_is_shadow f ltac:(unfold IMG_HI in Ghs; lia)) as S1.
    pose proof (Sh_is_shadow (f + sz - 1) ltac:(unfold IMG_HI in Ghs; lia)) as S2.
    unfold is_shadowZ in *. lia.
Qed.

Lemma AInv_patch : ltac2:(tb__ "0|1|
S3bS3bS10S0A1S1cS1cS1cSbS5fQ40A1M0A1S6cSbS1eA1VAInv;R9R4R3R2A4G0S3S10S5fQ8A1A1S1fR7R1A2S1fR6R1A2A3Fa;SfcRaR9R8R3A4S0SfbRcRbR1A3SfbReS13S0A1R2A3F_;Fa;VAInv;RdSfeR9SfdRaR9R5A3A2R7R6A4F_;F_;F_;F_;FR;Fmd;FtpL;FrhoL;Frho';Frho;Fx;FAi;FA2;").
Proof using ALA HCST.
  intros A2 Ai x rho rho' rhoL tpL md R HM Hrm HR Hsub.
  assert (HM' : AInv A2 (mkVal (rw rho') (rl rho') (rm rhoL)) tpL md).
  { eapply (law_vars _ _ _ ALA); [exact HM | reflexivity]. }
  eapply (law_frame _ _ _ ALA); [exact HM'| |].
  - intros a Hnm _. cbn [rho_patch rm]. unfold patchf. destruct (in_ranges_dec rho R a) as [Hi|Hn]; [|apply Hrm].
    exfalso. apply Hnm. eapply cmaddrA_mut. apply Hsub. eapply robjs_in_ranges; eauto.
  - intros a Hsh Hdef. cbn [rho_patch rm] in *. unfold patchf. destruct (in_ranges_dec rho R a) as [Hi|Hn]; [|rewrite Hrm; exact Hdef].
    exfalso. pose proof (Hsub _ (robjs_in_ranges Ai x rho R a HR Hi)) as Hc.
    apply (cmaddrA_not_shadow A2 None (bv_unsigned a) _ tpL md HM' Hc).
    destruct Hsh as (f & sz & Hin & Hr).
    destruct (law_blocks _ _ _ ALA A2 _ tpL md HM') as (_ & _ & HFr). destruct (HFr f sz Hin) as (_ & _ & G64 & Ghs & Gce & _).
    pose proof (topG_range (aa_geom A2)) as TG.
    pose proof (Sh_is_shadow f ltac:(unfold IMG_HI in Ghs; lia)) as S1.
    pose proof (Sh_is_shadow (f + sz - 1) ltac:(unfold IMG_HI in Ghs; lia)) as S2.
    unfold is_shadowZ in *. lia.
Qed.

Lemma KEPT_stepA : ltac2:(tb__ "0|1|
S3bS3bS10S0A1S1cS1cS7bS67SbS1eA1S1cSbS5fQ40A1M0A1S6cVAInv;RbR3R2R1A4SfcRcRaR9R5A4S0SfbReRcR1A3SfbReS13S0A1R2A3F_;Fa;ScaVCST;VXGL;ReRdS1fS69S68RbR7R9A3R8A2A1S1fRaA1A6G0S6aRdR9R1A3S3S10S5fQ8A1A1S1fRdR2A2S1fS69S68ReRaRcA3RbA2R2A2A3F_;Fa;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fs;Fms;FrhoL;Frho;Fx;FA2;FAi;").
Proof using ALA.
  intros Ai A2 x rho rhoL ms s R rho1 tp1 md1 HM1 HR Hsub Hkept a Hin.
  pose proof (robjs_in_ranges Ai x rho R a HR Hin) as Hc.
  rewrite <- (Z_to_bv_bv_unsigned 64 a). apply (proj1 Hkept); [apply bv_urange|].
  left. split; [eapply cmaddrA_client; eexact Hc | split; [eapply cmaddrA_client; exact (Hsub _ Hc) | exact (cmaddrA_not_errno Ai x _ rho1 tp1 md1 HM1 Hc)]].
Qed.

Lemma KEPT_stepA2 : ltac2:(tb__ "0|1|
S3bS3bS10S0A1S1cS1cS7bS67SbS1eA1S1cSbS5fQ40A1M0A1S6cVAInv;RbR3R2R1A4SfcRcRaR9R5A4SfcRcS13S0A1RaR6A4ScaVCST;VXGL;ReRdS1fS69S68RbR7R9A3R8A2A1S1fRaA1A6G0S6aRdR9R1A3S3S10S5fQ8A1A1S1fRdR2A2S1fS69S68ReRaRcA3RbA2R2A2A3F_;Fa;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;FR;Fs;Fms;FrhoL;Frho;Fx;FA2;FAi;").
Proof using ALA.
  intros Ai A2 x rho rhoL ms s R rho1 tp1 md1 HM1 HR HR2 Hkept a Hin.
  pose proof (robjs_in_ranges Ai x rho R a HR Hin) as Hc. pose proof (robjs_in_ranges A2 None rho R a HR2 Hin) as Hc2.
  rewrite <- (Z_to_bv_bv_unsigned 64 a). apply (proj1 Hkept); [apply bv_urange|].
  left. split; [eapply cmaddrA_client; eexact Hc | split; [eapply cmaddrA_client; exact Hc2 | exact (cmaddrA_not_errno Ai x _ rho1 tp1 md1 HM1 Hc)]].
Qed.

Section Sum.
Variable NP : positive.
Variable Kc : KcA.
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).
Variable FF : ltac2:(tb__ "0|0|
SbSdSdS0S0A2S0A2A1").
Variable BX : bxt.
Variable PA : AA -> Prop.
Hypothesis HKc : Kc_ok Kc.

Context {dF : Z}.
Hypothesis HBX : BXok_d dF BX.

Let JAi : ltac2:(tb__ "0|0|
S80S3bS0S64Fkc;FAi;Fnd;") := ltac2:(tb__ "0|0|
S90VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JA : ltac2:(tb__ "0|0|
S80S64Fnd;") := ltac2:(tb__ "0|0|
S87VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").
Let JAk : ltac2:(tb__ "0|0|
S80S3bS64FAi;Fnd;") := ltac2:(tb__ "0|0|
S94VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;VPA;Ab").

Lemma agree_vals_sym : ltac2:(tb__ "0|0|
S1S1cS1cS10aR3R2R1A3S10aR4R2R3A3F_;Fr2;Fr1;Fn;").
Proof using . clear. intros n r1 r2 [H1 H2]. split; [intros i Hi; symmetry; exact (H1 i Hi) | intros l; symmetry; exact (H2 l)]. Qed.
Lemma capK_same : ltac2:(tb__ "0|0|
S3bS3bS85VBX;R2A2S3SbSdS0S0A2A1S3cR2A1S3cR3A1A3S4bS3eR4A1S3eR3A1A2S85VBX;R4A2F_;F_;F_;FA';FA;").
Proof using . clear. intros A A' H EL HV. unfold capK in *. rewrite (large_live_same A A' EL). lia. Qed.
Lemma capK_insert : ltac2:(tb__ "0|3|
S3bS3bSbSdS0S0A2M0A1M1G1S0S0S85VBX;R6A2S3G1S3cR7A1M2S17G0R5R4A3A3S3G1G2S17G0R6SfG0SeS0S0R4R3A4R5A3A3A3S4bZ0R4A2S3S0S3eR9A1S4cS3eRaA1R5A2A3S85VBX;RaA2F_;F_;F_;F_;F_;Fn;Fp;Fl2;Fl1;FA';FA;").
Proof using .
  clear. intros A A' l1 l2 p n H E1 E2 Hn HV. unfold capK, LARGE_MIN in *. rewrite (large_live_insert A A' l1 l2 p n E1 E2), HV.
  destruct (64513 <=? n) eqn:E; [apply Z.leb_le in E|]; lia.
Qed.
Lemma capK_remove : ltac2:(tb__ "0|3|
S3bS3bSbSdS0S0A2M0A1M1G1S0S0S85VBX;R6A2S3G1S3cR7A1M2S17G0R5SfG0SeS0S0R3R2A4R4A3A3A3S3G1G2S17G0R6R5A3A3S4bS3eR9A1S3eR8A1A2S85VBX;R9A2F_;F_;F_;F_;Fn;Fp;Fl2;Fl1;FA';FA;").
Proof using .
  clear. intros A A' l1 l2 p n H E1 E2 HV. unfold capK, LARGE_MIN in *. rewrite (large_live_remove A A' l1 l2 p n E1 E2).
  destruct (64513 <=? n); lia.
Qed.

Lemma capN_same_live : ltac2:(tb__ "0|0|
S3bS3bS1S1cS1cSbSdS1bS1bA2A1S86VBX;R6R3R1A4S3SbSdS0S0A2A1S3cR6A1S3cR7A1A3S10aR6R5R4A3S3SaS105R7R4A2ScA3S86VBX;R9R6R5A4F_;F_;F_;F_;Ftv;FrhoP;Frho;Fnx;FA';FA;").
Proof using .
  clear. intros A A' nx rho rhoP tv H EL Hag Hb. unfold capN in *. rewrite (small_live_same A A' EL), (cntS_agree nx rho rhoP tv Hag Hb). exact H.
Qed.
Lemma capN_insert : ltac2:(tb__ "0|4|
S3bS3bS1S1cS1cSbSdS1bS1bA2M0A1G0SbSdS0S0A2M1A1M2G2S0S0S86VBX;RbR8R6A4S3G2S3cRcA1M3S17G1R5R4A3A3S3G2G3S17G1R6SfG1SeS0S0R4R3A4R5A3A3A3S10aRcRbRaA3S3SaS105RdRaA2ScA3S3G1S100RcRaA2SeS0S0R7R6A4A3S5S3S0R8Z0A3A1S86VBX;R11ReSfG0RcRdA3A4F_;F_;F_;F_;F_;F_;F_;Fn;Fp;Fl2;Fl1;Fnewt;Ftv;FrhoP;Frho;Fnx;FA';FA;").
Proof using .
  clear. intros A A' nx rho rhoP tv newt l1 l2 p n H E1 E2 Hag Hb Enew Hp. unfold capN in *.
  rewrite (small_live_insert A A' l1 l2 p n E1 E2), cntS_cons, (cntS_agree nx rho rhoP tv Hag Hb), Enew, (is_smallZ_large (p, n) Hp).
  unfold is_large. cbn [snd]. destruct (64513 <=? n); cbn [negb]; lia.
Qed.
Lemma capN_remove : ltac2:(tb__ "0|4|
S3bS3bS1S1cS1cSbSdS1bS1bA2M0A1S18G0SbSdS0S0A2M1A1M2G2S0S0S86VBX;RcR9R7A4S3G2S3cRdA1M3S17G1R5SfG1SeS0S0R3R2A4R4A3A3A3S3G2G3S17G1R6R5A3A3S10aRdRcRbA3S3SaS105ReRbA2ScA3S3S10G0A1S59G0RcRbA3S12G0RaA2A3S3G1S100RfRbA2SeS0S0R8R7A4A3S102R10RcA2S86VBX;R13R10S101G0ReRfA3A4F_;F_;F_;F_;F_;F_;F_;F_;Fn;Fp;Fl2;Fl1;Ft;Fi;Ftv;FrhoP;Frho;Fnx;FA';FA;").
Proof using .
  clear. intros A A' nx rho rhoP tv i t l1 l2 p n H E1 E2 Hag Hb Hnth Et Hnz. unfold capN in *.
  assert (Hp : p <> 0). { intros E0. apply Hnz. unfold tnz. change (bv_unsigned (eval rho (fst t))) with (fst (tvv rho t)). rewrite Et. exact E0. }
  assert (Hb' : tv_below nx (remove_nth i tv) = true).
  { unfold tv_below in *. apply forallb_forall. intros t' Ht'. apply (proj1 (forallb_forall _ _) Hb). eapply remove_nth_In. exact Ht'. }
  rewrite (small_live_remove A A' l1 l2 p n E1 E2), (cntS_agree nx rho rhoP _ Hag Hb'), (cntS_remove_nth rho tv i t Hnth), Et, (is_smallZ_large (p, n) Hp).
  unfold is_large. cbn [snd]. destruct (64513 <=? n); cbn [negb]; lia.
Qed.

Lemma prim_room_JA : ltac2:(tb__ "0|0|
S0S1S80S3bS1cS77R5VBX;A2S86VBX;R3R2S7cR4A1A4S3SaS82R6R5A2ScA3S47R5A1F_;F_;F_;Frho;FA;Fnd;Fnx;Fd;").
Proof using .
  clear. intros d nx nd A rho HB HC Hnb. exact (prim_room_capN d BX A rho (nd_tv nd) HB HC (nd_below_len nx nd Hnb)).
Qed.

Lemma sec_room_JA : ltac2:(tb__ "0|1|
SbS6fA1SdS0S0A2S0S3bS1cS76VBX;A1S85VBX;R3A2S4bZ0M0S15S0S0R6A3A2S4bG0R6A2S73R9S8eS75VBX;A1R8R7A3S3eR6A1S41R6A1S40R6A1R5A6S48R7A1F_;F_;F_;F_;F_;Frho;FA;Fkc;Fpot;Fb;").
Proof using .
  clear. intros b pot kc A rho [_ HKS] HCK Hp Hk HB. pose proof (BUD_sums_nonneg _ _ _ _ _ _ HB) as [N1 _].
  destruct HB as (_ & _ & _ & _ & _ & _ & _ & B1 & _). unfold bxa in B1. cbn [fst] in B1.
  apply (sec_room_of_cap BX A HKS HCK). unfold bxV. lia.
Qed.

Ltac chain_same_tv Hlink Hnb :=
  cbn zeta; intros ? ? _ _ Hut;
  eapply untracked_agree; [eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch] | | exact Hut];
  exact (proj1 (nd_below_split _ _ Hnb)).

Ltac cen_same_tv Hlink Hnb HLeq :=
  cbn zeta; intros ? Hcl _ _ Hut; split; [first [exact Hcl | rewrite <- HLeq; exact Hcl]|];
  eapply untracked_agree; [apply agree_vals_sym; eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch] | | exact Hut];
  exact (proj1 (nd_below_split _ _ Hnb)).
Ltac capK_same_tac HCK HLeq HVeq :=
  apply (capK_same _ _ HCK HLeq); rewrite HVeq;
  repeat match goal with |- context [bv_unsigned ?x] => lazymatch goal with H : 0 <= bv_unsigned x < _ |- _ => fail | _ => pose proof (bv_urange x) end end; lia.

Ltac capN_same_tac HCN Hlink Hnb HLeq :=
  eapply (capN_same_live _ _ _ _ _ _ HCN);
  [first [exact HLeq | symmetry; exact HLeq] | eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch] | exact (proj1 (nd_below_split _ _ Hnb))].

Lemma cen_insert : ltac2:(tb__ "0|3|
S3bS3bS1cS1cS1SbSdS1bS1bA2M0A1G0SbSdS0S0A2M1A1M2G2S0S0S10aR7R9R8A3S3SaS105R8R7A2ScA3S3G2S3cRcA1S17G1R6SfG1SeS0S0R4R3A4R5A3A3A3S3G2S3cReA1S17G1R7R6A3A3S3G1S100RcR9A2SeS0S0R6R5A4A3S5S3S0R7Z0A3A1G1S58G1R1S3cR11A1A3S4bS72S14S0S0R2A3A2S5S58G1R3VFB;A3A1S83R12SfG0RfR10A3R4A3S4S58G1R5S3cR16A1A3S83R14R11R5A3A2F_;F_;F_;F_;Fbn;F_;F_;F_;F_;F_;F_;Fn;Fp;Fk2;Fk1;Fnewt;Ftv;Fnx;FrhoP;Frho;FA2;FAi;").
Proof using .
  clear. intros Ai A2 rho rhoP nx tv newt k1 k2 p n Hag Hbt E2 E1 Enew Hp bn Hcl _ _ Hut.
  pose proof (proj1 (untracked_tv _ _ _) Hut) as HU.
  assert (Hne : (p, n) <> bn).
  { rewrite <- Enew. apply (HU newt (or_introl eq_refl)). unfold tnz. change (bv_unsigned (eval rhoP (fst newt))) with (fst (tvv rhoP newt)). rewrite Enew. exact Hp. }
  split.
  - rewrite E1. rewrite E2 in Hcl. apply in_app_or in Hcl as [H|[H|H]]; [apply in_or_app; left; exact H | exfalso; exact (Hne H) | apply in_or_app; right; exact H].
  - apply (proj2 (untracked_tv _ _ _)). intros t Ht Hnz.
    assert (Hb : (sv_below nx (fst t) && sv_below nx (snd t)) = true) by exact (proj1 (forallb_forall _ _) Hbt t Ht).
    rewrite <- (tvv_agree nx rho rhoP t Hag Hb). apply (HU t (or_intror Ht)). apply (proj2 (tnz_agree nx rho rhoP t Hag Hb)). exact Hnz.
Qed.

Lemma pclFA_cmaddrA : ltac2:(tb__ "0|1|
S3bS0S89VFB;R2A2S8aVFF;R3A2S84Vrho0;R4A2S8dVCST;Vrho0;VFB;VFF;R4A5S6SfbR6S13S0A1R5A3S7SdS0S0A2M0G0S4S58G0R1S3fR7A1A3S3S0R6ScfS3dR7A1R1A2A3A2Lfs;A2A2F_;F_;F_;F_;Fa;FAi;").
Proof using .
  intros Ai a HB HFF HT [H|[H|[(b & n & Hin & Hr)|(f & s & fl & Hin & [Hr| ->])]]].
  - left; left. rewrite (TPA_top rho0 Ai HT). exact H.
  - left; right; left; exact H.
  - left; right; right; left. exists b, n. split; [exact (HB _ Hin)|]. split; [discriminate | exact Hr].
  - left; right; right; right. exists f, s. split; [exact (proj1 (HFF _ _ _ Hin)) | exact Hr].
  - right. exists (f, s). destruct (HFF _ _ _ Hin) as [H1 H2]. auto.
Qed.

Lemma pclFA_client : ltac2:(tb__ "0|0|
S3bS0S89VFB;R2A2S8aVFF;R3A2S84Vrho0;R4A2S8dVCST;Vrho0;VFB;VFF;R4A5Sc9VCST;R6R5A3F_;F_;F_;F_;Fa;FAi;").
Proof using .
  intros Ai a HB HFF HT Hp. destruct (pclFA_cmaddrA Ai a HB HFF HT Hp) as [H|(fs & Hin & ->)].
  - eapply cmaddrA_client; exact H.
  - right. exists fs. auto.
Qed.

Lemma pclFA_range : ltac2:(tb__ "0|0|
S3bS1cSbS5fQ40A1A1S6cS0VAInv;R5R4R3R2A4S89VFB;R6A2S8aVFF;R7A2S84Vrho0;R8A2S8dVCST;Vrho0;VFB;VFF;R5A5S4S4bZ0R6A2S4dR6S4eZ2Z2fA2A2A2F_;F_;F_;F_;F_;Fa;Fmd;Ftp;Frho;FAi;").
Proof using ALA HCST.
  intros Ai rho tp md a HM HB HFF HT Hp. exact (client_range Ai a rho tp md HM (pclFA_client Ai a HB HFF HT Hp)).
Qed.

Lemma pclFA_not_errno : ltac2:(tb__ "0|0|
S3bS1cSbS5fQ40A1A1S6cS0VAInv;R5R4R3R2A4S89VFB;R6A2S8aVFF;R7A2S84Vrho0;R8A2S8dVCST;Vrho0;VFB;VFF;R5A5S5Sd5R6A1A1F_;F_;F_;F_;F_;Fa;Fmd;Ftp;Frho;FAi;").
Proof using ALA.
  intros Ai rho tp md a HM HB HFF HT Hp.
  destruct (pclFA_cmaddrA Ai a HB HFF HT Hp) as [Hc|(fs & Hfs & ->)]; [exact (cmaddrA_not_errno Ai None a rho tp md HM Hc)|].
  intros He. unfold errno_addrA, ERRNO_A in He. destruct fs as [f sz].
  destruct (law_blocks _ _ _ ALA Ai rho tp md HM) as (_ & _ & HFr). destruct (HFr f sz Hfs) as (_ & _ & _ & _ & _ & G & _). unfold IMG_HI in G. lia.
Qed.

Lemma pcl_not_in_R : ltac2:(tb__ "0|1|
S3bS10S0A1S1cSbS5fQ40M0A1A1S6cSbS1eA1S0VAInv;R7R5R4R3A4S89VFB;R8A2S8aVFF;R9A2S84Vrho0;RaA2SfcRbRaR9R6A4S4S4bZ0R6A2S4dR6S4eZ2Z40A2A2A2S95VCST;VXGL;Vrho0;VFB;VFF;R7A6S5S6aRcR9S61G0R8A2A3A1F_;F_;F_;F_;F_;F_;F_;Fa;FR;Fmd;Ftp;Frho;Fx;FAi;").
Proof using ALA HCST HXGL.
  intros Ai x rho tp md R a HM HB HFF HT HR Ha Hp Hin.
  pose proof (robjs_in_ranges Ai x rho R _ HR Hin) as Hc. rewrite Z_to_bv_unsigned, bv_wrap_small in Hc by (rewrite two64; lia).
  apply (cmaddrA_not_shadow Ai x a rho tp md HM Hc).
  destruct Hp as (y & Hy & [Hpy|Hgy] & ->).
  - apply Sh_is_shadow. exact (pclFA_range Ai rho tp md y HM HB HFF HT Hpy).
  - apply Sh_is_shadow. apply HXGL in Hgy. unfold IMG_HI, LOW_SHADOW_BEG in Hgy. lia.
Qed.

Lemma flag_not_in_R : ltac2:(tb__ "0|2|
S3bS10S0A1S1cSbS5fQ40M0A1A1S6cSbS1eA1SdS0S0A2M1VAInv;R7R5R4R3A4SfcR8R7R6R3A4S58G1R3S3fR9A1A3S5S6aR8R5S61G0ScfS3dRaA1R4A2A2A3A1F_;F_;F_;Ffs;FR;Fmd;Ftp;Frho;Fx;FAi;").
Proof using ALA HCST.
  intros Ai x rho tp md R fs HM HR Hfs Hin.
  destruct (law_blocks _ _ _ ALA Ai rho tp md HM) as (_ & HBl & HFr). destruct fs as [f s].
  destruct (HFr f s Hfs) as (_ & _ & _ & _ & _ & G1 & G2 & G3 & G4). pose proof (topG_range (aa_geom Ai)) as TG. unfold IMG_HI in G1.
  pose proof (robjs_in_ranges Ai x rho R _ HR Hin) as Hc. rewrite Z_to_bv_unsigned, bv_wrap_small in Hc by (rewrite two64; lia).
  destruct Hc as [H|[H|[(b & n & Hin' & _ & Hr)|(f' & s' & Hin' & Hr)]]].
  - lia.
  - hcst H. unfold IMG_HI, LOW_SHADOW_BEG in H. lia.
  - destruct (G3 b n Hin'). lia. lia.
  - destruct (G4 f' s' Hin'). lia. lia.
Qed.

Lemma keptFA_step : ltac2:(tb__ "0|4|
S3bS3bS10S0A1S1cS1cS7bS67SbS1eA1SbS5fQ40A1M0A1M1S6cG1S6cS1cVAInv;RdRaR5R4A4VAInv;RdRaR4R3A4S89VFB;RfA2S8aVFF;R10A2S89VFB;R10A2S8aVFF;R11A2S84Vrho0;R13A2S3S44S3dR13A1S3dR14A1A3SfcR15R13R12ReA4S92VCST;VXGL;Vrho0;VFB;VFF;S1fVrho0;A1M2S1fR13A1M3A7ScaVCST;VXGL;R17R16S1fS69S68R14R10R12A3R11A2A1G3A6G0S3S10S5fQ8A1A1S1fRdR1A2S1fR15R1A2A3Fa;S92VCST;VXGL;Vrho0;VFB;VFF;G2S1fSfeRdSfdR16RdR12A3A2A1A7F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Frho';FmdL;FtpL;Fmd;Ftp;FR;Fs;Fms;FrhoL;Frho;Fx;FA2;FAi;").
Proof using ALA HCST HXGL.
  intros Ai A2 x rho rhoL ms s R tp md tpL mdL rho' HM HM2 HB HFF HB2 HFF2 HT HG HR [HK1 HK2] Hkept Hrm.
  pose proof (TPA_kept rho0 Ai A2 HG HT) as HT2.
  assert (CS : forall y, 0 <= y -> pclFA CST rho0 FB FF y \/ in_rangesZ XGL y -> client_shadowA CST XGL Ai (Sh y) /\ client_shadowA CST XGL A2 (Sh y)).
  { intros y Hy [Hp|Hg].
    - split; left; exists y; split; [eapply pclFA_client; eauto | reflexivity | eapply pclFA_client; eauto | reflexivity].
    - split; right; exists y; auto. }
  split.
  - intros a Ha Hp. cbn [rho_patch rm]. unfold patchf.
    destruct (in_ranges_dec rho R (Z_to_bv 64 a)) as [Hi|Hn]; [apply HK1; assumption|].
    rewrite Hrm. transitivity (rm (rho_sub (rho_absorb rho R ms) s) (Z_to_bv 64 a)).
    + apply (proj1 Hkept); [exact Ha|]. destruct Hp as [Hp|[Hs Hd]].
      * left. split; [eapply pclFA_client; eauto|]. split; [eapply pclFA_client; eauto | exact (pclFA_not_errno Ai rho tp md a HM HB HFF HT Hp)].
      * right. destruct Hs as (y & Hy & Hpy & ->). destruct (CS y Hy Hpy) as [C1 C2]. split; [exact C1|]. split; [exact C2|].
        rewrite rm_absorb_out by exact Hn. rewrite (HK1 _ Ha (or_intror (conj (ex_intro _ y (conj Hy (conj Hpy eq_refl))) Hd))). exact Hd.
    + rewrite rm_absorb_out by exact Hn. apply HK1; assumption.
  - intros a j Ha Hp Hj Hdef. cbn [rho_patch rm]. unfold patchf.
    destruct Hp as (y & Hy & Hpy & ->).
    assert (Hy47 : 0 <= y < 2 ^ 47).
    { destruct Hpy as [Hpy|Hgy]; [exact (pclFA_range Ai rho tp md y HM HB HFF HT Hpy)|]. apply HXGL in Hgy. unfold IMG_HI, LOW_SHADOW_BEG in Hgy. lia. }
    assert (NW : ~ in_ranges rho R (word_byte (Sh y) j)).
    { intros Hin. pose proof (robjs_in_ranges Ai x rho R _ HR Hin) as Hc.
      apply (cmaddrA_not_shadow Ai x _ rho tp md HM Hc). apply word_byte_of_shadow; [apply Sh_is_shadow; exact Hy47 | exact Hj]. }
    destruct (in_ranges_dec rho R (word_byte (Sh y) j)) as [Hi|Hn]; [exfalso; exact (NW Hi)|].
    rewrite Hrm. apply (HKW Ai A2 _ _ Hkept y j Hy47); [| exact Hj |].
    + destruct Hpy as [Hpy|Hgy]; [left; split; eapply pclFA_client; eauto | right; exact Hgy].
    + rewrite rm_absorb_out by exact Hn. apply HK2; try assumption. exists y. auto.
Qed.

Definition T_afterA (Pre Cl : axst) (s : wsub) (R : list sobj) (L : axst) : axst := ltac2:(tb__ "0|0|
S136S21S35VCl;A1A1S9bVs;VPre;VL;VCl;VR;A5A2").

Definition call_checkTA (s : wsub) : bool := ltac2:(tb__ "0|1|
S19S19S27S66Vs;P18M0A2S20G0A1A2SfaG0VNP;A2A2S19S27S66Vs;SdaA2S20SdaA1A2SfaSdaVNP;A2A2A2").

Lemma tp_of_TPA : ltac2:(tb__ "0|0|
S3bS67S1cSbS1eA1S7bS10aVNP;Vrho0;R3A3S84Vrho0;R6A2S3SaSa3R6A1ScA3Sf7R8S69S68R6R5R4A3R7A2A2F_;F_;F_;Fms;FRb;Frho;Fs;FAi;").
Proof using .
  intros Ai s rho Rb ms [Hw _] [Ht _] H. unfold call_checkTA in H. apply andb_prop in H as [H _]. apply andb_prop in H as [Ee Hn].
  apply sv_eqb_sound in Ee. apply Pos.ltb_lt in Hn. unfold tp_ok in *. rewrite rw_call', Ee. cbn [eval].
  rewrite <- (Hw 24%positive Hn). exact Ht.
Qed.

Lemma top_of_TPA : ltac2:(tb__ "0|0|
S3bS67S1cSbS1eA1S7bS10aVNP;Vrho0;R3A3S84Vrho0;R6A2S3SaSa3R6A1ScA3Sf6R8S69S68R6R5R4A3R7A2A2F_;F_;F_;Fms;FRb;Frho;Fs;FAi;").
Proof using .
  intros Ai s rho Rb ms [Hw _] [_ Ht] H. unfold call_checkTA in H. apply andb_prop in H as [_ H]. apply andb_prop in H as [Ee Hn].
  apply sv_eqb_sound in Ee. apply Pos.ltb_lt in Hn. unfold top_var. rewrite rw_call', Ee. cbn [eval].
  rewrite <- (Hw _ Hn). symmetry. exact Ht.
Qed.

Lemma T_of_chkA : ltac2:(tb__ "0|0|
S3bS67S1cS10aVNP;Vrho0;R1A3S84Vrho0;R4A2S3SaSa3R4A1ScA3SffR4S43S3dR6A1A1A2F_;F_;F_;Frho;Fs;FAi;").
Proof using .
  intros Ai s rho Hag HT H. unfold call_checkTA in H. apply andb_prop in H as [_ H]. apply andb_prop in H as [_ Hn].
  apply Pos.ltb_lt in Hn. exact (T_of_TPA NP rho0 rho Ai Hag Hn HT).
Qed.

Lemma T_ok_T0 : ltac2:(tb__ "0|0|
S1cS3bS84Vrho0;R1A2SffR3S43S3dR2A1A1A2SffR4S107Vrho0;A1A2F_;F_;FAi;Frho;").
Proof using . clear. intros rho Ai HT H. rewrite <- (TPA_top rho0 Ai HT). exact H. Qed.

Lemma R_ranges_agreeA : ltac2:(tb__ "0|2|
S34S34S67SbS1eA1M0S1cS1cSbS5fQ40A1A1SbS6dA1M1S7bS6cS3S10G0A1S97RaR9R8A3S12G0R7A2A3S63Vsegs;R7R5RbSeG1S110R4S111R3R2A2A4A5S10aS1dS35RcA1A1R8R7A3S1eS58S1eR1RbA3S3SdS0S0A2S29RaR2A2S29RbR2A2A3F_;Fo;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho';Frho;FR;Fs;FPre;FCl;").
Proof using .
  intros Cl Pre s R rho rho' tp tr ms md He Hsm Hag o Hin.
  destruct (entails_frA_sound segs Cl Pre s R rho tp tr ms md He Hsm) as (_ & _ & _ & Hwf & _).
  eapply obj_range_agree_vals; [exact Hag|]. exact (proj1 (forallb_forall _ _) Hwf o Hin).
Qed.

Lemma cont_smatchA : ltac2:(tb__ "0|3|
S34S34S34S67SbS1eA1M0S1cS1cSbS5fQ40A1A1M1G1SbS6dA1M2S7bS6cSdG2S110A2S3S10G0A1S97RdRcRaA3S12G0R9A2A3S63Vsegs;R9R7ReSeG2S110R5S111R4R3A2A4A5S10aS1dS35RfA1A1RaR9A3S63Vsegs;RaR8S9bRdRfReR10RcA5R4A5S63Vsegs;SfeRbSfdRcRbRdA3A2R9Sa2R10R11ReRdRfA5R5A5F_;F_;F_;F_;Fw;Fmd;Fms;Ftr;FtpL;Ftp;Frho';Frho;FR;Fs;FL;FPre;FCl;").
Proof using .
  intros Cl Pre L s R rho rho' tp tpL tr ms md w He Hsm Hag' Hsm'.
  unfold T_afterA. apply smatchA_add_facts.
  - apply smatchA_patch; [exact Hsm'|]. intros a Hout. unfold patchf.
    destruct (in_ranges_dec rho R a) as [Hi|Hn]; [|reflexivity]. exfalso.
    destruct Hi as (oR & HinR & Hr).
    unfold import_postA, import_post in Hout. cbn [ax_S ss_objs set_objs subst_state] in Hout.
    apply outside_all_app_iff in Hout as [_ Hout].
    pose proof (proj1 (Forall_forall _ _) Hout oR HinR) as X. cbv beta zeta in X.
    rewrite (R_ranges_agreeA Cl Pre s R rho rho' tp tr ms md He Hsm Hag' oR HinR) in X. lia.
  - apply Forall_forall. intros p Hp. apply holds_patch.
    pose proof (proj1 Hsm) as HsmS.
    apply (holds_agree_vals (ss_next (ax_S Cl)) rho rho' p Hag').
    + exact (proj1 (forallb_forall _ _) (swf_facts _ (smatch_swf segs _ _ _ HsmS)) p Hp).
    + eapply (proj1 (Forall_forall _ _) (smatch_facts segs _ _ _ HsmS)). exact Hp.
  - apply forallb_forall. intros p Hp. pose proof (proj1 Hsm) as HsmS.
    eapply sprop_below_mono; [| exact (proj1 (forallb_forall _ _) (swf_facts _ (smatch_swf segs _ _ _ HsmS)) p Hp)].
    unfold import_postA, import_post. cbn [ax_S ss_next set_objs subst_state]. unfold import_next, pos_add_nat. lia.
Qed.

Lemma sv_eqb_refl : ltac2:(tb__ "0|0|
S1bS3SaS27R1R1A2ScA3Fa;").
Proof using .
  induction a; cbn; rewrite ?Z.eqb_refl, ?Pos.eqb_refl, ?N.eqb_refl, ?IHa, ?IHa1, ?IHa2; try reflexivity;
    try (destruct (aluop_eq_dec op op); [reflexivity | congruence]); try (destruct (mulop_eq_dec op op); [reflexivity | congruence]).
  rewrite Bool.eqb_reflx. reflexivity.
Qed.

Lemma new_objs_not_pre : ltac2:(tb__ "0|0|
S2fS2fS1eS58S1eR1S10bR3R2A2A3S4S58S1eR2S2eR3A1A3S5S58S1eR2S2eR4A1A3A1A2F_;Fo;FL;FPre;").
Proof using .
  intros Pre L o H. unfold new_objs in H. apply filter_In in H as [Hin Hn]. split; [exact Hin|].
  intros HinP. apply Bool.negb_true_iff in Hn. apply (Bool.eq_true_false_abs _ _ Hn) || idtac.
  assert (X : existsb (same_frame o) (ss_objs Pre) = true).
  { apply existsb_exists. exists o. split; [exact HinP|]. unfold same_frame. rewrite !sv_eqb_refl. reflexivity. }
  rewrite X in Hn. discriminate.
Qed.

Lemma pd_elems : ltac2:(tb__ "0|5|
SbSdS0S0A2M0A1S18S18G0G0Sd6R5A1S3S10G0A1M1S59G0R6R5A3S12G0R3A2M2A3S3G1S59G0R7R5A3G2A3S5S3S18R7R6A3A1S6S4bS4cS15S0S0R6A3M3S14S0S0R6A3A2S15S0S0R5A3M4A2S4bS4cG4S14S0S0R5A3A2G3A2A2F_;F_;F_;F_;Fy;Fx;Fj;Fi;Fl;").
Proof using .
  intros l i j [b n] [b' n'] H Hi Hj Hne. cbn [fst snd].
  destruct (Nat.lt_ge_cases i j) as [Hlt|Hge].
  - exact (H i j b n b' n' Hlt Hi Hj).
  - assert (Hlt : (j < i)%nat) by lia. destruct (H j i b' n' b n Hlt Hj Hi); lia.
Qed.

Lemma pd_mid : ltac2:(tb__ "0|4|
SbSdS0S0A2M0A1M1G0G1G1G0Sd6S17G0S17G0R5SfG0R4R3A3A3R2A3A1S58G0R2S17G0R6R4A3A3S6S4bS4cS15S0S0R6A3M2S14S0S0R6A3A2S15S0S0R3A3M3A2S4bS4cG3S14S0S0R3A3A2G2A2A2F_;F_;Fy;Fl3;Fl2;Fx;Fl1;").
Proof using .
  intros l1 x l2 l3 y H Hy.
  assert (Hx : nth_error ((l1 ++ x :: l2) ++ l3) (length l1) = Some x).
  { rewrite nth_error_app1 by (rewrite length_app; cbn; lia). rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
  apply in_app_or in Hy as [Hy|Hy]; apply In_nth_error in Hy as [k Hk].
  - assert (Hkl : (k < length l1)%nat) by (apply nth_error_Some; congruence).
    assert (Hk' : nth_error ((l1 ++ x :: l2) ++ l3) k = Some y).
    { rewrite nth_error_app1 by (rewrite length_app; cbn; lia). rewrite nth_error_app1 by lia. exact Hk. }
    eapply (pd_elems _ (length l1) k); eauto. lia.
  - assert (Hkl : (k < length l2)%nat) by (apply nth_error_Some; congruence).
    assert (Hk' : nth_error ((l1 ++ x :: l2) ++ l3) (length l1 + S k) = Some y).
    { rewrite nth_error_app1 by (rewrite length_app; cbn; lia).
      rewrite nth_error_app2 by lia. replace (length l1 + S k - length l1)%nat with (S k) by lia. cbn. exact Hk. }
    eapply (pd_elems _ (length l1) (length l1 + S k)%nat); eauto. lia.
Qed.

Lemma pd_mid2 : ltac2:(tb__ "0|4|
SbSdS0S0A2M0A1M1G1G0G1G0Sd6S17G0R5S17G0R4SfG0R3R2A3A3A3A1S58G0R2S17G0R6S17G0R5R3A3A3A3S6S4bS4cS15S0S0R5A3M2S14S0S0R5A3A2S15S0S0R3A3M3A2S4bS4cG3S14S0S0R3A3A2G2A2A2F_;F_;Fy;Fl2;Fx;Fl1;Fl0;").
Proof using .
  intros l0 l1 x l2 y H Hy.
  apply (pd_mid (l0 ++ l1) x l2 [] y).
  - rewrite app_nil_r. rewrite <- app_assoc. exact H.
  - rewrite <- app_assoc. exact Hy.
Qed.

Definition xrs_okA (Ai : AA) (x : option Z) (rho : valuation) (X : list (sv * sv)) : Prop := ltac2:(tb__ "0|2|
SdS1bS1bA2M0S0S58G0R2VX;A3S4S4bS6eVrho;S15S1bS1bR3A3A2M1R2A2S4dR2S4cG1S6eVrho;S14S1bS1bR3A3A2A2A2A2S6SfbVAi;Vx;R3A3S129VXGL;R3A2A2F_;F_;Fa;Fr;").

Lemma shadow_not_in_R : ltac2:(tb__ "0|1|
S3bS10S0A1S1cSbS5fQ40M0A1A1S6cSbS1eA1S0VAInv;R7R5R4R3A4SfcR8R7R6R3A4S12aR3A1S5S6aR8R5S61G0R4A2A3A1F_;F_;F_;Fz;FR;Fmd;Ftp;Frho;Fx;FAi;").
Proof using ALA HCST.
  intros Ai x rho tp md R z HM HR Hz Hin.
  pose proof (robjs_in_ranges Ai x rho R _ HR Hin) as Hc.
  unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in Hz.
  rewrite Z_to_bv_unsigned, bv_wrap_small in Hc by (rewrite two64; lia).
  exact (cmaddrA_not_shadow Ai x z rho tp md HM Hc ltac:(unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END; lia)).
Qed.

Lemma entails_frA_base : ltac2:(tb__ "0|1|
S34S34S67SbS1eA1M0S0S3S10G0A1S97R5R4R3A3S12G0R2A2A3S3S1bS36R5A1S23R2A1A3S3S1bS36R7A1S23R3A1A3F_;F_;Fz;FR;Fs;FPre;FC;").
Proof using .
  intros C Pre s R z He Hb. rewrite entails_frA_ref_eq in He. unfold entails_frA_ref in He. destruct (entails_fr (ax_S C) (ax_S Pre) s); [|discriminate].
  match type of He with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
  apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [_ Hc]. apply sv_eqb_sound in Hc. rewrite Hb in Hc. cbn in Hc. symmetry. exact Hc.
Qed.

Lemma shadow_addr_Sh : ltac2:(tb__ "0|1|
S0S3S5fQ40M0A1S39S114R1A2S61G0S116R1A1A2A3Fa;").
Proof using . intros a. unfold shadow_addr, Sh. f_equal. lia. Qed.

Lemma xrs_client : ltac2:(tb__ "0|3|
S3bS3bS10S0A1S1cSbSdS1bS1bA2M0A1S0G0Sa6R7R5R4R3A4S0SfbR9R7R1A3SfbR9S13S0A1R2A3F_;Fa;S58G0R3R5A3S4S4bS6eR7S15S1bS1bR4A3A2M1R5A2S4dR5S4cG1S6eR7S14S1bS1bR4A3A2A2A2A2S4S6S4Sc9VCST;RbR6A3Sc9VCST;RaR6A3A2S129VXGL;R6A2A2S4Sd8VCST;VXGL;RbS116R6A1M2A4Sd8VCST;VXGL;RaG2A4A2A2F_;F_;F_;F_;Fr;Fa;FX;Frho;Fx;FA2;FAi;").
Proof using .
  intros Ai A2 x rho X a r HX Hsub Hr Ha. destruct (HX r a Hr Ha) as [Hc|Hg].
  - split; [left; split; [eapply cmaddrA_client; exact Hc | eapply cmaddrA_client; exact (Hsub _ Hc)]|].
    split; left; exists a; split; [eapply cmaddrA_client; exact Hc | reflexivity | eapply cmaddrA_client; exact (Hsub _ Hc) | reflexivity].
  - split; [right; exact Hg|]. split; right; exists a; auto.
Qed.

Lemma smatchA_X_defined : ltac2:(tb__ "0|4|
S1cSbS5fQ40M0A1A1S34SdSbS6dA1S110A2SdS1bS1bA2M1S0S63Vsegs;R6R5R4R3A5S3S1bS36R5A1S23S114A1A3S58G1R4S37R6A1A3S4S4bS60G0S25R9S15S1bS1bR5A3A2A2M2R4A2S4dR4S4cG2S60G0S25R9S14S1bS1bR5A3A2A2A2A2A2S5S3S10S5fQ8A1M3A1S1fRaS39S114R5A2A2S13G3A1A3A1F_;F_;F_;F_;Fa;Fr;Fw;FC;Ftp;Frho;").
Proof using .
  intros rho tp C w r a (_ & _ & _ & HSO & _) Hb Hr Ha. unfold shadow_ok in HSO. rewrite Hb in HSO. cbn [eval] in HSO. rewrite lit_unsigned in HSO.
  change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF in HSO.
  destruct (proj1 (Forall_forall _ _) HSO r Hr) as (_ & _ & HA). destruct (HA a Ha) as (_ & _ & _ & v & Hv & _). rewrite Hv. discriminate.
Qed.

Lemma caller_X_kept : ltac2:(tb__ "0|12|
S3bS3bS10S0A1S1cSbS5fQ40M0A1M1A1M2S6cSbS1eA1S7bS67S1cS34S34S34S0G2SdSbS6dA1S110A2S63Vsegs;RdR2R6R1A5VAInv;R11ReRdRcA4SfcR12R10RfRcA4Sa6R13R11R10S37R9A1A4S0SfbR15R13R1A3SfbR15S13S0A1R2A3F_;Fa;SdS1bS1bA2M3S0S58G3R2S37RdA1A3S4S4bS6eR15S15S1bS1bR3A3M4A2M5R2A2S4dR2S4cG5S6eR15S14S1bS1bR3A3M6A2A2A2A2S4S4bZ0M7R3A2S4dR3S4eZ2Z2fA2A2A2F_;F_;Fa;Fr;S3S1bS36RcA1S23S114A1A3ScaVCST;VXGL;R17R16S1fS69S68R14R11R10A3RfA2A1S1fReA1A6S1eS58S1eR1S10bS35ReA1S35RdA1A2A3G1S12aS60G0R1A2A1S5S4S4bS15S0S0S29R13R4A2M8A3S60G0R2A2M9A2S4dG9S14S0S0G8A3A2A2A1F_;Fw;F_;Fo';S3S0RcS60G0S25R16S36RfA1A2A2A3G3S0S58G3R2S37R12A1A3S4S4bS60G0S25R1aG4A2A2MaR2A2S4dR2S4cGaS60G0S25R1aG6A2A2A2A2A2S4S3S10S5fQ8A1MbA1McS1fR15S39R11R3A2MdA2S1fR1bGdA2A3S4S0S4S4bG7R1A2S4dR1Z8MeA2A2S5S3GcS1fR1dS38S4cR13S51R5GeA2A2R2A2A2S13GbA1MfA3A1S5S3GcS1fR18S38S4cR14S51R6GeA2A2R3A2A2GfA3A1F_;F_;Fj;S0S1eS4S4bG7R2A2S4dR2GeA2A2S58S1eR2S10bS35R16A1S35R15A1A2A3S5S4S4bS15S0S0S29R19R3A2M10A3S60G0S38S4cR15S51R7GeA2A2R4A2A2M11A2S4dG11S14S0S0G10A3A2A2A1F_;F_;Fo';Fj;A2A2F_;F_;Fa;Fr;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw0;Ftp0;Fz;FL;FPre;FC;FrhoL;Fs;Fms;FR;Fmd;Ftp;Frho;Fx;FA2;FAi;").
Proof using ALA HCST HXGL.
  intros Ai A2 x rho tp md R ms s rhoL C Pre L z tp0 w0 Hsm0 HM HR HX Hsub H47 Hb Hkept Hnew -> r a Hr Ha.
  assert (HDEF : rm rho (shadow_addr SHADOW_OFF a) <> None).
  { destruct Hsm0 as (_ & _ & _ & HSO & _). unfold shadow_ok in HSO. rewrite Hb in HSO. cbn [eval] in HSO. rewrite lit_unsigned in HSO.
    change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF in HSO.
    destruct (proj1 (Forall_forall _ _) HSO r Hr) as (_ & _ & HA). destruct (HA a Ha) as (_ & _ & _ & v & Hv & _). rewrite Hv. discriminate. }
  rewrite Hb. cbn [eval]. rewrite lit_unsigned. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF.
  destruct (xrs_client Ai A2 x rho (ax_X C) a r HX Hsub Hr Ha) as [HC HS].
  pose proof (H47 r a Hr Ha) as Ha47. pose proof (Sh_is_shadow a Ha47) as HSa.
  assert (EW : Sh a = SHADOW_OFF + a / 8) by (unfold Sh; lia).
  assert (NR : ~ in_ranges rho R (Z_to_bv 64 (Sh a))) by (eapply shadow_not_in_R; eauto).
  split; [|split; [intros j Hj | intros j o' Hj]].
  - rewrite shadow_addr_Sh. rewrite (proj1 Hkept (Sh a)); [| unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in HSa; lia |].
    + apply rm_absorb_out. exact NR.
    + right. split; [exact (proj1 HS)|]. split; [exact (proj2 HS)|]. rewrite rm_absorb_out by exact NR. rewrite <- shadow_addr_Sh. exact HDEF.
  - intros Hdef. rewrite <- EW in Hdef |- *. apply (HKW Ai A2 _ _ Hkept a j Ha47 HC Hj). rewrite rm_absorb_out; [exact Hdef|].
    rewrite <- (Z_to_bv_bv_unsigned 64 (word_byte (Sh a) j)). eapply shadow_not_in_R; eauto. apply word_byte_of_shadow; [exact HSa | exact Hj].
  - intros Ho'. apply Hnew; [exact Ho'|]. rewrite <- EW. apply word_byte_of_shadow; [exact HSa | exact Hj].
Qed.

Lemma xrs_client2 : ltac2:(tb__ "0|3|
S3bS3bS10S0A1S1cSbSdS1bS1bA2M0A1S0G0Sa6R7R5R4R3A4Sa6R7S13S0A1R5R4A4S58G0R3R5A3S4S4bS6eR7S15S1bS1bR4A3A2M1R5A2S4dR5S4cG1S6eR7S14S1bS1bR4A3A2A2A2A2S4S6S4Sc9VCST;RbR6A3Sc9VCST;RaR6A3A2S129VXGL;R6A2A2S4Sd8VCST;VXGL;RbS116R6A1M2A4Sd8VCST;VXGL;RaG2A4A2A2F_;F_;F_;F_;Fr;Fa;FX;Frho;Fx;FA2;FAi;").
Proof using .
  intros Ai A2 x rho X a r HX HX2 Hr Ha. destruct (HX r a Hr Ha) as [Hc|Hg]; destruct (HX2 r a Hr Ha) as [Hc2|Hg2].
  - split; [left; split; [eapply cmaddrA_client; exact Hc | eapply cmaddrA_client; exact Hc2]|].
    split; left; exists a; split; [eapply cmaddrA_client; exact Hc | reflexivity | eapply cmaddrA_client; exact Hc2 | reflexivity].
  - split; [right; exact Hg2|]. split; right; exists a; auto.
  - split; [right; exact Hg|]. split; right; exists a; auto.
  - split; [right; exact Hg|]. split; right; exists a; auto.
Qed.

Lemma caller_X_kept2 : ltac2:(tb__ "0|12|
S3bS3bS10S0A1S1cSbS5fQ40M0A1M1A1M2S6cSbS1eA1S7bS67S1cS34S34S34SbSdS1bS1bA2M3A1S0G2SdSbS6dA1S110A2S63Vsegs;ReR2R7R1A5G3S58G3R1R6A3S58G3R2S37RaA1A3F_;Fr;VAInv;R13R10RfReA4SfcR14R12R11ReA4Sa6R15R13R12R8A4Sa6R15S13S0A1R13R9A4G3S0S58G3R2RcA3S4S4bS6eR17S15S1bS1bR3A3M4A2M5R2A2S4dR2S4cG5S6eR17S14S1bS1bR3A3M6A2A2A2A2S4S4bZ0M7R3A2S4dR3S4eZ2Z2fA2A2A2F_;F_;Fa;Fr;S3S1bS36ReA1S23S114A1A3ScaVCST;VXGL;R19R18S1fS69S68R16R13R12A3R11A2A1S1fR10A1A6S1eS58S1eR1S10bS35R10A1S35RfA1A2A3G1S12aS60G0R1A2A1S5S4S4bS15S0S0S29R15R4A2M8A3S60G0R2A2M9A2S4dG9S14S0S0G8A3A2A2A1F_;Fw;F_;Fo';S3S0RdS60G0S25R18S36R11A1A2A2A3G3S0S58G3R2R11A3S4S4bS60G0S25R1cG4A2A2MaR2A2S4dR2S4cGaS60G0S25R1cG6A2A2A2A2A2S4S3S10S5fQ8A1MbA1McS1fR17S39R12R3A2MdA2S1fR1dGdA2A3S4S0S4S4bG7R1A2S4dR1Z8MeA2A2S5S3GcS1fR1fS38S4cR14S51R5GeA2A2R2A2A2S13GbA1MfA3A1S5S3GcS1fR1aS38S4cR15S51R6GeA2A2R3A2A2GfA3A1F_;F_;Fj;S0S1eS4S4bG7R2A2S4dR2GeA2A2S58S1eR2S10bS35R18A1S35R17A1A2A3S5S4S4bS15S0S0S29R1bR3A2M10A3S60G0S38S4cR16S51R7GeA2A2R4A2A2M11A2S4dG11S14S0S0G10A3A2A2A1F_;F_;Fo';Fj;A2A2F_;F_;Fa;Fr;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw0;Ftp0;Fz;FX;FL;FPre;FC;FrhoL;Fs;Fms;FR;Fmd;Ftp;Frho;Fx;FA2;FAi;").
Proof using ALA HCST HXGL.
  intros Ai A2 x rho tp md R ms s rhoL C Pre L X z tp0 w0 Hsm0 HXC HM HR HX HX2 H47 Hb Hkept Hnew -> r a Hr Ha.
  assert (HDEF : rm rho (shadow_addr SHADOW_OFF a) <> None).
  { destruct Hsm0 as (_ & _ & _ & HSO & _). unfold shadow_ok in HSO. rewrite Hb in HSO. cbn [eval] in HSO. rewrite lit_unsigned in HSO.
    change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF in HSO.
    destruct (proj1 (Forall_forall _ _) HSO r (HXC r Hr)) as (_ & _ & HA). destruct (HA a Ha) as (_ & _ & _ & v & Hv & _). rewrite Hv. discriminate. }
  rewrite Hb. cbn [eval]. rewrite lit_unsigned. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF.
  destruct (xrs_client2 Ai A2 x rho X a r HX HX2 Hr Ha) as [HC HS].
  pose proof (H47 r a Hr Ha) as Ha47. pose proof (Sh_is_shadow a Ha47) as HSa.
  assert (EW : Sh a = SHADOW_OFF + a / 8) by (unfold Sh; lia).
  assert (NR : ~ in_ranges rho R (Z_to_bv 64 (Sh a))) by (eapply shadow_not_in_R; eauto).
  split; [|split; [intros j Hj | intros j o' Hj]].
  - rewrite shadow_addr_Sh. rewrite (proj1 Hkept (Sh a)); [| unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in HSa; lia |].
    + apply rm_absorb_out. exact NR.
    + right. split; [exact (proj1 HS)|]. split; [exact (proj2 HS)|]. rewrite rm_absorb_out by exact NR. rewrite <- shadow_addr_Sh. exact HDEF.
  - intros Hdef. rewrite <- EW in Hdef |- *. apply (HKW Ai A2 _ _ Hkept a j Ha47 HC Hj). rewrite rm_absorb_out; [exact Hdef|].
    rewrite <- (Z_to_bv_bv_unsigned 64 (word_byte (Sh a) j)). eapply shadow_not_in_R; eauto. apply word_byte_of_shadow; [exact HSa | exact Hj].
  - intros Ho'. apply Hnew; [exact Ho'|]. rewrite <- EW. apply word_byte_of_shadow; [exact HSa | exact Hj].
Qed.

Lemma xrs_range : ltac2:(tb__ "0|2|
S3bS10S0A1S1cSbS5fQ40A1A1S6cSbSdS1bS1bA2M0A1VAInv;R6R4R3R2A4Sa6R7R6R5R2A4G0S0S58G0R2R5A3S4S4bS6eR9S15S1bS1bR3A3A2M1R2A2S4dR2S4cG1S6eR9S14S1bS1bR3A3A2A2A2A2S4S4bZ0R3A2S4dR3S4eZ2Z2fA2A2A2F_;F_;Fa;Fr;F_;F_;FX;Fmd;Ftp;Frho;Fx;FAi;").
Proof using ALA HCST HXGL.
  intros Ai x rho tp md X HM HX r a Hr Ha. destruct (HX r a Hr Ha) as [Hc|Hg].
  - exact (client_range Ai a rho tp md HM (cmaddrA_client _ _ _ Hc)).
  - apply HXGL in Hg. unfold IMG_HI, LOW_SHADOW_BEG in Hg. lia.
Qed.

Lemma client_or_xgl_noband : ltac2:(tb__ "0|0|
S3bS1cSbS5fQ40A1A1S6cS0VAInv;R5R4R3R2A4S6SfbR6S13S0A1R2A3S129VXGL;R2A2A2S6S4dR3S11aA2S4bS119R3A2A2F_;F_;Fa;Fmd;Ftp;Frho;FAi;").
Proof using ALA HCST HXGL.
  intros Ai rho tp md a HM [Hc|Hg].
  - pose proof (law_client_app _ _ _ ALA Ai rho tp md a HM (cmaddrA_client _ _ _ Hc)) as X. pose proof (topG_range (aa_geom Ai)) as TG.
    unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
  - apply HXGL in Hg. unfold IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
Qed.

Lemma band_free_of_points : ltac2:(tb__ "0|0|
S0S0S4bZ1R1A2S0S4S4bR4R1A2S4dR1S4cR4R3A2A2A2S6S4dR2S11aA2S4bS119R2A2A2F_;Fa;Sd4R4R3A2F_;F_;Flen;Flo;").
Proof using .
  clear. intros lo len Hlen H. unfold band_free.
  destruct (H lo ltac:(lia)) as [Hlo|Hhi]; [|right; exact Hhi].
  destruct (Z_le_gt_dec (lo + len) SHADOW_BAND_LO) as [Hle|Hgt]; [left; exact Hle|]. exfalso.
  destruct (H SHADOW_BAND_LO ltac:(lia)) as [X|X]; unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *; lia.
Qed.

Lemma xr_covered_point : ltac2:(tb__ "0|3|
S1cSbS22A1SbSdS1bS1bA2M0A1G0S126S22S26R4A1R3A3S3SaS3aR4R3R2A3ScA3S0S4S4bS12cR7S15S1bS1bR4A3A2M1R1A2S4dR1S4cG1S12cR7S14S1bS1bR4A3A2A2A2A2S7G0G0S4S58G0R1R7A3S4S4bS12cR9S15S1bS1bR1A3A2M2R3A2S4dR3S4cG2S12cR9S14S1bS1bR1A3A2A2A2A2A2Lr;A2F_;Fa;F_;F_;Fr';FX;Ffacts;Frho;").
Proof using .
  clear. intros rho facts X [b' l'] Hf H a Ha. cbn [fst snd] in Ha. unfold xr_covered in H. apply lazy_orb_prop in H as [H|H].
  - apply existsb_exists in H as (r & Hr & Heq). apply xr_eqb_sound in Heq. subst r. exists (b', l'). split; [exact Hr | exact Ha].
  - apply existsb_exists in H as ([b l] & Hr & Hsub). exists (b, l). split; [exact Hr|]. cbn [fst snd].
    pose proof (mk_prov_ok rho facts Hf) as Hpv.
    unfold xr_sub_pv in Hsub. cbn [fst snd] in Hsub.
    apply lazy_andb_prop in Hsub as [_ Hsub]. apply lazy_andb_prop in Hsub as [H1 Hsub]. apply lazy_andb_prop in Hsub as [Hnw Hsub].
    apply lazy_andb_prop in Hsub as [H2 _].
    pose proof (puleq_sound rho _ _ _ _ Hpv H1) as A1. pose proof (puleq_sound rho _ _ _ _ Hpv H2) as A2.
    pose proof (puleq_sound rho _ _ _ _ Hpv Hnw) as A3.
    unfold U in A1, A2, A3, Ha |- *. cbn [eval] in A1, A2, A3. rewrite !add_val in A2. rewrite add_val in A3.
    pose proof (urange (eval rho b)) as Rb. pose proof (urange (eval rho l)) as Rl.
    pose proof (urange (eval rho b')) as Rb'. pose proof (urange (eval rho l')) as Rl'.
    set (B := bv_unsigned (eval rho b)) in *. set (L := bv_unsigned (eval rho l)) in *.
    set (B' := bv_unsigned (eval rho b')) in *. set (L' := bv_unsigned (eval rho l')) in *.
    assert (Hnw' : B' + L' < 2 ^ 64).
    { destruct (Z_lt_le_dec (B' + L') (2 ^ 64)) as [Hlt|Hge]; [exact Hlt|]. exfalso.
      rewrite <- (Z.mod_add _ (-1)) in A3 by lia. rewrite Z.mod_small in A3; lia. }
    rewrite (Z.mod_small (B' + L')) in A2 by lia.
    assert (A2' : B' + L' <= B + L).
    { destruct (Z_lt_le_dec (B + L) (2 ^ 64)) as [Hlt|Hge]; [rewrite Z.mod_small in A2 by lia; lia|].
      rewrite <- (Z.mod_add _ (-1)) in A2 by lia. rewrite Z.mod_small in A2; lia. }
    lia.
Qed.

Definition robj_stackA (facts : list sprop) (o : sobj) : bool := ltac2:(tb__ "0|6|
SaSaL_;M0S108Vfacts;Vo;A2S1bSaLx;S2bVo;A1S0G0S4fZ0M1R1A2G0S53R1S4eZ2M2Z28A2A2S135Vfacts;S2aVo;A1G1S23S54S4eG2Z2fA2R1A2A1A4S11Xax2S11Xax2Lhi;S1S11Li;S10dS1bS1bS11Lb;La;M3Lop;M4G4S10eG3Lop;M5G5SaS2S1bS11La;Lw;Lsgn;S1S1bS0S11Lk;Li;Ll;X1bx8S11Xax2").

Lemma robj_stackA_sound : ltac2:(tb__ "0|1|
SbS22A1S1cS0S1eS0S126S22S26R4A1R5A3SffR5R4A2S3SaSa8R7R4A2ScA3S4S4bS15S0S0S29R7R5A2M0A3R4A2S4dR4S14S0S0G0A3A2A2S4S4bR7R5A2S4dR5S4eZ2Z2fA2A2A2F_;F_;F_;F_;Fa;Fo;FT;Frho;Ffacts;").
Proof using .
  clear. intros facts rho T o a HF HT H Hr. unfold robj_stackA in H. apply lazy_andb_prop in H as [H1 H2].
  split; [exact (robj_stack_sound facts rho T o a HF HT H1 Hr)|].
  destruct (ob_hi o) as [hi| | | | | | |] eqn:Ehi; try discriminate.
  apply lazy_andb_prop in H2 as [H3 H2]. apply lazy_andb_prop in H2 as [H4 H5]. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
  pose proof (uleq_sound rho facts _ 0 _ HF H5) as U5. unfold U in U5. rewrite U_lit in U5. unfold M64v in U5.
  rewrite Z.mod_small in U5 by lia.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite Ehi in Hr. cbn [fst snd] in Hr. rewrite (soff_lit_small rho hi) in Hr by lia. lia.
Qed.

Definition lit_in_ranges (L : list (Z * Z)) (b l : Z) : bool := ltac2:(tb__ "0|2|
S5cSdS0S0A2M0G0S19S4fS15S0S0R1A3M1Vb;A2S4fS4cVb;Vl;A2S4cG1S14S0S0R1A3A2A2A2Lcn;VL;A3").

Lemma lit_in_ranges_sound : ltac2:(tb__ "0|0|
SbSdS0S0A2A1S0S0S0S3SaSafR4R3R2A3ScA3S4S4bR4R2A2S4dR2S4cR4R3A2A2A2S129R6R3A2F_;F_;Fa;Fl;Fb;FL;").
Proof using .
  clear. intros L b l a H Ha. unfold lit_in_ranges in H. apply existsb_exists in H as ([c n] & Hin & Hc). cbn [fst snd] in Hc.
  apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. exists c, n. split; [exact Hin | lia].
Qed.

Definition robjs_checkA_ref (facts : list sprop) (tv : list (sv * sv)) (skip : option nat) (extra : sobj -> bool) (R : list sobj) : bool := ltac2:(tb__ "0|1|
S5aS1eS1eSaSaL_;M0Sa8Vfacts;R1A2ScG0S106Vtv;Vskip;R1A3ScVextra;R1A1Xax2Xax2Lo;VR;A3").
Lemma forallb_lazy_weaken_rl : forall {A} (f g : A -> bool) l, (forall a, f a = true -> g a = true) -> forallb_lazy f l = true -> forallb g l = true.
Proof using . clear. intros A f g l H Hl. rewrite forallb_lazy_eq in Hl. apply forallb_forall. intros a Ha. apply H. exact (proj1 (forallb_forall _ _) Hl a Ha). Qed.

Definition robj_stackA_p (pf : pfacts) (o : sobj) : bool := ltac2:(tb__ "0|6|
SaSaL_;M0S137Vpf;Vo;A2S1bSaLx;S2bVo;A1S0G0S4fZ0M1R1A2G0S53R1S4eZ2M2Z28A2A2S133Vpf;S2aVo;A1G1S23S54S4eG2Z2fA2R1A2A1A4S11Xax2S11Xax2Lhi;S1S11Li;S10dS1bS1bS11Lb;La;M3Lop;M4G4S10eG3Lop;M5G5SaS2S1bS11La;Lw;Lsgn;S1S1bS0S11Lk;Li;Ll;X1bx8S11Xax2").
Lemma robj_stackA_p_eq : ltac2:(tb__ "0|0|
SbS22A1S1eS3SaSacS131R2A1R1A2Sa8R2R1A2A3Fo;Ffacts;").
Proof using . clear. intros facts o. unfold robj_stackA_p, robj_stackA. rewrite XformFast.robj_stack_p_eq. reflexivity. Qed.

Definition robjs_checkA_dg (facts : list sprop) (tv : list (sv * sv)) (skip : option nat) (extra : sobj -> bool) (R : list sobj) : bool := ltac2:(tb__ "0|1|
S134Vfacts;A1S132S5aS1eS1eSaSaL_;M0S106Vtv;Vskip;R1A3ScG0Vextra;R1A1ScSacR2R1A2Xax2Xax2Lo;VR;A3Tpf;").
Lemma robjs_checkA_dg_eq : ltac2:(tb__ "0|0|
SbS22A1SbSdS1bS1bA2A1S10S18A1S1eSaF_;SbS1eA1S3SaSb1R5R4R3R2R1A5Sb2R5R4R3R2R1A5A3FR;Fextra;Fskip;Ftv;Ffacts;").
Proof using .
  clear. intros facts tv skip extra R. unfold robjs_checkA_dg, robjs_checkA_ref. cbv zeta. rewrite DigFastA.mk_pf_f_eq.
  induction R as [|o r IH]; cbn [forallb]; [reflexivity|]. rewrite IH, robj_stackA_p_eq.
  destruct (robj_stackA facts o), (robj_tracked tv skip o), (extra o); reflexivity.
Qed.
Definition robjs_checkA (facts : list sprop) (tv : list (sv * sv)) (skip : option nat) (extra : sobj -> bool) (R : list sobj) : bool := ltac2:(tb__ "0|1|
SaSaL_;M0S12fS1eS1eG0S106Vtv;Vskip;R1A3ScVextra;R1A1Xax2Lo;VR;A3ScSb1Vfacts;Vtv;Vskip;Vextra;VR;A5Xax2").
Lemma robjs_checkA_ref_eq : ltac2:(tb__ "0|0|
SbS22A1SbSdS1bS1bA2A1S10S18A1S1eSaF_;SbS1eA1S3SaSb0R5R4R3R2R1A5Sb2R5R4R3R2R1A5A3FR;Fextra;Fskip;Ftv;Ffacts;").
Proof using .
  clear. intros facts tv skip extra R. unfold robjs_checkA. rewrite <- robjs_checkA_dg_eq.
  destruct (forallb_lazy (fun o => robj_tracked tv skip o ||| extra o) R) eqn:Z; [|reflexivity].
  symmetry. rewrite robjs_checkA_dg_eq. unfold robjs_checkA_ref. revert Z. apply forallb_lazy_weaken_rl. intros o Hs.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; try reflexivity; try discriminate Hs; try exact Hs.
Qed.

Lemma blocks_bases_differA : ltac2:(tb__ "0|2|
S3bS1cSbS5fQ40A1A1S6cS0S0S0S0VAInv;R8R7R6R5A4S58SdS0S0A2M0SeS0S0R5R4A4M1S3cR9A1A3S58G0SeS0S0R4R3A4S3cRaA1A3S5S3G0SeS0S0R7R6A4G1A3A1S5S3S0R8R6A3A1F_;F_;F_;F_;Fn2;Fb2;Fn1;Fb1;Fmd;Ftp;Frho;FAi;").
Proof using ALA.
  intros Ai rho tp md b1 n1 b2 n2 HM H1 H2 Hne Heq. subst b2.
  destruct (law_blocks _ _ _ ALA Ai rho tp md HM) as (HPD & HBl & _).
  destruct (HBl _ _ H1) as (P1 & _). destruct (HBl _ _ H2) as (P2 & _).
  apply In_nth_error in H1 as [i Hi]. apply In_nth_error in H2 as [j Hj].
  assert (Hij : i <> j) by (intros ->; rewrite Hi in Hj; injection Hj; intros; apply Hne; congruence).
  assert (Hi' : nth_error (aa_live Ai ++ aa_frames Ai) i = Some (b1, n1)) by (rewrite nth_error_app1; [exact Hi | apply nth_error_Some; congruence]).
  assert (Hj' : nth_error (aa_live Ai ++ aa_frames Ai) j = Some (b1, n2)) by (rewrite nth_error_app1; [exact Hj | apply nth_error_Some; congruence]).
  pose proof (pd_elems _ i j _ _ HPD Hi' Hj' Hij) as D. cbn [fst snd] in D. lia.
Qed.

Lemma robjs_checkA_sound : ltac2:(tb__ "0|5|
S3bS1cSbS22A1SbSdS1bS1bA2M0A1S10S18A1M1S1eSaF_;SbS1eA1S10S0A1M2S1cSbS5fQ40A1A1S6cVAInv;RbR3R2R1A4S126S22S26RbA1RaA3S8bVFB;RdRcRaA4S103RdRbA2S104ReRcA2SffRfS43S3dR10A1A1A2S3SaSb0RfReRdRcRbA5ScA3S1eS0S58S1eR2ReA3S3SaR10R3A1ScA3S4S4bS15S0S0S29R15R4A2M3A3R3A2S4dR3S14S0S0G3A3A2A2SfbR17R10R4A3F_;F_;F_;Fa;Fo;G1OLskip;RfS18G2OLx;M4RdS0S7G0G0S4S3S10G0A1S59G0R13R3A3S12G0R1A2A3S4S102R15R1A2S3S0S15S0S0S100R15R1A2A3R2A3A2A2Lt;A2Lxb;S9X10x2Li;G4RcS0S9Lz;S8X10x2X10x2SfcR14RdR13ReA4F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;Fx;FR;Fextra;Fskip;Ftv;Ffacts;Frho;FAi;").
Proof using ALA.
  intros Ai rho facts tv skip extra R x rho1 tp1 md1 HM HF HN HD HZ HT Hchk Hextra Hx o a Ho Hr.
  rewrite robjs_checkA_ref_eq in Hchk. unfold robjs_checkA_ref in Hchk. pose proof (proj1 (forallb_forall _ _) Hchk o Ho) as Hc. cbn beta in Hc.
  apply lazy_orb_prop in Hc as [Hc|Hc]; [left; exact (robj_stackA_sound facts rho _ o a HF HT Hc Hr)|].
  apply lazy_orb_prop in Hc as [Hc|Hc]; [|exact (Hextra o a Ho Hc Hr)].
  destruct (robj_tracked_sound tv skip o Hc) as (j & t & Hj & Hsk & Hb & Hl & Hh).
  destruct (tracked_range rho o t a Hb Hl Hh Hr) as [Ha Hpos].
  pose proof (nth_error_In _ _ Hj) as Hin.
  assert (Hnz : tnz rho t).
  { intros Hz0. pose proof (proj1 (Forall_forall _ _) HZ t Hin (fun H => H Hz0)). lia. }
  destruct (proj1 (Forall_forall _ _) HN t Hin Hnz) as (Tpos & Tin & Tfb).
  right; right; left. exists (fst (tvv rho t)), (snd (tvv rho t)). rewrite <- surjective_pairing.
  split; [exact Tin|]. split; [|exact Ha].
  destruct skip as [i|], x as [xb|]; try contradiction; [|discriminate].
  destruct Hx as (ti & Hi & Hzi & Hxb). intros Ex. injection Ex as Ex. subst xb.
  assert (Hij : i <> j) by (intros ->; apply Hsk; reflexivity).
  destruct (proj1 (Forall_forall _ _) HN ti (nth_error_In _ _ Hi) Hzi) as (Tpos' & Tin' & _).
  pose proof (tvd_nth rho tv i j ti t HD Hi Hj Hij Hzi Hnz) as Hne.
  rewrite (surjective_pairing (tvv rho ti)) in Tin', Hne. rewrite (surjective_pairing (tvv rho t)) in Tin, Hne.
  eapply (blocks_bases_differA Ai rho1 tp1 md1 _ _ _ _ HM Tin' Tin Hne). exact Ex.
Qed.

Definition xr_lit_in (L : list (Z * Z)) (r : sv * sv) : bool := ltac2:(tb__ "0|c|
S1bSaLx;M0S15S1bS1bVr;A3S0G0S14S1bS1bVr;A3S0SaSaL_;M1S4fZ0M2R2A2G1S4fG2R1A2G1S53S4cR2R1A2S4eZ2Z3eA2A2SafVL;R2R1A3S11Xax2S11Xax2S11Xax2Ll;S1S11Li;M3S10dS1bS1bS11Lb0;La;M4Lop;M5G5S10eG4Lop;M6G6SaS2S1bS11La;Lw;Lsgn;M7S1S1bS0S11Lk;Li;Ll;M8X1bx8Lb;G3S10dS1bS1bS11Lb;La;M9Lop;MaGaS10eG9Lop;MbGbG7G8X1bx8").

Lemma xr_lit_in_sound : ltac2:(tb__ "0|1|
SbSdS0S0A2A1S1cSdS1bS1bA2S0S3SaSabR4R2A2ScA3S4S4bS6eR4S15S1bS1bR3A3A2M0R2A2S4dR2S4cG0S6eR4S14S1bS1bR3A3A2A2A2A2S129R6R3A2F_;F_;Fa;Fr;Frho;FL;").
Proof using .
  clear. intros L rho [b l] a H Ha. unfold xr_lit_in in H. cbn [fst snd] in H, Ha.
  destruct b as [b| | | | | | |]; try discriminate. destruct l as [l| | | | | | |]; try discriminate.
  apply lazy_andb_prop in H as [H0 H]. apply lazy_andb_prop in H as [H1 H]. apply lazy_andb_prop in H as [H2 H3].
  apply Z.leb_le in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  unfold uval in Ha. rewrite !U_lit in Ha. unfold M64v in Ha. rewrite !Z.mod_small in Ha by lia.
  eapply lit_in_ranges_sound; eauto.
Qed.

Definition xr_tracked (tv : list (sv * sv)) (skip : option nat) (r : sv * sv) : bool := ltac2:(tb__ "0|0|
S106Vtv;Vskip;S33S15S1bS1bVr;A3S23Z0A1S14S1bS1bVr;A3S16S32A1S30A5A3").

Definition xr_in_stack_obj_ref (facts : list sprop) (r : sv * sv) (o : sobj) : bool := ltac2:(tb__ "0|f|
SaSaL_;M0Sa8Vfacts;Vo;A2S1bSaLx;M1S14S1bS1bVr;A3S0G1S2dVo;A1S0G1S2bVo;A1S0G0S4fZ0M2R3A2G0G0S27S15S1bS1bVr;A3M3S2aVo;A1M4A2G0S4fR2G2A2S4fR3R1A2S11Xax2S11Xax2ScG1G3S0S11Lz;S1S11Li;M5S10dS1bS1bS10dSaLop;R3S1bSaLb0;R1S0G0S27R3G4A2G0S4fR6R1A2S4fS4cR1R7A2R5A2S11Xax2S11Xax2Lk;G5S10dS1bS1bS11Lb1;La;M6Lop0;M7G7S10eG6Lop0;M8G8SaS2S1bS11La;Lw;Lsgn;M9S1S1bS0S11Lk;Li;MaLl0;MbX1bx8S11S11S11S11S11S11S11S11S11X10dxaLb0;Lb;Lop;S10dS1bS1bS11Lb;La;McLop;MdS10eGcLop;MeGeG9GbX1bx8Xax2S11Xax2Lhi;G5GdGdGeGeG9GbX1bx8Llo;G5GdGdGeGeG9GbX1bx8Ll;G5GdGdGeGeG9S1GaLl;X1bx8S11Xax2").

Lemma xr_in_stack_obj_ref_sound : ltac2:(tb__ "0|1|
SbS22A1S1cS0SdS1bS1bA2S1eS0S126S22S26R5A1R6A3SffR6R5A2S3SaSb4R8R5R4A3ScA3S4S4bS6eR8S15S1bS1bR6A3A2M0R4A2S4dR4S4cG0S6eR8S14S1bS1bR6A3A2A2A2A2S4S4bR8R5A2S4dR5S4eZ2Z2fA2A2A2F_;F_;F_;F_;Fa;Fo;Fr;FT;Frho;Ffacts;").
Proof using .
  clear. intros facts rho T [b l] o a HF HT H Ha. unfold xr_in_stack_obj_ref in H. cbn [fst snd] in H, Ha.
  apply lazy_andb_prop in H as [HS H].
  destruct l as [l| | | | | | |]; try discriminate.
  destruct (ob_lo o) as [lo| | | | | | |] eqn:Elo; try discriminate.
  destruct (ob_hi o) as [hi| | | | | | |] eqn:Ehi; try discriminate.
  apply lazy_andb_prop in H as [H0 H]. apply Z.leb_le in H0.
  pose proof HS as HS0. unfold robj_stackA in HS0. apply lazy_andb_prop in HS0 as [HS1 HS2]. rewrite Ehi in HS2.
  apply lazy_andb_prop in HS2 as [Hh0 HS2]. apply lazy_andb_prop in HS2 as [Hh1 _]. apply Z.leb_le in Hh0. apply Z.ltb_lt in Hh1.
  unfold robj_stack in HS1. rewrite Elo, Ehi in HS1.
  apply lazy_andb_prop in HS1 as [Hl0 HS1]. apply lazy_andb_prop in HS1 as [Hl1 _]. apply Z.leb_le in Hl0. apply Z.leb_le in Hl1.
  unfold uval in Ha. rewrite U_lit in Ha. unfold M64v in Ha.

  assert (RNG : forall x, bv_unsigned (eval rho (ob_base o)) + lo <= x < bv_unsigned (eval rho (ob_base o)) + hi -> T <= x < 2 ^ 47).
  { intros x Hx. apply (robj_stackA_sound facts rho T o x HF HT HS). unfold obj_range, obj_lo_of, obj_hi_of. rewrite Elo, Ehi. cbn [fst snd].
    rewrite !soff_lit_small by lia. exact Hx. }
  pose proof (bv_urange (eval rho (ob_base o))) as Rb.
  apply lazy_orb_prop in H as [H|H].
  - apply lazy_andb_prop in H as [Hb H]. apply lazy_andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    apply sv_eqb_sound in Hb. subst b. rewrite (Z.mod_small l) in Ha by lia. apply RNG. lia.
  - destruct b as [| |op b1 b2| | | | |]; try discriminate. destruct op; try discriminate. destruct b2 as [k| | | | | | |]; try discriminate.
    apply lazy_andb_prop in H as [Hb H]. apply lazy_andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    apply sv_eqb_sound in Hb. subst b1. rewrite (Z.mod_small l) in Ha by lia. rewrite U_add, U_lit in Ha. unfold M64v in Ha.
    destruct (Z.eq_dec l 0) as [->|Hl]; [lia|].
    pose proof (RNG (bv_unsigned (eval rho (ob_base o)) + lo) ltac:(lia)) as R0.
    pose proof (RNG (bv_unsigned (eval rho (ob_base o)) + hi - 1) ltac:(lia)) as R1. destruct HT as [_ TR].
    assert (E0 : (bv_unsigned (eval rho (ob_base o)) + k mod 18446744073709551616) mod 18446744073709551616 = bv_unsigned (eval rho (ob_base o)) + k).
    { rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia. }
    rewrite E0 in Ha. apply RNG. lia.
Qed.

Definition xr_in_stack_obj (facts : list sprop) (r : sv * sv) (o : sobj) : bool := ltac2:(tb__ "0|f|
SaSaL_;M0S1bSaLx;M1S14S1bS1bVr;A3S0G1S2dVo;A1S0G1S2bVo;A1S0G0S4fZ0M2R3A2G0G0S27S15S1bS1bVr;A3M3S2aVo;A1M4A2G0S4fR2G2A2S4fR3R1A2S11Xax2S11Xax2ScG1G3S0S11Lz;S1S11Li;M5S10dS1bS1bS10dSaLop;R3S1bSaLb0;R1S0G0S27R3G4A2G0S4fR6R1A2S4fS4cR1R7A2R5A2S11Xax2S11Xax2Lk;G5S10dS1bS1bS11Lb1;La;M6Lop0;M7G7S10eG6Lop0;M8G8SaS2S1bS11La;Lw;Lsgn;M9S1S1bS0S11Lk;Li;MaLl0;MbX1bx8S11S11S11S11S11S11S11S11S11X10dxaLb0;Lb;Lop;S10dS1bS1bS11Lb;La;McLop;MdS10eGcLop;MeGeG9GbX1bx8Xax2S11Xax2Lhi;G5GdGdGeGeG9GbX1bx8Llo;G5GdGdGeGeG9GbX1bx8Ll;G5GdGdGeGeG9S1GaLl;X1bx8Sa8Vfacts;Vo;A2S11Xax2").
Lemma xr_in_stack_obj_ref_eq : ltac2:(tb__ "0|0|
SbS22A1SdS1bS1bA2S1eS3SaSaaR3R2R1A3Sb4R3R2R1A3A3Fo;Fr;Ffacts;").
Proof using .
  intros facts r o. unfold xr_in_stack_obj, xr_in_stack_obj_ref.
  destruct (robj_stackA facts o); match goal with |- (if ?c then _ else _) = _ => destruct c end; reflexivity.
Qed.
Lemma xr_in_stack_obj_sound : ltac2:(tb__ "0|1|
SbS22A1S1cS0SdS1bS1bA2S1eS0S126S22S26R5A1R6A3SffR6R5A2S3SaSaaR8R5R4A3ScA3S4S4bS6eR8S15S1bS1bR6A3A2M0R4A2S4dR4S4cG0S6eR8S14S1bS1bR6A3A2A2A2A2S4S4bR8R5A2S4dR5S4eZ2Z2fA2A2A2F_;F_;F_;F_;Fa;Fo;Fr;FT;Frho;Ffacts;").
Proof using .
  intros facts rho T r o a HF HT H. rewrite xr_in_stack_obj_ref_eq in H. exact (xr_in_stack_obj_ref_sound facts rho T r o a HF HT H).
Qed.

Definition xrs_checkA_ref (facts : list sprop) (tv : list (sv * sv)) (skip : option nat) (objs : list sobj)
           (extra : sv * sv -> bool) (X : list (sv * sv)) : bool := ltac2:(tb__ "0|2|
S5aSdS1bS1bA2M0G0SaSaL_;M1SabVXGL;R1A2ScG1SadVtv;Vskip;R1A3ScG1S5cS1eSaaVfacts;R1A2Vobjs;A3ScVextra;R1A1Xax2Xax2Xax2Lr;VX;A3").

Definition xr_in_stack_obj_p (pf : pfacts) (r : sv * sv) (o : sobj) : bool := ltac2:(tb__ "0|f|
SaSaL_;M0S1bSaLx;M1S14S1bS1bVr;A3S0G1S2dVo;A1S0G1S2bVo;A1S0G0S4fZ0M2R3A2G0G0S27S15S1bS1bVr;A3M3S2aVo;A1M4A2G0S4fR2G2A2S4fR3R1A2S11Xax2S11Xax2ScG1G3S0S11Lz;S1S11Li;M5S10dS1bS1bS10dSaLop;R3S1bSaLb0;R1S0G0S27R3G4A2G0S4fR6R1A2S4fS4cR1R7A2R5A2S11Xax2S11Xax2Lk;G5S10dS1bS1bS11Lb1;La;M6Lop0;M7G7S10eG6Lop0;M8G8SaS2S1bS11La;Lw;Lsgn;M9S1S1bS0S11Lk;Li;MaLl0;MbX1bx8S11S11S11S11S11S11S11S11S11X10dxaLb0;Lb;Lop;S10dS1bS1bS11Lb;La;McLop;MdS10eGcLop;MeGeG9GbX1bx8Xax2S11Xax2Lhi;G5GdGdGeGeG9GbX1bx8Llo;G5GdGdGeGeG9GbX1bx8Ll;G5GdGdGeGeG9S1GaLl;X1bx8SacVpf;Vo;A2S11Xax2").
Lemma xr_in_stack_obj_p_eq : ltac2:(tb__ "0|0|
SbS22A1SdS1bS1bA2S1eS3SaSb3S131R3A1R2R1A3SaaR3R2R1A3A3Fo;Fr;Ffacts;").
Proof using . clear. intros facts r o. unfold xr_in_stack_obj_p, xr_in_stack_obj. rewrite robj_stackA_p_eq. reflexivity. Qed.

Definition xrs_checkA_dg (facts : list sprop) (tv : list (sv * sv)) (skip : option nat) (objs : list sobj)
           (extra : sv * sv -> bool) (X : list (sv * sv)) : bool := ltac2:(tb__ "0|2|
S134Vfacts;A1S132S5aSdS1bS1bA2M0G0SaSaL_;M1SabVXGL;R1A2ScG1SadVtv;Vskip;R1A3ScG1Vextra;R1A1ScS130S1eSb3R2R1A2Vobjs;A3Xax2Xax2Xax2Lr;VX;A3Tpf;").
Lemma xrs_checkA_dg_eq : ltac2:(tb__ "0|2|
SbS22A1SbSdS1bS1bA2M0A1M1S10S18A1SbS1eA1G0SaF_;G1S3SaSb6R6R5R4R3R2R1A6Sb7R6R5R4R3R2R1A6A3FX;Fextra;Fobjs;Fskip;Ftv;Ffacts;").
Proof using .
  clear. intros facts tv skip objs extra X. unfold xrs_checkA_dg, xrs_checkA_ref. cbv zeta. rewrite DigFastA.mk_pf_f_eq.
  induction X as [|r t IH]; cbn [forallb]; [reflexivity|]. rewrite IH, existsb_lazy_eq.
  rewrite (EntailFast.existsb_ext_in (xr_in_stack_obj_p (mk_pf facts) r) (xr_in_stack_obj facts r) objs (fun o _ => xr_in_stack_obj_p_eq facts r o)).
  destruct (xr_lit_in XGL r), (xr_tracked tv skip r), (existsb (xr_in_stack_obj facts r) objs), (extra r); reflexivity.
Qed.
Definition xrs_checkA (facts : list sprop) (tv : list (sv * sv)) (skip : option nat) (objs : list sobj)
           (extra : sv * sv -> bool) (X : list (sv * sv)) : bool := ltac2:(tb__ "0|2|
SaSaL_;M0S12fSdS1bS1bA2M1G1G0SabVXGL;R1A2ScG0SadVtv;Vskip;R1A3ScVextra;R1A1Xax2Xax2Lr;VX;A3ScSb6Vfacts;Vtv;Vskip;Vobjs;Vextra;VX;A6Xax2").
Lemma xrs_checkA_ref_eq : ltac2:(tb__ "0|2|
SbS22A1SbSdS1bS1bA2M0A1M1S10S18A1SbS1eA1G0SaF_;G1S3SaSb5R6R5R4R3R2R1A6Sb7R6R5R4R3R2R1A6A3FX;Fextra;Fobjs;Fskip;Ftv;Ffacts;").
Proof using .
  clear. intros facts tv skip objs extra X. unfold xrs_checkA. rewrite <- xrs_checkA_dg_eq.
  destruct (forallb_lazy (fun r => xr_lit_in XGL r ||| (xr_tracked tv skip r ||| extra r)) X) eqn:Z; [|reflexivity].
  symmetry. rewrite xrs_checkA_dg_eq. unfold xrs_checkA_ref. revert Z. apply forallb_lazy_weaken_rl. intros r Hs.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; try reflexivity; try discriminate Hs; try exact Hs.
Qed.

Lemma xrs_checkA_sound : ltac2:(tb__ "0|6|
S3bS1cSbS22A1SbSdS1bS1bA2M0A1M1S10S18A1M2SbS1eA1G0SaF_;G1S10S0A1M3S1cSbS5fQ40A1A1S6cVAInv;RcR3R2R1A4S126S22S26RcA1RbA3S8bVFB;ReRdRbA4S103ReRcA2S104RfRdA2SffR10S43S3dR11A1A1A2S3SaSb5R10RfReRdRcRbA6ScA3G0S0S58G0R2ReA3S3SaR10R3A1ScA3S4S4bS6eR16S15S1bS1bR4A3A2M4R3A2S4dR3S4cG4S6eR16S14S1bS1bR4A3A2A2A2A2S6SfbR18R10R4A3S129VXGL;R4A2A2F_;F_;F_;Fa;Fr;G2OLskip;R10S18G3OLx;M5RdS0S7G0G0S4S3S10G0A1S59G0R14R3A3S12G0R1A2A3S4S102R16R1A2S3S0S15S0S0S100R16R1A2A3R2A3A2A2Lt;A2Lxb;S9X10x2Li;G5RcS0S9Lz;S8X10x2X10x2Sa6R15RdR14ReA4F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd1;Ftp1;Frho1;Fx;FX;Fextra;Fobjs;Fskip;Ftv;Ffacts;Frho;FAi;").
Proof using ALA.
  intros Ai rho facts tv skip objs extra X x rho1 tp1 md1 HM HF HN HD HZ HT Hchk Hextra Hx r a Hr Ha.
  rewrite xrs_checkA_ref_eq in Hchk. unfold xrs_checkA_ref in Hchk. pose proof (proj1 (forallb_forall _ _) Hchk r Hr) as Hc. cbn beta in Hc.
  apply lazy_orb_prop in Hc as [Hc|Hc]; [right; eapply xr_lit_in_sound; eauto|].
  apply lazy_orb_prop in Hc as [Hc|Hc].
  - left. unfold xr_tracked in Hc.
    destruct (robj_tracked_sound tv skip _ Hc) as (j & t & Hj & Hsk & Hb & _ & Hh). cbn [ob_base ob_hi] in Hb, Hh.
    pose proof (nth_error_In _ _ Hj) as Hin.
    assert (Er : tvv rho t = (uval rho (fst r), uval rho (snd r))) by (unfold tvv, uval; rewrite Hb, Hh; reflexivity).
    destruct (Z.eq_dec (uval rho (fst r)) 0) as [Hz0|Hnz0].
    { exfalso. pose proof (proj1 (Forall_forall _ _) HZ t Hin) as Z0. cbv beta in Z0. rewrite Er in Z0. cbn [snd] in Z0.
      unfold tnz in Z0. rewrite <- Hb in Z0. unfold uval in *. specialize (Z0 ltac:(lia)). lia. }
    assert (Hnz : tnz rho t) by (unfold tnz; rewrite <- Hb; unfold uval in Hnz0; exact Hnz0).
    destruct (proj1 (Forall_forall _ _) HN t Hin Hnz) as (Tpos & Tin & Tfb). rewrite Er in Tpos, Tin, Tfb. cbn [snd] in Tpos.
    right; right; left. exists (uval rho (fst r)), (uval rho (snd r)). split; [exact Tin|]. split; [|exact Ha].
    destruct skip as [i|], x as [xb|]; try contradiction; [|discriminate].
    destruct Hx as (ti & Hi & Hzi & Hxb). intros Ex. injection Ex as Ex. subst xb.
    assert (Hij : i <> j) by (intros ->; apply Hsk; reflexivity).
    destruct (proj1 (Forall_forall _ _) HN ti (nth_error_In _ _ Hi) Hzi) as (Tpos' & Tin' & _).
    pose proof (tvd_nth rho tv i j ti t HD Hi Hj Hij Hzi Hnz) as Hne. rewrite Er in Hne.
    rewrite (surjective_pairing (tvv rho ti)) in Tin', Hne.
    eapply (blocks_bases_differA Ai rho1 tp1 md1 _ _ _ _ HM Tin' Tin Hne). exact Ex.
  - apply lazy_orb_prop in Hc as [Hc|Hc]; [|exact (Hextra r a Hr Hc Ha)].
    apply existsb_exists in Hc as (o & Ho & Hc). left. left. eapply xr_in_stack_obj_sound; eauto.
Qed.

Lemma band_free_site : ltac2:(tb__ "0|3|
S3bS34S34S67SbS1eA1M0S1cSbS5fQ40A1A1SbS6dA1M1S7bS6cSdS1bS1bA2M2S63Vsegs;R6R5RaSeG1S110R4S111R3R2A2A4A5VAInv;RcR7R6R3A4Sa6RdS13S0A1R8S37RcA1A4S3S10G0A1S97RdRcRbA3S12G0RaA2A3S58G2R5S37RdA1A3S4bZ1S12cRbS6bRdS14S1bS1bR6A3A2A2A2Sd4S12cRcS6bReS15S1bS1bR7A3A2A2S12cRcS6bReS14S1bS1bR7A3A2A2A2F_;F_;F_;F_;F_;F_;Fr;Fmd;Fms;Ftr;Ftp;Frho;FR;Fs;FPre;FCl;FAi;").
Proof using ALA HCST HXGL.
  intros Ai Cl Pre s R rho tp tr ms md r Hsm HM HX He Hr Hlen.
  assert (HXcov : forallb (fun r0 => xr_covered (ss_facts (ax_S Cl)) (ax_X Cl) (xr_subst s r0)) (ax_X Pre) = true).
  { clear - He. rewrite entails_frA_ref_eq in He. unfold entails_frA_ref in He. destruct (entails_fr (ax_S Cl) (ax_S Pre) s); [|discriminate].
    match type of He with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    apply andb_prop in Hc as [Hc Hwf]. apply andb_prop in Hc as [Hc _]. exact Hc. }
  pose proof (proj1 (forallb_forall _ _) HXcov r Hr) as Hcov. pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  apply band_free_of_points; [exact Hlen|]. intros a Ha.
  destruct (xr_covered_point rho (ss_facts (ax_S Cl)) (ax_X Cl) (xr_subst s r) HF Hcov a ltac:(destruct r; cbn [xr_subst fst snd] in *; exact Ha)) as (rr & Hrr & Harr).
  apply (client_or_xgl_noband Ai rho tp md a HM). exact (HX rr a Hrr ltac:(unfold uval, U in *; exact Harr)).
Qed.

Lemma live_nodup : ltac2:(tb__ "0|0|
S3bS1cSbS5fQ40A1A1S6cVAInv;R4R3R2R1A4S5bSdS0S0A2S3cR5A1A2F_;Fmd;Ftp;Frho;FA;").
Proof using ALA.
  intros A rho tp md HM. destruct (law_blocks _ _ _ ALA A rho tp md HM) as (HPD & HBl & _).
  apply (proj2 (List.NoDup_nth_error _)). intros i j Hi Eij.
  destruct (nth_error (aa_live A) i) as [[b n]|] eqn:Ei; [|apply nth_error_None in Ei; lia].
  symmetry in Eij.
  destruct (Nat.eq_dec i j) as [->|Hne]; [reflexivity|]. exfalso.
  destruct (HBl b n (nth_error_In _ _ Ei)) as (G1 & _).
  assert (Hx : nth_error (aa_live A ++ aa_frames A) i = Some (b, n)) by (rewrite nth_error_app1 by lia; exact Ei).
  assert (Hy : nth_error (aa_live A ++ aa_frames A) j = Some (b, n)).
  { rewrite nth_error_app1; [exact Eij|]. apply nth_error_Some. rewrite Eij. discriminate. }
  pose proof (pd_elems _ _ _ _ _ HPD Hx Hy Hne) as D. cbn [fst snd] in D. lia.
Qed.

Lemma JAi_large_live_le : ltac2:(tb__ "0|0|
S80S3bS0S1cSbS5fQ40A1A1SbS6dA1S6cVJAi;R7R6R5R4R3R2R1A7S4bS46R7A1S4cS4cS52S1aSdS0S0A2VFB;A2A1S52S1aSdS1bS1bA2S7cR8A1A2A1A2S51R6S71A2A2A2F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;").
Proof using ALA.
  intros nd Ai kc rho tp tr md HJ.
  destruct HJ as (_ & _ & HM & _ & _ & _ & _ & _ & _ & _ & HXA & _).
  unfold XA in HXA. destruct (XAz_blocks _ _ _ _ _ _ HXA) as (bl & Hlen & Hbl). destruct HXA as [_ HCEN].
  assert (Hkc : kc / KU = Z.of_nat (length bl)) by (rewrite <- Hlen, Z.mul_comm; apply Z.div_mul; unfold KU; lia).
  rewrite Hkc. unfold large_live.
  assert (INC : incl (List.filter is_large (aa_live Ai)) (FB ++ tvals rho (nd_tv nd) ++ bl)).
  { intros bn Hbn. apply filter_In in Hbn as [Hl Hg]. unfold is_large in Hg. apply Z.leb_le in Hg.
    apply in_or_app. destruct (in_dec ZZ_eq_dec bn FB) as [Hf|Hf]; [left; exact Hf|]. right.
    apply in_or_app. destruct (in_dec ZZ_eq_dec bn (tvals rho (nd_tv nd))) as [Ht|Ht]; [left; exact Ht|]. right.
    apply Hbl. apply (HCEN bn Hl); [unfold LARGE_MIN; exact Hg | exact Hf |].
    intros v Hv _ ->. exact (Ht Hv). }
  pose proof (List.NoDup_incl_length (List.NoDup_filter is_large (live_nodup Ai rho tp md HM)) INC) as HL.
  rewrite !length_app in HL. unfold tvals in HL. rewrite length_map in HL. lia.
Qed.
Lemma JAi_large_live_le0 : ltac2:(tb__ "0|1|
SbSdS1bS1bA2M0A1SbSdSdS1bS0A2S1bA2A1SbS6fA1S3bS0S1cSbS5fQ40A1A1SbS6dA1S6cVJAi;S7eR9R8R7S93A4R6R5R4R3R2R1A7S4bS46R7A1S4cS52S1aSdS0S0A2VFB;A2A1S52S1aG0RaA2A1A2A2F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fbd;Ffr;Ftv;").
Proof using ALA.
  intros tv fr bd Ai kc rho tp tr md HJ. pose proof (JAi_large_live_le _ _ _ _ _ _ _ HJ) as H. cbn [nd_tv] in H.
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [HXA _] & _). cbn in HXA. subst kc. rewrite Z.div_0_l in H by (unfold KU; lia). lia.
Qed.

Lemma JAi_small_live_le : ltac2:(tb__ "0|0|
S80S3bS0S1cSbS5fQ40A1A1SbS6dA1S6cVJAi;R7R6R5R4R3R2R1A7S4bS4aR7A1S4cS79VBX;A1S52S1aSdS1bS1bA2S7cR8A1A2A1A2A2F_;Fmd;Ftr;Ftp;Frho;Fkc;FAi;Fnd;").
Proof using .
  intros nd Ai kc rho tp tr md HJ. pose proof (JAi_proj_capN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H. unfold capN in H.
  pose proof (cntS_bounds rho (nd_tv nd)). lia.
Qed.

Lemma eval_rwl : ltac2:(tb__ "0|1|
S1cS1cS3S1S5fQ40A1M0F_;S24R1A1S24R2A1A3S3S1SbS5fQ8A1A1F_;S2cR2A1S2cR3A1A3S1bS3G0S25R4R1A2S25R5R1A2A3Fe;F_;F_;Frho';Frho;").
Proof using .
  clear. intros [w l m] [w' l' m'] E1 E2 e. cbn [rw rl] in E1, E2. subst w' l'.
  induction e; cbn; try rewrite ?IHe1, ?IHe2, ?IHe; reflexivity.
Qed.
Lemma JAi_errno_havoc : ltac2:(tb__ "0|3|
S1S80S3bS0S1cS1cSbS5fQ40M0A1M1A1SbS6dA1S6cS3SaS82R9R8A2ScA3S0Sd5R1A1S129VCST;R2A2F_;Fa;S3S1G1F_;S24R6A1S24R7A1A3S3S1SbS5fQ8A1M2A1F_;S2cR7A1S2cR8A1A3G1S5Sd5S60G0R1A2A1A1S3S10G2A1S1fRaR2A2S1fRbR2A2A3F_;Fa;VJAi;RdRcRbRaR8R7R6A7VJAi;ReRdRcRaR9R8R7A7F_;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho';Frho;Fkc;FAi;Fnd;Fn;").
Proof using ALA HCST.
  intros n nd Ai kc rho rho' tp tr md Hnb HEC Erw Erl Hrm HJ.
  destruct (nd_below_split n nd Hnb) as (Hbt & Hbf & Hbb & Hba).
  destruct HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK & HP0 & HXA & HBU & HPA & HCK & HCN).
  assert (Hag : agree_vals n rho rho') by (split; [intros i _; rewrite Erw; reflexivity | intros l; rewrite Erl; reflexivity]).
  assert (EDEC : forall z, errno_addrA z \/ ~ errno_addrA z) by (intros z; unfold errno_addrA; lia).
  destruct (law_blocks' Ai rho tp md HM) as (_ & HBl & HFr). pose proof (topG_range (aa_geom Ai)) as TG.

  assert (ELO : forall z, errno_addrA z -> z < IMG_HI) by (intros z Hz; unfold errno_addrA, ERRNO_A, IMG_HI in *; lia).
  assert (ZB : forall z, 0 <= z < 2 ^ 64 -> IMG_HI <= z -> rm rho' (Z_to_bv 64 z) = rm rho (Z_to_bv 64 z)).
  { intros z Hz Hge. apply Hrm. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64 in *; lia). intros He. pose proof (ELO z He). lia. }
  assert (SHB : forall x, 0 <= x -> IMG_HI <= Sh x) by (intros x Hx; unfold Sh, SHADOW_OFF, IMG_HI; pose proof (Z.div_pos x 8 Hx ltac:(lia)); lia).
  assert (WB : forall a j, 0 <= a < 2 ^ 64 -> IMG_HI <= a -> 0 <= j < 8 -> rm rho' (word_byte a j) = rm rho (word_byte a j)).
  { intros a j Ha Hge Hj. unfold word_byte. apply ZB.
    - pose proof (Z.mul_div_le a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)). pose proof (Z.div_mod a 8 ltac:(lia)).
      assert (a / 8 * 8 <= 2 ^ 64 - 8). { assert (a / 8 <= (2 ^ 64 - 1) / 8) by (apply Z.div_le_mono; lia). change ((2 ^ 64 - 1) / 8) with 2305843009213693951 in *. lia. }
      lia.
    - assert (IMG_HI / 8 <= a / 8) by (apply Z.div_le_mono; lia). unfold IMG_HI in *. change (6565888 / 8) with 820736 in *. lia. }
  split; [destruct Hav as [H1 H2]; split; [intros i Hi; rewrite Erw; exact (H1 i Hi) | intros l; rewrite Erl; exact (H2 l)]|].
  split; [exact Hk|]. split.
  {
    eapply (law_frame _ _ _ ALA); [exact HM| |].
    - intros a Hnm _. apply Hrm. intros He. apply Hnm. right; right; right. exact (HEC _ He).
    - intros a (f & sz & Hin & Hr) Hdef. rewrite Hrm; [exact Hdef|]. intros He. pose proof (ELO _ He).
      destruct (HFr f sz Hin) as (_ & _ & _ & ((G4 & _) & _) & _). pose proof (SHB f ltac:(unfold IMG_HI in *; lia)). lia. }
  split; [exact HT|]. split; [exact HB|]. split; [exact HFF|].
  split; [split; [eapply tvinA_agree; eauto | split; [eapply tvd_agree; eauto | eapply tvz_agree; eauto]]|].
  split; [eapply frinA_agree; eauto|].
  split.
  {
    destruct HK as [K1 K2]. split.
    - intros a Ha Hp. rewrite <- (K1 a Ha Hp). apply Hrm. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64 in *; lia). intros He. pose proof (ELO a He) as Hlo.
      destruct Hp as [[Hs|[[_ Hne]|[(b & sz & Hin & Hr)|(f & sz & fl & Hin & Hr)]]]|[(x & Hx & _ & ->) _]].
      + rewrite <- (TPA_top _ _ HT) in Hs. unfold IMG_HI in *. lia.
      + exact (Hne He).
      + destruct (HBl b sz (HB _ Hin)) as (_ & _ & _ & _ & ((G5 & _) & _)). lia.
      + destruct (HFF f sz fl Hin) as [Hfr ->]. destruct (HFr f sz Hfr) as (_ & _ & _ & ((G4 & _) & _) & _ & ((G6 & _) & _) & _). lia.
      + pose proof (SHB x Hx). lia.
    - intros a j Ha Hp Hj Hdef. destruct Hp as (x & Hx & Hpx & ->). rewrite (WB (Sh x) j Ha (SHB x Hx) Hj). exact (K2 (Sh x) j Ha (ex_intro _ x (conj Hx (conj Hpx eq_refl))) Hj Hdef). }
  split; [exact HP0|].
  assert (HLV : forall b sz z, In (b, sz) (aa_live Ai) -> b <= z < b + sz -> 0 <= z < 2 ^ 47 /\ IMG_HI <= z).
  { intros b sz z Hin Hz. destruct (HBl b sz Hin) as (_ & _ & G3 & G4 & ((G5 & _) & _)). lia. }
  destruct (XA_frame FB (nd_am nd) Ai Ai rho rho' (nd_tv nd) (nd_tv nd) kc HXA) as [HXA' EP].
  - intros b sz H1 _ H3. split; [exact H1|]. unfold untracked in *. rewrite (tvals_agree n rho rho' _ Hag Hbt). exact H3.
  - intros b sz z H1 _ Hz. destruct (HLV b sz z H1 Hz) as [Z1 Z2]. apply ZB; [lia | exact Z2].
  - intros b sz a H1 _ Ha. destruct (HLV b sz a H1 Ha) as [Z1 Z2].
    assert (S0 : 0 <= Sh a < 2 ^ 64) by (pose proof (Sh_is_shadow a Z1) as SS; unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in SS; lia).
    replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia). split.
    + intros _. unfold shadow_addr. replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia). apply ZB; [exact S0 | apply SHB; lia].
    + intros j Hj Hdef. rewrite (WB (Sh a) j S0 (SHB a ltac:(lia)) Hj). exact Hdef.
  - intros e _. apply eval_rwl; assumption.
  - intros bn H1 _ _ H4. split; [exact H1|]. unfold untracked in *. rewrite <- (tvals_agree n rho rho' _ Hag Hbt). exact H4.
  - split; [exact HXA'|]. split; [|split; [exact HPA|split; [exact HCK | exact (capN_agree n BX Ai rho rho' _ Hag Hbt HCN)]]]. rewrite EP. eapply BUD_agree; eauto.
Qed.

Section CallT.
Variable TR : assn -> assn -> Prop.
Hypothesis TR_facts : ltac2:(tb__ "0|1|
S64S34S1cSbS5fQ40A1A1S9eS126S22S26R3A1S21S35R4A1A1A3VTR;S62Vsegs;R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Hypothesis TR_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TR (SPA segs (J x) S rho tp) Q) -> TR (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Hypothesis TR_pre : ltac2:(tb__ "0|0|
S9eS9eS9eSa1R3R1A1R5R2A1F_;Fw;VTR;R4R2A2VTR;R4R3A2F_;F_;FQ;FP';FP;").
Hypothesis TR_callP : ltac2:(tb__ "0|5|
S64S64S34S34S67SbS1eA1M0SbSdS34S96A2M1A1SbSdS1bS1bA2M2A1S9eS1cSbS5fQ40A1A1M3G2S58G2R1R5A3S58G2R2S37RbA1A3F_;Fr;S3S10G0A1S97RaR9R8A3S12G0R7A2A3S3SaS98RbRaR9R8S127G1S34S15S34S96A2R7A4A5ScA3S1cG3VTR;S62Vsegs;RfRdR2R1A5S9aVsegs;S1dS35RdA1A1R2R1RaA5A2Ftp1;Frho1;SbS6dA1M4S7bS6cS63Vsegs;R9R8R10SeG4S110R3S111R2R1A2A4A5R13RaR9R4R2A4R13S69S68RbRfS112R3RaR4A3A3R10A2RaR5R3A4F_;F_;Fmd;Fms;Ftr;S34S96G4S7bS6cS1cG3G4S7bS6cS58G1SeS34S96RaR9A4R14A3S63Vsegs;R12R11R19SeG4S110R9S111R8R7A2A4A5R1cR13R12RaR8A4S10aS1dS35R1aA1A1S69S68R14R18S112R9R13RaA3A3R19A2R8A3S63Vsegs;R9R8ReSeG4S110R7S111R6R5A2A4A5ReS69S68R16R1aS112RbR15RcA3A3R1bA2R15RaR9R8R6A6S4S138R17S112RcR16RdA3R1bR1cR1dR10R1eR19RbA9S1cS10cR18S112RdR17ReA3R1cR1dS35R1eA1S35R1fA1S35R11A1R1RcA9VTR;S62Vsegs;S9dR11S69S68R19R1dS112ReR18RfA3A3R1eA2R18RdRcA5S139R1eR1fR12R20R1dR1bA6R2RcA5R1aA2F_;Frho';A2F_;F_;F_;F_;F_;F_;Fmd';Fms';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;FJL;FL;VTR;S62Vsegs;R11RfR8R7A5R9A2F_;F_;F_;F_;F_;F_;Ftp;Frho;FQ;FXk;FPosts;FR;Fs;FPre;FC;FJp;FJ;").

Ltac clear_TR := try clear TR_callP; try clear TR_pre; try clear TR_ex; try clear TR_facts.

Definition site_okA (Cl : axst) (s : wsub) (R : list sobj) (rho : valuation) (nd : ndesc) (x : option Z)
           (extra : AA -> machine_state -> Prop) : Prop := ltac2:(tb__ "0|2|
S3bS7bS126S22S26Vrho;A1S21S35VCl;A1A1A3VP0f;Vrho0;A1S10aVNP;Vrho0;Vrho;A3S89VFB;R5A2S8aVFF;R6A2S8bVFB;R7Vrho;S7cVnd;A1M0A4S103Vrho;G0A2S104Vrho;G0A2S8fVFF;RaVrho;S7dVnd;A1A4S7S1cS1cS7SbS5fQ40A1A1M1G1S7S6cS6cVAInv;ReR3R2R1A4Lmd1;A2Ltp1;A2Lrho1;A2S84Vrho0;RcA2SffVrho;S43S3dRdA1A1A2S4SfcReVx;Vrho;VR;A4S4Sa6ReVx;Vrho;S37VCl;A1A4Vextra;ReRdA2A2A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fms;FAi;").

Definition preA (rho : valuation) : Prop := ltac2:(tb__ "0|0|
S4VP0f;Vrho0;A1S10aVNP;Vrho0;Vrho;A3A2").
Definition payA (facts : list sprop) (costV : sv) (costK : Z) (bfrom bto : list bitem) : Prop := ltac2:(tb__ "0|0|
S7aS125Vfacts;VcostV;VcostK;Vbfrom;Vbto;A6").
Lemma payA_of_bud_pay : ltac2:(tb__ "0|1|
SbS22A1S1bS0SbS6fA1M0G0S3SaS78R5R4R3R2R1A5ScA3S11bR6R5R4R3R2A5F_;Fbto;Fbfrom;FcostK;FcostV;Ffacts;").
Proof using . intros. apply bud_pay_okF. assumption. Qed.

Lemma In_remove_nth_ne {T} : ltac2:(tb__ "0|0|
SbVT;A1S18VT;VT;S3S10VT;A1S59VT;R4R3A3S12VT;R2A2A3S58VT;R2R5A3S5S3VT;R3R4A3A1S58VT;R4S101VT;R6R7A3A3F_;F_;F_;Fx;Ft;Fi;Fl;").
Proof using . clear. induction l as [|h r IH]; intros [|i] t x Hn Hin Hne; cbn in *; try discriminate; try contradiction.
  - injection Hn as ->. destruct Hin as [<-|H]; [contradiction | exact H].
  - destruct Hin as [<-|H]; [left; reflexivity | right; exact (IH i t x Hn H Hne)].
Qed.
Lemma cen_remove : ltac2:(tb__ "0|4|
S3bS3bS1cS1cS1SbSdS1bS1bA2M0A1S18G0SbSdS0S0A2M1A1M2G2S0S0G2S10aR9RbRaA3S3SaS105RaR9A2ScA3S3S10G0A1S59G0RaR9A3S12G0R8A2A3S3G1S100ReR9A2SeS0S0R6R5A4A3S4bZ1R6A2S3G2S3cR12A1M3S17G1RaSfG1SeS0S0R8R7A4R9A3A3A3S3G2G3S17G1RbRaA3A3Sd6S17G1S17G1RcSfG1SeS0S0RaR9A4RbA3A3R8A3A1G1S58G1R1S3cR15A1A3S4bS72S14S0S0R2A3A2S5S58G1R3VFB;A3A1S83R16S101G0R13R14A3R4A3S4S58G1R5S3cR1aA1A3S83R18R15R5A3A2F_;F_;F_;F_;Fbn;F_;F_;F_;F_;F_;F_;F_;F_;Ffr;Fn;Fp;Fk2;Fk1;Ft;Fi;Ftv;Fnx;FrhoP;Frho;FA2;FAi;").
Proof using .
  clear. intros Ai A2 rho rhoP nx tv i t k1 k2 p n fr Hag Hbt Hnth Ht Hn E1 E2 HPD bn Hcl _ _ Hut.
  rewrite E2 in Hcl. split; [rewrite E1; apply in_app_or in Hcl as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]|].
  assert (Hne : bn <> (p, n)).
  { intros ->. pose proof (pd_mid k1 (p, n) k2 fr (p, n) HPD Hcl) as D. cbn [fst snd] in D. lia. }
  apply (proj2 (untracked_tv _ _ _)). intros t' Ht' Hnz' Heq.
  assert (Hb : (sv_below nx (fst t') && sv_below nx (snd t')) = true) by exact (proj1 (forallb_forall _ _) Hbt t' Ht').
  assert (Hnt : t' <> t) by (intros ->; apply Hne; rewrite <- Heq; exact Ht).
  apply (proj1 (untracked_tv _ _ _) Hut t' (In_remove_nth_ne tv i t t' Hnth Ht' Hnt)).
  - apply (proj2 (tnz_agree nx rho rhoP t' Hag Hb)). exact Hnz'.
  - rewrite (tvv_agree nx rho rhoP t' Hag Hb). exact Heq.
Qed.

Lemma live2_kept : ltac2:(tb__ "0|b|
S3bS3bS10S0A1S1cS1cS1cS7bS67SbS1eA1SbS5fQ40M0A1M1A1S6cS0S0VAInv;RdRaR4R3A4SfcReRcRbR6A4ScaVCST;VXGL;RfReS1fS69S68RcR7R9A3R8A2A1S1fRaA1A6G1S3S10S5fQ8A1M2A1M3S1fRdR1A2S1fRcR1A2A3Fa;S58SdS0S0A2M4SeS0S0R6R5A4S3cR11A1M5A3S58G4SeS0S0R7R6A4G5A3S4S0S4S4bR9R1A2S4dR1S4cR9R8A2A2A2M6S3G3S1fSfeR11SfdR12R11RdA3A2S61G0R2A2M7A2S1fR12G7A2A3F_;Fz;S0G6S4S5S3G3S1fR12S39S114R2A2A2S13G2A1M8A3A1S3G3S1fSfeR12SfdR13R12ReA3A2S39S114R3A2M9A2S1fR13G9A2A3F_;S0S4S4bZ0R1A2S4dR1Z8MaA2A2S5S3G3S1fR14S38S4cS114S51R4GaA2A2R2A2A2G8A3A1S5S3G3S1fSfeR14SfdR15R14R10A3A2S38S4cS114S51R5GaA2A2R3A2A2G8A3A1F_;F_;Fj;A2F_;Fa;A2F_;F_;F_;F_;F_;F_;Fn;Fb;Fmd;Ftp;FR;Fs;Fms;FrhoL;Frho';Frho;Fx;FA2;FAi;").
Proof using ALA HCST.
  intros Ai A2 x rho rho' rhoL ms s R tp md b n HM HR Hkept Hrm Hin1 Hin2.
  destruct (law_blocks _ _ _ ALA Ai rho tp md HM) as (_ & HBl & _). destruct (HBl b n Hin1) as (G1 & _ & G3 & G4 & G5). top_rng G4.
  assert (CL : forall z, b <= z < b + n -> client_addrA CST Ai z /\ client_addrA CST A2 z).
  { intros z Hz. split; left; right; left; exists b, n; auto. }
  assert (NE : forall z, b <= z < b + n -> ~ errno_addrA z).
  { intros z Hz He. unfold errno_addrA, ERRNO_A, IMG_HI in *. lia. }
  split.
  - intros z Hz. cbn [rho_patch rm]. unfold patchf. destruct (in_ranges_dec rho R (Z_to_bv 64 z)) as [Hi|Hn]; [reflexivity|].
    rewrite Hrm. rewrite (proj1 Hkept z ltac:(lia) (or_introl (conj (proj1 (CL z Hz)) (conj (proj2 (CL z Hz)) (NE z Hz))))). apply rm_absorb_out. exact Hn.
  - intros a Ha. assert (Ha47 : 0 <= a < 2 ^ 47) by lia. pose proof (Sh_is_shadow a Ha47) as HSa.
    assert (EW : Sh a = SHADOW_OFF + a / 8) by (unfold Sh; lia).
    assert (CS : client_shadowA CST XGL Ai (Sh a) /\ client_shadowA CST XGL A2 (Sh a)).
    { destruct (CL a Ha) as [C1 C2]. split; left; exists a; auto. }
    split.
    + intros HDEF. rewrite shadow_addr_Sh in HDEF |- *. cbn [rho_patch rm]. unfold patchf.
      destruct (in_ranges_dec rho R (Z_to_bv 64 (Sh a))) as [Hi|Hn]; [exfalso; exact (shadow_not_in_R Ai x rho tp md R _ HM HR HSa Hi)|].
      rewrite Hrm. rewrite (proj1 Hkept (Sh a)); [| unfold is_shadowZ, SHADOW_OFF, HIGH_SHADOW_END in HSa; lia |].
      * apply rm_absorb_out. exact Hn.
      * right. split; [exact (proj1 CS)|]. split; [exact (proj2 CS)|]. rewrite rm_absorb_out by exact Hn. exact HDEF.
    + intros j Hj Hdef. rewrite <- EW in Hdef |- *. cbn [rho_patch rm]. unfold patchf.
      assert (NW : ~ in_ranges rho R (word_byte (Sh a) j)).
      { rewrite <- (Z_to_bv_bv_unsigned 64 (word_byte (Sh a) j)). eapply shadow_not_in_R; eauto. apply word_byte_of_shadow; [exact HSa | exact Hj]. }
      destruct (in_ranges_dec rho R (word_byte (Sh a) j)) as [Hi|Hn]; [exfalso; exact (NW Hi)|].
      rewrite Hrm. apply (HKW Ai A2 _ _ Hkept a j Ha47 (or_introl (CL a Ha)) Hj). rewrite rm_absorb_out; [exact Hdef | exact Hn].
Qed.

Lemma cont_JAi_PA : ltac2:(tb__ "0|a|
S3bOF_;S34S34S34S67SbS1eA1M0S1cSbS5fQ40A1A1M1SbS6dA1M2S7bS6cS1cG1G2S6cS1cS80S3bS0S3bS10S0A1SbSdS1bS1bA2A1SbS6fA1S1bS0S3S10G0A1S97R18R17R15A3S12G0R14A2A3S63Vsegs;R14R13R19SeG2S110R12S111R11R10A2A4A5Sf9VNP;S1dS35R1aA1A1A2S3SaS82S1dS35R1bA1A1RcA2ScA3S3SaS70S1dS35R1cA1A1R7A2ScA3VJAi;ReRdRcR18R17R16R14A7SfcReRbR19R1aA4S10cR1aS112R16R19R17A3R1bR1cS35R1eA1S35R1fA1S35R1dA1R11R15A9VAInv;ReR16R15R13A4VKc;R15R14A2S0SfbR13R10R1A3SfbR12S13S0A1R2A3F_;Fa;SdS0S0A2M3S58G3R1VFB;A3S58G3R2S3cR13A1A3F_;Fb;S3SbG3A1S3fR12A1S3fR14A1A3S3S44S3dR13A1S3dR15A1A3ScaVCST;VXGL;R16R14S1fS69S68R21R22S112R1dR20R1eA3A3R23A2A1S1fR1cA1A6S11bS21S35R27A1A1R11R10S81R18A1R12A5S4bZ0M4S3eR16A1A2S4bG4S41R17A1A2S4bG4S40R18A1A2S4bS3eR19A1S4cS3eR1bA1S6eR26R15A2A2A2S4bS50S71S4cS41R1aA1S40R1aA1A2A2S4cS50S71S4cS41R1cA1S40R1cA1A2A2R15A2A2SfeR1fSfdR28R1fR29A3A2S1cS4S8bVFB;R1cR1R1aA4S4S103R1R1aA2S104R1R1aA2A2A2TrhoP;S0S0S58G3SeS0S0R2R1A4M5S3cR20A1M6A3S5S58G3SeS0S0R3R2A4VFB;A3A1M7S83R2dS7cR23A1SeS0S0R4R3A4M8A3S58G3SeS0S0R5R4A4M9S3cR21A1A3F_;F_;F_;Fn;Fb;SfeR21SfdR2aR21R2bA3A2S1cS0S0S58G3G5S3cR22A1A3G7S83R2fS7cR25A1G8A3S83R6R21G9A3F_;F_;F_;Fn;Fb;TrhoP;SfeR22SfdR2bR22R2cA3A2S1cG3S58G3R1G6A3S4bS72S14S0S0R2A3A2S5S58G3R3VFB;A3A1S83R5R21R4A3S4S58G3R5S3cR26A1A3S83R31S7cR27A1R5A3A2F_;F_;F_;F_;Fbn;TrhoP;R32R1fA1S85VBX;R20A2S86VBX;R21SfeR25SfdR2eR25R2fA3A2R1fA4S90VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;R35S7eR20S7dR25A1R1fS7fR25A1A4R22R23SfeR26SfdR2fR26R30A3A2R29R28R27A12F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FdK;FdV;Fbd';Ftv';Fx;FA2;Fkc;FAi;Fnd;Frho';Fmd';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;Ftp;Frho;FR;Fs;FL;FPre;FCl;FPAx;").
Proof using ALA HCST HXGL.
  intros PAx Cl Pre L s R rho tp tr ms md rhoL tpL tr' md' rho' nd Ai kc A2 x tv' bd' dV dK He Hsm Hnf Hnb Hbb HJ HRok Hlink HM2 Hk2 Hsub HFB2 HFR2 HG2 Hkept2
         HP HV0 HKm0 HKf0 HV HK HTV HL2 HU2 HC2 HPA2 HCK2 HCN2.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  assert (Hag' : agree_vals (ss_next (ax_S Cl)) rho rho') by (destruct Hlink as (A & _); exact A).
  assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
  { eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]. }
  destruct (nd_below_split _ nd Hnb) as (Hbt & Hbf & Hbb0 & Hba).
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  assert (Hrm' : forall a, rm rho' a = rm rhoL a) by (intros a; eapply call_linkP_rm; exact Hlink).
  destruct (XA_frame FB (nd_am nd) Ai A2 rho (rho_patch rho' (patchf rho rho' R)) (nd_tv nd) tv' kc HXA) as [HXA' EPOT].
  { intros b n H1 H2 H3. split; [exact (HL2 b n H1 H2 H3) | exact (HU2 b n H1 H2 H3)]. }
  { intros b n z H1 H2 Hz. exact (proj1 (live2_kept Ai A2 x rho rho' rhoL (vms md tp ms) s R tp md b n HM HRok Hkept2 Hrm' H1 H2) z Hz). }
  { intros b n a H1 H2 Ha. exact (proj2 (live2_kept Ai A2 x rho rho' rhoL (vms md tp ms) s R tp md b n HM HRok Hkept2 Hrm' H1 H2) a Ha). }
  { intros e Hin. eapply am_svs_agree; [exact HagP | exact Hba | exact Hin]. }
  { exact HC2. }
  split; [|split; [exact Hk2|split; [|split; [|split; [|split; [|split; [exact HTV|split; [|split; [|split; [exact HP0|split; [exact HXA'|split; [|split; [exact HPA2 | split; [exact HCK2 | exact HCN2]]]]]]]]]]]]]].
  - eapply agree_vals_trans; [exact Hav|]. eapply agree_vals_le; [exact Hnf | exact HagP].
  - eapply (AInv_patch A2 Ai x); [exact HM2 | exact Hrm' | exact HRok | exact Hsub].
  - exact (TPA_kept rho0 Ai A2 HG2 HT).
  - exact HFB2.
  - intros f sz fl Hin. rewrite HFR2, HG2. exact (HFF f sz fl Hin).
  - eapply frinA_agree; [exact HagP | exact Hbf |]. destruct HFR as [HFR HCEN]. split.
    + unfold frinA0 in HFR |- *. apply Forall_forall. intros y Hy.
      pose proof (proj1 (Forall_forall _ _) HFR y Hy) as (Y1 & Y2 & Y3). rewrite HFR2, HG2. auto.
    + eapply frinA_rest_map; [exact HFR2 | reflexivity | exact HCEN].
  - eapply (keptFA_step Ai A2 x rho rhoL (vms md tp ms) s R tp md tpL md' rho' HM HM2 HB HFF HFB2); [| exact HT | exact HG2 | exact HRok | exact HK0 | exact Hkept2 | exact Hrm'].
    intros f sz fl Hin. rewrite HFR2, HG2. exact (HFF f sz fl Hin).
  - cbn [nd_am nd_bd]. rewrite EPOT. eapply BUD_agree; [exact HagP | exact Hbb |].
    eapply (BUD_payF preA (ss_facts (ax_S Cl)) dV dK (nd_bd nd) bd' _ (aa_V Ai) (aa_Km Ai) (aa_Kf Ai)); eauto. all: try (split; assumption).
Qed.

Lemma cont_JAi : ltac2:(tb__ "0|a|
S34S34S34S67SbS1eA1M0S1cSbS5fQ40A1A1M1SbS6dA1M2S7bS6cS1cG1G2S6cS1cS80S3bS0S3bS10S0A1SbSdS1bS1bA2A1SbS6fA1S1bS0S3S10G0A1S97R18R17R15A3S12G0R14A2A3S63Vsegs;R14R13R19SeG2S110R12S111R11R10A2A4A5Sf9VNP;S1dS35R1aA1A1A2S3SaS82S1dS35R1bA1A1RcA2ScA3S3SaS70S1dS35R1cA1A1R7A2ScA3VJAi;ReRdRcR18R17R16R14A7SfcReRbR19R1aA4S10cR1aS112R16R19R17A3R1bR1cS35R1eA1S35R1fA1S35R1dA1R11R15A9VAInv;ReR16R15R13A4VKc;R15R14A2S0SfbR13R10R1A3SfbR12S13S0A1R2A3F_;Fa;SdS0S0A2M3S58G3R1VFB;A3S58G3R2S3cR13A1A3F_;Fb;S3SbG3A1S3fR12A1S3fR14A1A3S3S44S3dR13A1S3dR15A1A3ScaVCST;VXGL;R16R14S1fS69S68R21R22S112R1dR20R1eA3A3R23A2A1S1fR1cA1A6S11bS21S35R27A1A1R11R10S81R18A1R12A5S4bZ0M4S3eR16A1A2S4bG4S41R17A1A2S4bG4S40R18A1A2S4bS3eR19A1S4cS3eR1bA1S6eR26R15A2A2A2S4bS50S71S4cS41R1aA1S40R1aA1A2A2S4cS50S71S4cS41R1cA1S40R1cA1A2A2R15A2A2SfeR1fSfdR28R1fR29A3A2S1cS4S8bVFB;R1cR1R1aA4S4S103R1R1aA2S104R1R1aA2A2A2TrhoP;S0S0S58G3SeS0S0R2R1A4M5S3cR20A1M6A3S5S58G3SeS0S0R3R2A4VFB;A3A1M7S83R2dS7cR23A1SeS0S0R4R3A4M8A3S58G3SeS0S0R5R4A4M9S3cR21A1A3F_;F_;F_;Fn;Fb;SfeR21SfdR2aR21R2bA3A2S1cS0S0S58G3G5S3cR22A1A3G7S83R2fS7cR25A1G8A3S83R6R21G9A3F_;F_;F_;Fn;Fb;TrhoP;SfeR22SfdR2bR22R2cA3A2S1cG3S58G3R1G6A3S4bS72S14S0S0R2A3A2S5S58G3R3VFB;A3A1S83R5R21R4A3S4S58G3R5S3cR26A1A3S83R31S7cR27A1R5A3A2F_;F_;F_;F_;Fbn;TrhoP;VPA;R1fA1S85VBX;R20A2S86VBX;R21SfeR25SfdR2eR25R2fA3A2R1fA4VJAi;S7eR20S7dR25A1R1fS7fR25A1A4R22R23SfeR26SfdR2fR26R30A3A2R29R28R27A7F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FdK;FdV;Fbd';Ftv';Fx;FA2;Fkc;FAi;Fnd;Frho';Fmd';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;Ftp;Frho;FR;Fs;FL;FPre;FCl;").
Proof using ALA HCST HXGL. exact (cont_JAi_PA PA). Qed.

Definition is_cls (c : Z) (x : Z * Z) : bool := ltac2:(tb__ "0|0|
S56S14S0S0Vx;A3S117Vc;A1A2").
Definition ccount (c : Z) (l : list (Z * Z)) : nat := ltac2:(tb__ "0|1|
S1aSdS0S0A2M0S5dG0S124Vc;A1Vl;A3A2").
Definition ffpairs : list (Z * Z) := ltac2:(tb__ "0|2|
S127SdSdS0S0A2M0S0A2M1G0G1S15G0S0R1A3Ly;VFF;A4").

Lemma ccount_app : ltac2:(tb__ "0|2|
S0SbSdS0S0A2M0A1M1G1S3S18S11cR3S17G0R2R1A3A2S12dS11cR3R2A2S11cR3R1A2A2A3Fl2;Fl1;Fc;").
Proof using . clear. intros. unfold ccount. rewrite List.filter_app, length_app. reflexivity. Qed.

Lemma ccount_map_cls : ltac2:(tb__ "0|2|
S0S0SbSdS0S0A2M0A1S4bZ0R3A2M1G1S3S18S11cR5S127G0G0G0SeS0S0S14S0S0R1A3S117R5A1A4Lpf;R3A4A2SaS18L_;S56R5R4A2S1aG0R3A2U0Xax2A3F_;F_;Fb;Fc0;Fc;").
Proof using .
  clear. intros c c0 b Hc Hc0. unfold ccount. induction b as [|x r IH]; cbn; [destruct (c =? c0); reflexivity|].
  unfold is_cls at 1. cbn [snd].
  destruct (Z.eqb_spec c c0) as [->|Hne].
  - rewrite Z.eqb_refl. cbn. rewrite IH. reflexivity.
  - destruct (Z.eqb_spec (fs_frame_size c0) (fs_frame_size c)) as [E|_]; [exfalso; apply Hne; symmetry; exact (fs_frame_size_inj _ _ Hc0 Hc E)|].
    exact IH.
Qed.

Lemma ccount_frames_of : ltac2:(tb__ "0|3|
SbSbSdS0S0A2M0A1M1A1S0S0S4bZ0R2A2M2G2S3S18S11cR3S49R4R5A2A2SaS18L_;S53R3R4A2U0S1aG0S128G1S57S54R3R4A2A1R5S16G0A1A4A2Xax2A3F_;F_;Fc;Fc0;FB;").
Proof using .
  clear. induction B as [|b B IH]; intros c0 c Hc0 Hc; cbn [frames_of].
  - cbn. destruct (c <? c0); [reflexivity|]. destruct (Z.to_nat (c - c0)); reflexivity.
  - rewrite ccount_app, ccount_map_cls by lia. rewrite (IH (c0 + 1) c) by lia.
    destruct (Z.eqb_spec c c0) as [->|Hne].
    + rewrite Z.sub_diag. replace (c0 <? c0) with false by (symmetry; apply Z.ltb_irrefl).
      replace (c0 <? c0 + 1) with true by (symmetry; apply Z.ltb_lt; lia). rewrite Z2Nat.inj_0. cbn [nth]. lia.
    + destruct (Z.ltb_spec c c0) as [Hlt|Hge].
      * replace (c <? c0 + 1) with true by (symmetry; apply Z.ltb_lt; lia). lia.
      * replace (c <? c0 + 1) with false by (symmetry; apply Z.ltb_ge; lia).
        replace (Z.to_nat (c - c0)) with (S (Z.to_nat (c - (c0 + 1)))) by lia. cbn [nth]. lia.
Qed.

Lemma n_frames_ccount : ltac2:(tb__ "0|0|
S3bS0S4bZ0R1A2S3S18Se9R3R2A2S11cR2S3fR3A1A2A3F_;Fc;FA;").
Proof using .
  clear. intros A c Hc. unfold n_frames, aa_frames. rewrite ccount_frames_of by lia.
  replace (c <? 0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Z.sub_0_r. reflexivity.
Qed.

Lemma frames_nodup : ltac2:(tb__ "0|0|
S3bS1cSbS5fQ40A1A1S6cVAInv;R4R3R2R1A4S5bSdS0S0A2S3fR5A1A2F_;Fmd;Ftp;Frho;FA;").
Proof using ALA.
  intros A rho tp md HM. destruct (law_blocks _ _ _ ALA A rho tp md HM) as (HPD & _ & HFr).
  apply (proj2 (List.NoDup_nth_error _)). intros i j Hi Eij.
  destruct (nth_error (aa_frames A) i) as [[f sz]|] eqn:Ei; [|apply nth_error_None in Ei; lia].
  symmetry in Eij.
  destruct (Nat.eq_dec i j) as [->|Hne]; [reflexivity|]. exfalso.
  destruct (HFr f sz (nth_error_In _ _ Ei)) as (_ & _ & G64 & _).
  assert (Hx : nth_error (aa_live A ++ aa_frames A) (length (aa_live A) + i) = Some (f, sz)).
  { rewrite nth_error_app2 by lia. replace (length (aa_live A) + i - length (aa_live A))%nat with i by lia. exact Ei. }
  assert (Hy : nth_error (aa_live A ++ aa_frames A) (length (aa_live A) + j) = Some (f, sz)).
  { rewrite nth_error_app2 by lia. replace (length (aa_live A) + j - length (aa_live A))%nat with j by lia. exact Eij. }
  pose proof (pd_elems _ _ _ _ _ HPD Hx Hy ltac:(lia)) as D. cbn [fst snd] in D. lia.
Qed.

Lemma ccount_incl : ltac2:(tb__ "0|2|
S0SbSdS0S0A2M0A1M1G1S5bG0R2A2S5eG0R3R2A3S12eS11cR5R4A2S11cR5R3A2A2F_;F_;Fm;Fl;Fc;").
Proof using .
  clear. intros c l m Hnd Hincl. unfold ccount. apply List.NoDup_incl_length.
  - apply List.NoDup_filter. exact Hnd.
  - intros x Hx. apply List.filter_In in Hx as [Hx Hc]. apply List.filter_In. split; [exact (Hincl x Hx) | exact Hc].
Qed.

Lemma n_frames_bound : ltac2:(tb__ "0|1|
S3bS1cSbS5fQ40A1A1S6cSbSdSdS1bS0A2S1bA2M0A1S0S4bZ0R1A2VAInv;R7R6R5R4A4S8fVFF;R8R7R4A4S12eSe9R9R4A2S12dS11cR4S123A2S11cR4S127G0SdS0S0A2S8cR8A1R5A4A2A2A2F_;F_;F_;Fc;Ffr;Fmd;Ftp;Frho;FAi;").
Proof using ALA.
  intros Ai rho tp md fr c Hc HM (_ & HC & _). rewrite n_frames_ccount by exact Hc. rewrite <- ccount_app.
  apply ccount_incl; [exact (frames_nodup Ai rho tp md HM)|].
  intros x Hx. apply in_or_app. destruct (HC x Hx) as [(fl & Hin)|Hin]; [left | right; exact Hin].
  unfold ffpairs. apply in_map_iff. exists (fst x, snd x, fl). split; [destruct x; reflexivity | exact Hin].
Qed.

Lemma cont_JAi_fr : ltac2:(tb__ "0|b|
S34S34S34S67SbS1eA1M0S1cSbS5fQ40A1A1M1SbS6dA1M2S7bS6cS1cG1G2S6cS1cS80S3bS0S3bS10S0A1SbSdS1bS1bA2A1SbSdSdS1bS0A2S1bA2A1SbS6fA1S1bS0S3S10G0A1S97R19R18R16A3S12G0R15A2A3S63Vsegs;R15R14R1aSeG2S110R13S111R12R11A2A4A5Sf9VNP;S1dS35R1bA1A1A2S3SaS82S1dS35R1cA1A1RdA2ScA3S3SaS70S1dS35R1dA1A1R7A2ScA3VJAi;RfReRdR19R18R17R15A7SfcRfRcR1aR1bA4S10cR1bS112R17R1aR18A3R1cR1dS35R1fA1S35R20A1S35R1eA1R12R16A9VAInv;RfR17R16R14A4VKc;R16R15A2SfcR11S13S0A1R1eR1fA4SdS0S0A2M3S58G3R1VFB;A3S58G3R2S3cR14A1A3F_;Fb;S0S0S0S58SdG3S0A2SeG3S0SeS0S0R3R2A4M4R1A4VFF;A3S58G3SeS0S0R4R3A4M5S3fR17A1A3F_;Ffl;Fsz;Ff;S3S44S3dR14A1S3dR16A1A3ScaVCST;VXGL;R17R15S1fS69S68R22R23S112R1eR21R1fA3A3R24A2A1S1fR1dA1A6S11bS21S35R28A1A1R11R10S81R19A1R12A5S4bZ0M6S3eR17A1A2S4bG6S41R18A1A2S4bG6S40R19A1A2S4bS3eR1aA1S4cS3eR1cA1S6eR27R15A2A2A2S4bS50S71S4cS41R1bA1S40R1bA1A2A2S4cS50S71S4cS41R1dA1S40R1dA1A2A2R15A2A2SfeR20SfdR29R20R2aA3A2S1cS4S8bVFB;R1dR1R1bA4S4S103R1R1bA2S104R1R1bA2A2A2TrhoP;S8fVFF;R1dSfeR21SfdR2aR21R2bA3A2R1aA4S0S0S58G3SeS0S0R2R1A4M7S3cR22A1M8A3S5S58G3G4VFB;A3A1M9S83R2fS7cR25A1G5A3S58G3SeS0S0R5R4A4MaS3cR23A1A3F_;F_;F_;Fn;Fb;SfeR23SfdR2cR23R2dA3A2S1cS0S0S58G3G7S3cR24A1A3G9S83R31S7cR27A1G5A3S83R6R23GaA3F_;F_;F_;Fn;Fb;TrhoP;SfeR24SfdR2dR24R2eA3A2S1cG3S58G3R1G8A3S4bS72S14S0S0R2A3A2S5S58G3R3VFB;A3A1S83R5R23R4A3S4S58G3R5S3cR28A1A3S83R33S7cR29A1R5A3A2F_;F_;F_;F_;Fbn;TrhoP;VPA;R21A1S85VBX;R22A2S86VBX;R23SfeR27SfdR30R27R31A3A2R21A4VJAi;S7eR22R21R20S7fR27A1A4R24R25SfeR28SfdR31R28R32A3A2R2bR2aR29A7F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FdK;FdV;Fbd';Ffr';Ftv';Fx;FA2;Fkc;FAi;Fnd;Frho';Fmd';Ftr';FtpL;FrhoL;Fmd;Fms;Ftr;Ftp;Frho;FR;Fs;FL;FPre;FCl;").
Proof using ALA HCST HXGL.
  intros Cl Pre L s R rho tp tr ms md rhoL tpL tr' md' rho' nd Ai kc A2 x tv' fr' bd' dV dK He Hsm Hnf Hnb Hbb HJ HRok Hlink HM2 Hk2 Hsub HFB2 HFR2 HG2 Hkept2
         HP HV0 HKm0 HKf0 HV HK HTV HFR' HL2 HU2 HC2 HPA2 HCK2 HCN2.
  pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
  assert (Hag' : agree_vals (ss_next (ax_S Cl)) rho rho') by (destruct Hlink as (A & _); exact A).
  assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
  { eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]. }
  destruct (nd_below_split _ nd Hnb) as (Hbt & Hbf & Hbb0 & Hba).
  pose proof (smatchA_facts segs _ _ _ _ Hsm) as HF.
  assert (Hrm' : forall a, rm rho' a = rm rhoL a) by (intros a; eapply call_linkP_rm; exact Hlink).
  destruct (XA_frame FB (nd_am nd) Ai A2 rho (rho_patch rho' (patchf rho rho' R)) (nd_tv nd) tv' kc HXA) as [HXA' EPOT].
  { intros b n H1 H2 H3. split; [exact (HL2 b n H1 H2 H3) | exact (HU2 b n H1 H2 H3)]. }
  { intros b n z H1 H2 Hz. exact (proj1 (live2_kept Ai A2 x rho rho' rhoL (vms md tp ms) s R tp md b n HM HRok Hkept2 Hrm' H1 H2) z Hz). }
  { intros b n a H1 H2 Ha. exact (proj2 (live2_kept Ai A2 x rho rho' rhoL (vms md tp ms) s R tp md b n HM HRok Hkept2 Hrm' H1 H2) a Ha). }
  { intros e Hin. eapply am_svs_agree; [exact HagP | exact Hba | exact Hin]. }
  { exact HC2. }
  split; [|split; [exact Hk2|split; [|split; [|split; [|split; [|split; [exact HTV|split; [|split; [|split; [exact HP0|split; [exact HXA'|split; [|split; [exact HPA2 | split; [exact HCK2 | exact HCN2]]]]]]]]]]]]]].
  - eapply agree_vals_trans; [exact Hav|]. eapply agree_vals_le; [exact Hnf | exact HagP].
  - eapply (AInv_patch A2 A2 None); [exact HM2 | exact Hrm' | exact Hsub | exact (fun a H => H)].
  - exact (TPA_kept rho0 Ai A2 HG2 HT).
  - exact HFB2.
  - intros f sz fl Hin. rewrite HG2. split; [exact (HFR2 f sz fl Hin) | exact (proj2 (HFF f sz fl Hin))].
  - exact HFR'.
  - eapply (keptFA_step Ai A2 x rho rhoL (vms md tp ms) s R tp md tpL md' rho' HM HM2 HB HFF HFB2); [| exact HT | exact HG2 | exact HRok | exact HK0 | exact Hkept2 | exact Hrm'].
    intros f sz fl Hin. rewrite HG2. split; [exact (HFR2 f sz fl Hin) | exact (proj2 (HFF f sz fl Hin))].
  - cbn [nd_am nd_bd]. rewrite EPOT. eapply BUD_agree; [exact HagP | exact Hbb |].
    eapply (BUD_payF preA (ss_facts (ax_S Cl)) dV dK (nd_bd nd) bd' _ (aa_V Ai) (aa_Km Ai) (aa_Kf Ai)); eauto. all: try (split; assumption).
Qed.

Theorem malloc_callT : ltac2:(tb__ "0|5|
SbSbcA1SbbS34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80SbS6fA1S9eS3bS1cG1VTR;S62Vsegs;Sd1VAInv;RdRcR3VKc;S20PcM2A1A6SbaVE;RdRcA3R2R1A5S9aVsegs;S113R2R1Se5VE;VAInv;VCST;VXGL;RdRcR3VKc;A8A5A2Ftp1;Frho1;FAi;S3S10G0A1S97R9SbaVE;RbRaA3R8A3S12G0R7A2A3S3SaS98RaSbaVE;RcRbA3R9R8SfS34Sc2VE;RcRbA3SfS34SbeVE;RcRbA3S16S34A1A3A3A5ScA3S3SaSa3RaA1ScA3S3SaSf8VNP;S1dS35RcA1A1A2ScA3S3SaS82S1dS35RdA1A1R8A2ScA3S3SaS70S1dS35ReA1A1R8A2ScA3S3SaS28S1dS35RfA1A1S66ReG2A2A2ScA3S3S1bS66S99RfSbaVE;R12R11A3SbeVE;R12R11A3R10A4Sc3A2S20S109S1dS35R10A1A1UaM3A2A1A3S11bS21S35R11A1A1S66R10G2A2S71S81RcA1RbA5S3bS3bVPA;R2A1S42R3R2S6eR12S66R14G2A2A2M4A3VPA;R3A1F_;F_;FA';FA;S11eR13R12R11R10ReS13S0A1S3bS7bS4S4S4bZ1G4A2S4dG4S4eZ2Z27A2A2A2SbfR17R16S69S68R12R13R1A3R14A2A3A2Lms;LAi;A7S1cG1VTR;S62Vsegs;VJA;S7eS7cR11A1S7dR11A1R10S7fR11A1A4A1Sa2SbaVE;R18R17A3R16R15R14Sc2VE;R18R17A3A5R2R1A5RfA2Ftp';Frho';S1cG1VTR;S62Vsegs;VJA;S7eSfSdS1bS1bA2SeS1bS1bS20S109S1dS35R17A1A1G3A2A1S66R16G2A2A4S7cR12A1A3S7dR12A1R11S7fR12A1A4A1Sa2SbaVE;R19R18A3R17R16R15SbeVE;R19R18A3A5R2R1A5R10A2Ftp';Frho';VTR;S62Vsegs;VJA;R11A1R16R13R12A5RfA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;").
Proof using ALA HCST HXGL HKc TR_callP TR_ex TR_facts TR_pre HBX.
  intros W st Cl s R rho tp nd bd' Q CALLEE He Hchk Htp Hnf Hnb Hbb Hs12 Hres HPAY HPAK HSITE Tnull Tok.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex AA (JAk nd)). intros Ai. apply (TR_ex Z (JAi nd Ai)). intros kc.
  eapply (TR_callP (JAi nd Ai kc) (J_alloc_pre AInv W st Ai Kc (SVar 12)) Cl (Pre_malloc E W st) s R
            (Posts_malloc E AInv CST XGL W st Ai Kc) (ax_X Cl) Q rho tp (fun r H => H) He).
  - exact Hchk.
  - intros rho1 tp1. apply CALLEE.
  -
    intros tr ms md Hsm HJ. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & Hn & HU).
    split; [eapply AInv_absorb; [exact HM | exact HRok]|]. split; [exact Hk|]. split; [eapply tp_of_TPA; eauto|]. split; [exact HU|].
    pose proof HBU as (_ & _ & _ & _ & _ & HwF & HnF & _).
    destruct HPAY as (HwT & HcK & HPS). destruct (HPS rho HF (conj HP0 Hav) HwF HnF) as (P1 & P2 & NNT). pose proof (bsum_nonneg bd' rho HwT NNT) as [P3 P4].
    cbn [eval]. rewrite rw_call'. split; [|split; [exact Hn | exact (top_of_TPA Ai s rho _ _ Hav HT Htp)]].
    pose proof (bv_urange (eval rho (wsub_get s 12))) as HR12. unfold uval in P1.
    apply budget_ok_alloc_intro; [eapply (BUD_limit_ok_alloc (nd_bd nd) _); [exact HBU | lia | lia | lia] | | exact (prim_room_JA _ _ nd Ai rho HBX HCNi Hnb)].
    exact (sec_room_JA _ _ _ Ai rho (BXok_d_ok _ _ HBX) HCKi (proj1 (proj1 (apot_range (nd_am nd) rho))) ltac:(eapply XA_kc_nonneg; exact HXA) HBU).
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & Hn & HU).
    pose proof (entails_frA_base _ _ _ _ SHADOW_OFF He eq_refl) as HbC.
    set (n := uval rho (wsub_get s 12)) in *.
    assert (Hn12 : bv_unsigned (rw (rho_sub (rho_absorb rho R (vms md tp ms)) s) 12%positive) = n) by (subst n; rewrite rw_call'; reflexivity).
    cbn [Posts_malloc In] in HinL.
    destruct HinL as [HinL | [HinL | []]]; injection HinL as HL HJLe; subst L JL.
    +
      destruct HJL as (A2 & HM2 & HL2 & HF2 & HV2 & HKm2 & HKf2 & HG2 & Hkept2 & Hk2 & HC2).
      assert (Hsub : forall a, cmaddrA Ai None a -> cmaddrA A2 None a).
      { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
        - right; right; left. exists b, m. rewrite HL2. auto.
        - right; right; right. exists f, sz. rewrite HF2. auto. }
      split.
      * split; [split; [exact (KEPT_stepA Ai A2 None rho rhoL _ s R _ _ _ HM HRok Hsub Hkept2)|]|split].
        -- intros o' oR Hin' _. exfalso. destruct (new_objs_not_pre _ _ _ Hin') as [A B0]. exact (B0 A).
        -- intros r a j oR Hr. cbn in Hr. destruct Hr.
        -- eapply (caller_X_kept Ai A2 None rho tp md R (vms md tp ms) s rhoL Cl); eauto.
           ++ eapply xrs_range; eauto.
           ++ intros o' Hin'. exfalso. destruct (new_objs_not_pre _ _ _ Hin') as [A B0]. exact (B0 A).
      * intros rho' Hlink.
        eapply TR_pre; [ | apply (Tnull (rho_patch rho' (patchf rho rho' R)) tpL)].
        intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
        destruct HJ' as (A2' & HM2' & HL2' & HF2' & HV2' & HKm2' & HKf2' & HG2' & Hkept2' & Hk2' & HC2').
        destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
        split; [exact (cont_smatchA Cl (Pre_malloc E W st) _ s R rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
        exists A2', kc.
        assert (Hsub' : forall a, cmaddrA Ai None a -> cmaddrA A2' None a).
        { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
          - right; right; left. exists b, m. rewrite HL2'. auto.
          - right; right; right. exists f, sz. rewrite HF2'. auto. }
        destruct (law_budget _ _ _ ALA A2' _ _ _ HM2') as (_ & _ & HV0 & HKm0 & HKf0).
        pose proof (HPAK Ai A2' HPA ltac:(rewrite <- Hn12; exact HC2')) as HPA2.
        eapply (cont_JAi Cl (Pre_malloc E W st) (L_malloc_null E W st) s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc A2' None
                  (nd_tv nd) bd' (wsub_get s 12) KU He Hsm Hnf Hnb Hbb HJ HRok Hlink HM2' Hk2' Hsub'); try assumption.
        -- intros b Hb. rewrite HL2'. exact (HB b Hb).
        -- rewrite HV2', Hn12. unfold n. lia.
        -- rewrite HKm2', HKf2'. unfold KU. lia.
        -- assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
           { eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]. }
           destruct (nd_below_split _ _ Hnb) as (Hbt & _ & _ & _).
           cbn zeta. split; [|split].
           ++ apply (tvinA_agree FB A2' (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt |].
              unfold tvinA in HN |- *. apply Forall_forall. intros t Ht Hnz.
              destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [rewrite HL2'; exact X1 | exact X2].
           ++ apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HD].
           ++ apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HZ].
        -- intros b m Hb _ _. rewrite HL2'. exact Hb.
        -- chain_same_tv Hlink Hnb.
        -- cen_same_tv Hlink Hnb HL2'.
        -- capK_same_tac HCKi HL2' HV2'.
        -- capN_same_tac HCNi Hlink Hnb HL2'.
    +
      destruct HJL as (A2 & l1 & l2 & HM2 & HL2 & HLi & HF2 & HV2 & HKm2 & HKf2 & HG2 & Hkept2 & Hk2 & HC2).
      set (p := bv_unsigned (rw rhoL V_RES)) in *.
      rewrite Hn12 in HL2.
      assert (HinNew : In (p, n) (aa_live A2)) by (rewrite HL2; apply in_or_app; right; left; reflexivity).
      assert (Hsub : forall a, cmaddrA Ai None a -> cmaddrA A2 None a).
      { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
        - right; right; left. exists b, m. rewrite HL2. split; [apply in_app_mid; rewrite <- HLi; exact Hin | auto].
        - right; right; right. exists f, sz. rewrite HF2. auto. }
      destruct (law_blocks _ _ _ ALA A2 _ _ _ HM2) as (HPD & HBl & HFr).
      destruct (HBl p n HinNew) as (G1 & G2 & G3 & G4 & G5). top_rng G4.
      assert (NEWFREE : forall a, p <= a < p + n -> cmaddrA Ai None a -> False).
      { intros a Ha [Hc|[Hc|[(b & m & Hb & _ & Hr)|(f & sz & Hf & Hr)]]].
        -   rewrite <- HG2 in Hc. lia.
        - hcst Hc. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
        - rewrite HLi in Hb. pose proof (pd_mid l1 (p, n) l2 (aa_frames A2) (b, m) ltac:(rewrite <- HL2; exact HPD) Hb) as D. cbn [fst snd] in D. lia.
        - assert (Hf2 : In (f, sz) (aa_frames A2)) by (rewrite HF2; exact Hf).
          apply In_nth_error in Hf2 as [k Hkk].
          assert (Hx : nth_error (aa_live A2 ++ aa_frames A2) (length l1) = Some (p, n)).
          { rewrite nth_error_app1 by (rewrite HL2, length_app; cbn; lia). rewrite HL2, nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
          assert (Hy : nth_error (aa_live A2 ++ aa_frames A2) (length (aa_live A2) + k) = Some (f, sz)).
          { rewrite nth_error_app2 by lia. replace (length (aa_live A2) + k - length (aa_live A2))%nat with k by lia. exact Hkk. }
          pose proof (pd_elems _ _ _ _ _ HPD Hx Hy ltac:(rewrite HL2, length_app; cbn; lia)) as D. cbn [fst snd] in D.
          destruct (HFr f sz ltac:(rewrite HF2; exact Hf)) as (_ & _ & G64 & _). lia. }
      split.
      * split; [split; [exact (KEPT_stepA Ai A2 None rho rhoL _ s R _ _ _ HM HRok Hsub Hkept2)|]|split].
        --
           intros o' oR Hin' HinR. destruct (new_objs_not_pre _ _ _ Hin') as [A B0].
           assert (Ho' : o' = block_obj (SVar 12) DUnknown).
           { cbn [ax_S L_malloc_ok Pre_malloc mkA ss_objs] in A, B0.
             apply in_inv in A as [A|A]; [exfalso; apply B0; left; exact A|].
             apply in_app_or in A as [A|A]; [exfalso; apply B0; right; apply in_or_app; left; exact A|].
             apply in_app_or in A as [[A|[]]|A]; [symmetry; exact A|]. exfalso; apply B0; right; apply in_or_app; right; exact A. }
           subst o'. destruct (obj_range rho oR) as [lo hi] eqn:HR2.
           unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi block_obj].
           rewrite soff_lit_small by lia. unfold soff. cbn [eval]. fold p. rewrite bv_signed_U, (proj1 Hag1 12%positive ltac:(cbv; lia)) || idtac.
           assert (E12 : bv_unsigned (rw rhoL 12%positive) = n).
           { rewrite <- Hn12. f_equal. symmetry. apply (proj1 Hag1). cbv. reflexivity. }
           rewrite bv_signed_U, E12.
           apply ranges_disjoint_by_points. intros a Ha1 Ha2. apply (NEWFREE a).
           ++ destruct (Zsigned_spec n) as [[_ X]|[_ X]]; rewrite X in Ha1; lia.
           ++ apply (HRok oR a HinR). rewrite HR2. cbn [fst snd]. exact Ha2.
        --
           intros r a j oR Hr Ha Hj HoR. cbn [ax_X L_malloc_ok mkA] in Hr. destruct Hr as [<-|[]]. cbn [fst snd eval] in Ha.
           assert (E12 : bv_unsigned (rw rhoL 12%positive) = n).
           { rewrite <- Hn12. f_equal. symmetry. apply (proj1 Hag1). cbv. reflexivity. }
           fold p in Ha. rewrite E12 in Ha.
           intros Hrng. apply (shadow_not_in_R Ai None rho tp md R (bv_unsigned (word_byte (bv_unsigned (eval rhoL (ax_base (L_malloc_ok E W st))) + a / 8) j)) HM HRok).
           ++ cbn [ax_base L_malloc_ok mkA base_sv eval]. rewrite lit_unsigned. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF.
              replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia). apply word_byte_of_shadow; [apply Sh_is_shadow; lia | exact Hj].
           ++ rewrite Z_to_bv_bv_unsigned. exists oR. split; [exact HoR | exact Hrng].
        -- eapply (caller_X_kept Ai A2 None rho tp md R (vms md tp ms) s rhoL Cl); eauto.
           ++ eapply xrs_range; eauto.
           ++ intros o' Hin' w Hw. destruct (new_objs_not_pre _ _ _ Hin') as [A B0].
              assert (Ho' : o' = block_obj (SVar 12) DUnknown).
              { cbn [ax_S L_malloc_ok Pre_malloc mkA ss_objs] in A, B0.
                apply in_inv in A as [A|A]; [exfalso; apply B0; left; exact A|].
                apply in_app_or in A as [A|A]; [exfalso; apply B0; right; apply in_or_app; left; exact A|].
                apply in_app_or in A as [[A|[]]|A]; [symmetry; exact A|]. exfalso; apply B0; right; apply in_or_app; right; exact A. }
              subst o'. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi block_obj].
              rewrite soff_lit_small by lia. unfold soff. cbn [eval]. fold p.
              assert (E12 : bv_unsigned (rw rhoL 12%positive) = n).
              { rewrite <- Hn12. f_equal. symmetry. apply (proj1 Hag1). cbv. reflexivity. }
              rewrite bv_signed_U, E12.
              destruct (Zsigned_spec n) as [[_ X]|[_ X]]; rewrite X; cbn [fst snd]; intros Hr';
                exact (client_not_shadow A2 (bv_unsigned w) rhoL tpL md' HM2 ltac:(left; right; left; exists p, n; split; [exact HinNew | lia]) Hw).
      * intros rho' Hlink.
        eapply TR_pre; [ | apply (Tok (rho_patch rho' (patchf rho rho' R)) tpL)].
        intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
        destruct HJ' as (A3 & k1 & k2 & HM3 & HL3 & HLi3 & HF3 & HV3 & HKm3 & HKf3 & HG3 & Hkept3 & Hk3 & HC3).
        destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
        split; [exact (cont_smatchA Cl (Pre_malloc E W st) _ s R rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
        exists A3, kc.
        rewrite Hn12 in HL3. fold p in HL3.
        assert (Hsub' : forall a, cmaddrA Ai None a -> cmaddrA A3 None a).
        { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
          - right; right; left. exists b, m. rewrite HL3. split; [apply in_app_mid; rewrite <- HLi3; exact Hin | auto].
          - right; right; right. exists f, sz. rewrite HF3. auto. }
        destruct (law_budget _ _ _ ALA A3 _ _ _ HM3) as (_ & _ & HV0 & HKm0 & HKf0).
        destruct (law_blocks _ _ _ ALA A3 _ _ _ HM3) as (HPD3 & HBl3 & _).
        assert (HinNew3 : In (p, n) (aa_live A3)) by (rewrite HL3; apply in_or_app; right; left; reflexivity).
        destruct (HBl3 p n HinNew3) as (G1' & _ & G3' & _).
        assert (Hag' : agree_vals (ss_next (ax_S Cl)) rho rho') by exact (proj1 Hlink).
        assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
        { eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]. }
        assert (E1 : rw rho' (pos_add_nat (ss_next (ax_S Cl)) 10) = rw rhoL V_RES).
        { destruct Hlink as (_ & _ & _ & L4).
          specialize (L4 V_RES). change (ss_next (ax_S (Pre_malloc E W st))) with NF in L4.
          unfold import_subA in Hres. change (ss_next (ax_S (Pre_malloc E W st))) with NF in Hres.
          rewrite Hres in L4. cbn [eval] in L4. symmetry. apply L4; [reflexivity | cbv; lia]. }
        assert (E2 : bv_unsigned (eval rho' (wsub_get s 12)) = n).
        { unfold n, uval. f_equal. symmetry. eapply eval_agree_vals; [exact Hag' | exact Hs12]. }
        assert (Enew : tvv (rho_patch rho' (patchf rho rho' R)) (SVar (pos_add_nat (ss_next (ax_S Cl)) 10), wsub_get s 12) = (p, n)).
        { unfold tvv. cbn [fst snd eval]. rewrite !eval_patch. cbn [eval rho_patch rw]. rewrite E1, E2. reflexivity. }
        pose proof Hnb as Hnb0. destruct (nd_below_split _ _ Hnb) as (Hbt & _ & _ & _).
        pose proof (HPAK Ai A3 HPA ltac:(rewrite <- Hn12; exact HC3)) as HPA2.
        eapply (cont_JAi Cl (Pre_malloc E W st) (L_malloc_ok E W st) s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc A3 None
                  _ bd' (wsub_get s 12) KU He Hsm Hnf Hnb0 Hbb HJ HRok Hlink HM3 Hk3 Hsub'); try assumption.
        -- intros b Hb. rewrite HL3. apply in_app_mid. rewrite <- HLi3. exact (HB b Hb).
        -- rewrite HV3, Hn12. unfold n. lia.
        -- rewrite HKm3, HKf3. unfold KU. lia.
        -- cbn zeta. split; [|split].
           ++
              constructor.
              ** intros _. rewrite Enew. cbn [snd]. split; [lia|]. split; [exact HinNew3|].
                 intros HinFB. pose proof (HB _ HinFB) as Hold. rewrite HLi3 in Hold.
                 pose proof (pd_mid k1 (p, n) k2 (aa_frames A3) (p, n) ltac:(rewrite <- HL3; exact HPD3) Hold) as D. cbn [fst snd] in D. lia.
              ** apply (tvinA_agree FB A3 (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt |].
                 unfold tvinA in HN |- *. apply Forall_forall. intros t Ht Hnz.
                 destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [|exact X2].
                 rewrite HL3. apply in_app_mid. rewrite <- HLi3. exact X1.
           ++
              cbn [tvd]. split.
              ** intros t' Ht' _ Hnz'. rewrite Enew.
                 assert (Hbt' : (sv_below (ss_next (ax_S Cl)) (fst t') && sv_below (ss_next (ax_S Cl)) (snd t')) = true) by exact (proj1 (forallb_forall _ _) Hbt t' Ht').
                 rewrite (tvv_agree (ss_next (ax_S Cl)) rho _ t' HagP Hbt').
                 apply (proj1 (tnz_agree (ss_next (ax_S Cl)) rho _ t' HagP Hbt')) in Hnz'.
                 destruct (proj1 (Forall_forall _ _) HN t' Ht' Hnz') as (X0 & X1 & _).
                 intros Heq. rewrite HLi3 in X1.
                 pose proof (pd_mid k1 (p, n) k2 (aa_frames A3) (tvv rho t') ltac:(rewrite <- HL3; exact HPD3) X1) as D.
                 rewrite <- Heq in D. cbn [fst snd] in D. lia.
              ** apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HD].
           ++
              constructor.
              ** intros Hz. exfalso. apply Hz. unfold tnz. change (bv_unsigned (eval ?r (fst ?t))) with (fst (tvv r t)). rewrite Enew. cbn [fst]. lia.
              ** apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HZ].
        -- intros b m Hb _ _. rewrite HL3. apply in_app_mid. rewrite <- HLi3. exact Hb.
        --
           cbn zeta. intros b m Hb _ Hut. apply (proj2 (untracked_tv _ _ _)). intros t [<-|Ht] Hnz.
           ++ rewrite Enew. intros Heq. rewrite HLi3 in Hb.
              pose proof (pd_mid k1 (p, n) k2 (aa_frames A3) (b, m) ltac:(rewrite <- HL3; exact HPD3) Hb) as D. cbn [fst snd] in D.
              injection Heq as E1p E2n. destruct (HBl3 b m ltac:(rewrite HL3; apply in_app_mid; exact Hb)) as (Gm & _). lia.
           ++ revert t Ht Hnz. apply (proj1 (untracked_tv _ _ _)).
              eapply untracked_agree; [exact HagP | exact Hbt | exact Hut].
        -- cbn zeta. exact (cen_insert Ai A3 rho _ _ (nd_tv nd) _ k1 k2 p n HagP Hbt HL3 HLi3 Enew ltac:(destruct (HBl3 p n HinNew3) as (_ & _ & G & _); lia)).
        -- apply (capK_insert Ai A3 k1 k2 p n HCKi HLi3 HL3); [unfold n, uval; match goal with |- context [bv_unsigned ?x] => pose proof (bv_urange x) end; lia | rewrite HV3; try rewrite Hn12; reflexivity].
        -- exact (capN_insert Ai A3 _ rho _ (nd_tv nd) _ k1 k2 p n HCNi HLi3 HL3 HagP Hbt Enew ltac:(destruct (HBl3 p n HinNew3) as (_ & _ & G & _); lia)).
Qed.

Definition Posts_malloc_sel (bn bo : bool) (W : list ulink) (st : ustop) (Ai : AA) : list (axst * jpostA) := ltac2:(tb__ "0|3|
S17SdS34S96A2M0SaSbG0A1M1Lbn;Vbn;SfG0SeS34S96Sc2VE;VW;Vst;A3SdfVAInv;VCST;VXGL;VAi;VKc;A5A4S16G0A1M2A3G2Xax2SaG1Lbo;Vbo;SfG0SeS34S96SbeVE;VW;Vst;A3Se0VAInv;VCST;VXGL;VAi;VKc;A5A4G2A3G2Xax2A3").
Definition Lbl_malloc_sel (bn bo : bool) (W : list ulink) (st : ustop) : list axst := ltac2:(tb__ "0|2|
S17S34SaSbS34A1M0Lbn;Vbn;SfS34Sc2VE;VW;Vst;A3S16S34A1M1A3G1Xax2SaG0Lbo;Vbo;SfS34SbeVE;VW;Vst;A3G1A3G1Xax2A3").
Lemma map_fst_malloc_sel : ltac2:(tb__ "0|0|
SaSaSbSbcA1SbbS3bS3SbS34A1S127SdS34S96A2S34S15S34S96A2S11fR5R4R3R2R1A5A4S121R5R4R3R2A4A3FAi;Fst;FW;Fbo;Fbn;").
Proof using . clear. intros [|] [|] W st Ai; reflexivity. Qed.
Lemma In_malloc_sel : ltac2:(tb__ "0|2|
SaSaSbSbcA1SbbS3bS34S96S58SdS34S96A2M0SeS34S96R2R1A4S11fR7R6R5R4R3A5A3S6S4S3SaR8ScA3S3G0SeS34S96Sc2VE;R6R5A3SdfVAInv;VCST;VXGL;R4VKc;A5A4SeS34S96R3R2A4M1A3A2S4S3SaR7ScA3S3G0SeS34S96SbeVE;R6R5A3Se0VAInv;VCST;VXGL;R4VKc;A5A4G1A3A2A2F_;FJL;FL;FAi;Fst;FW;Fbo;Fbn;").
Proof using .
  clear. intros [|] [|] W st Ai L JL H; cbn [Posts_malloc_sel app In] in H; intuition.
Qed.
Lemma Posts_malloc_sel_all : ltac2:(tb__ "0|0|
SbSbcA1SbbS3bS3SbSdS34S96A2A1S11fScScR3R2R1A5Se5VE;VAInv;VCST;VXGL;R3R2R1VKc;A8A3FAi;Fst;FW;").
Proof using . clear. intros; reflexivity. Qed.

Theorem malloc_callT_gen_sec : ltac2:(tb__ "0|7|
SaSaS3bS1cOF_;F_;S3bOF_;SbSbcA1SbbS34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80SbS6fA1S9eS3bS1cG1VTR;S62Vsegs;S1cG1SbS6dA1M2S6cS4Sd1VAInv;R11R10R7VKc;S20PcM3A1R4R3R2R1AaR13R7R4A2A2Lm;Lt;Lp;Lr;SbaVE;RdRcA3R2R1A5S9aVsegs;S113R2R1S11fR11R10RdRcR3A5A5A2Ftp1;Frho1;FAi;S3S10G0A1S97R9SbaVE;RbRaA3R8A3S12G0R7A2A3S3SaS98RaSbaVE;RcRbA3R9R8S121R10RfRcRbA4A5ScA3S3SaSa3RaA1ScA3S3SaSf8VNP;S1dS35RcA1A1A2ScA3S3SaS82S1dS35RdA1A1R8A2ScA3S3SaS70S1dS35ReA1A1R8A2ScA3S3SaS28S1dS35RfA1A1S66ReG3A2A2ScA3S3S1bS66S99RfSbaVE;R12R11A3SbeVE;R12R11A3R10A4Sc3A2S20S109S1dS35R10A1A1UaM4A2A1A3S11bS21S35R11A1A1S66R10G3A2S71S81RcA1RbA5S3bS3bVPA;R2A1S42R3R2S6eR12S66R14G3A2A2A3R19R3A1F_;F_;FA';FA;S3bS7bS0VPA;R3A1S4bZ0R2A2S73S81R13A1S8eS75VBX;A1S91S7fR13A1R15A2R3A3S3eR5A1S41R5A1S40R5A1R15A6R1dR6S69S68R16R17R5A3R18A2A2F_;F_;F_;Fkc;Fms;FA;S3bS0G2S6cVJAi;R13R4R3R15R14R2R1A7S48R5A1F_;Fmd;Ftr;Fkc;FAi;S3bS0G2S6cVJAi;R14R4R3R16R15R2R1A7S47R5A1F_;Fmd;Ftr;Fkc;FAi;S11eR16R15R14R13R11S13S0A1S3bS7bS4S4S4bZ1S6eR15S66R17G3A2A2M5A2S4dG5S4eZ2Z27A2A2A2SbfR1aR19S69S68R15R16R1A3R17A2A3A2Lms;LAi;A7S3SaR1dScA3M6S1cG1VTR;S62Vsegs;S87VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;R1dS7eS7cR15A1S7dR15A1R14S7fR15A1A4AcSa2SbaVE;R1cR1bA3R1aR19R18Sc2VE;R1cR1bA3A5R2R1A5R13A2Ftp';Frho';F_;G6S1cG1VTR;S62Vsegs;S87VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;R1eS7eSfSdS1bS1bA2SeS1bS1bS20S109S1dS35R1bA1A1G4A2A1S66R1aG3A2A4S7cR16A1A3S7dR16A1R15S7fR16A1A4AcSa2SbaVE;R1dR1cA3R1bR1aR19SbeVE;R1dR1cA3A5R2R1A5R14A2Ftp';Frho';F_;VTR;S62Vsegs;VJA;R14A1R19R16R15A5R12A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;FPA';FCF;Fbo;Fbn;").
Proof using ALA HCST HXGL HKc TR_callP TR_ex TR_facts TR_pre.
  intros bn bo CF PA' W st Cl s R rho tp nd bd' Q CALLEE He Hchk Htp Hnf Hnb Hbb Hs12 Hres HPAY HPAK HCF HSEC HPRIM HSITE Tnull Tok.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex AA (JAk nd)). intros Ai. apply (TR_ex Z (JAi nd Ai)). intros kc.
  eapply (TR_callP (JAi nd Ai kc) (fun r p t m => J_alloc_pre AInv W st Ai Kc (SVar 12) r p t m /\ CF Ai r) Cl (Pre_malloc E W st) s R
            (Posts_malloc_sel bn bo W st Ai) (ax_X Cl) Q rho tp (fun r H => H) He).
  - rewrite map_fst_malloc_sel. exact Hchk.
  - intros rho1 tp1. apply CALLEE.
  -
    intros tr ms md Hsm HJ. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    split; [|exact (HCF Ai (vms md tp ms) kc HPA (XA_kc_nonneg _ _ _ _ _ _ HXA) HBU)].
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & Hn & HU).
    split; [eapply AInv_absorb; [exact HM | exact HRok]|]. split; [exact Hk|]. split; [eapply tp_of_TPA; eauto|]. split; [exact HU|].
    pose proof HBU as (_ & _ & _ & _ & _ & HwF & HnF & _).
    destruct HPAY as (HwT & HcK & HPS). destruct (HPS rho HF (conj HP0 Hav) HwF HnF) as (P1 & P2 & NNT). pose proof (bsum_nonneg bd' rho HwT NNT) as [P3 P4].
    cbn [eval]. rewrite rw_call'. split; [|split; [exact Hn | exact (top_of_TPA Ai s rho _ _ Hav HT Htp)]].
    pose proof (bv_urange (eval rho (wsub_get s 12))) as HR12. unfold uval in P1.
    apply budget_ok_alloc_intro; [eapply (BUD_limit_ok_alloc (nd_bd nd) _); [exact HBU | lia | lia | lia] | | exact (HPRIM Ai kc tr md HJ)].
    exact (HSEC Ai kc tr md HJ).
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & Hn & HU).
    pose proof (entails_frA_base _ _ _ _ SHADOW_OFF He eq_refl) as HbC.
    set (n := uval rho (wsub_get s 12)) in *.
    assert (Hn12 : bv_unsigned (rw (rho_sub (rho_absorb rho R (vms md tp ms)) s) 12%positive) = n) by (subst n; rewrite rw_call'; reflexivity).
    apply In_malloc_sel in HinL.
    destruct HinL as [[Ebn HinL] | [Ebo HinL]]; injection HinL as HL HJLe; subst L JL.
    +
      destruct HJL as (A2 & HM2 & HL2 & HF2 & HV2 & HKm2 & HKf2 & HG2 & Hkept2 & Hk2 & HC2).
      assert (Hsub : forall a, cmaddrA Ai None a -> cmaddrA A2 None a).
      { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
        - right; right; left. exists b, m. rewrite HL2. auto.
        - right; right; right. exists f, sz. rewrite HF2. auto. }
      split.
      * split; [split; [exact (KEPT_stepA Ai A2 None rho rhoL _ s R _ _ _ HM HRok Hsub Hkept2)|]|split].
        -- intros o' oR Hin' _. exfalso. destruct (new_objs_not_pre _ _ _ Hin') as [A B0]. exact (B0 A).
        -- intros r a j oR Hr. cbn in Hr. destruct Hr.
        -- eapply (caller_X_kept Ai A2 None rho tp md R (vms md tp ms) s rhoL Cl); eauto.
           ++ eapply xrs_range; eauto.
           ++ intros o' Hin'. exfalso. destruct (new_objs_not_pre _ _ _ Hin') as [A B0]. exact (B0 A).
      * intros rho' Hlink.
        eapply TR_pre; [ | apply (Tnull Ebn (rho_patch rho' (patchf rho rho' R)) tpL)].
        intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
        destruct HJ' as (A2' & HM2' & HL2' & HF2' & HV2' & HKm2' & HKf2' & HG2' & Hkept2' & Hk2' & HC2').
        destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
        split; [exact (cont_smatchA Cl (Pre_malloc E W st) _ s R rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
        exists A2', kc.
        assert (Hsub' : forall a, cmaddrA Ai None a -> cmaddrA A2' None a).
        { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
          - right; right; left. exists b, m. rewrite HL2'. auto.
          - right; right; right. exists f, sz. rewrite HF2'. auto. }
        destruct (law_budget _ _ _ ALA A2' _ _ _ HM2') as (_ & _ & HV0 & HKm0 & HKf0).
        pose proof (HPAK Ai A2' HPA ltac:(rewrite <- Hn12; exact HC2')) as HPA2.
        eapply (cont_JAi_PA PA' Cl (Pre_malloc E W st) (L_malloc_null E W st) s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc A2' None
                  (nd_tv nd) bd' (wsub_get s 12) KU He Hsm Hnf Hnb Hbb HJ HRok Hlink HM2' Hk2' Hsub'); try assumption.
        -- intros b Hb. rewrite HL2'. exact (HB b Hb).
        -- rewrite HV2', Hn12. unfold n. lia.
        -- rewrite HKm2', HKf2'. unfold KU. lia.
        -- assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
           { eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]. }
           destruct (nd_below_split _ _ Hnb) as (Hbt & _ & _ & _).
           cbn zeta. split; [|split].
           ++ apply (tvinA_agree FB A2' (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt |].
              unfold tvinA in HN |- *. apply Forall_forall. intros t Ht Hnz.
              destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [rewrite HL2'; exact X1 | exact X2].
           ++ apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HD].
           ++ apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HZ].
        -- intros b m Hb _ _. rewrite HL2'. exact Hb.
        -- chain_same_tv Hlink Hnb.
        -- cen_same_tv Hlink Hnb HL2'.
        -- capK_same_tac HCKi HL2' HV2'.
        -- capN_same_tac HCNi Hlink Hnb HL2'.
    +
      destruct HJL as (A2 & l1 & l2 & HM2 & HL2 & HLi & HF2 & HV2 & HKm2 & HKf2 & HG2 & Hkept2 & Hk2 & HC2).
      set (p := bv_unsigned (rw rhoL V_RES)) in *.
      rewrite Hn12 in HL2.
      assert (HinNew : In (p, n) (aa_live A2)) by (rewrite HL2; apply in_or_app; right; left; reflexivity).
      assert (Hsub : forall a, cmaddrA Ai None a -> cmaddrA A2 None a).
      { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
        - right; right; left. exists b, m. rewrite HL2. split; [apply in_app_mid; rewrite <- HLi; exact Hin | auto].
        - right; right; right. exists f, sz. rewrite HF2. auto. }
      destruct (law_blocks _ _ _ ALA A2 _ _ _ HM2) as (HPD & HBl & HFr).
      destruct (HBl p n HinNew) as (G1 & G2 & G3 & G4 & G5). top_rng G4.
      assert (NEWFREE : forall a, p <= a < p + n -> cmaddrA Ai None a -> False).
      { intros a Ha [Hc|[Hc|[(b & m & Hb & _ & Hr)|(f & sz & Hf & Hr)]]].
        -   rewrite <- HG2 in Hc. lia.
        - hcst Hc. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
        - rewrite HLi in Hb. pose proof (pd_mid l1 (p, n) l2 (aa_frames A2) (b, m) ltac:(rewrite <- HL2; exact HPD) Hb) as D. cbn [fst snd] in D. lia.
        - assert (Hf2 : In (f, sz) (aa_frames A2)) by (rewrite HF2; exact Hf).
          apply In_nth_error in Hf2 as [k Hkk].
          assert (Hx : nth_error (aa_live A2 ++ aa_frames A2) (length l1) = Some (p, n)).
          { rewrite nth_error_app1 by (rewrite HL2, length_app; cbn; lia). rewrite HL2, nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
          assert (Hy : nth_error (aa_live A2 ++ aa_frames A2) (length (aa_live A2) + k) = Some (f, sz)).
          { rewrite nth_error_app2 by lia. replace (length (aa_live A2) + k - length (aa_live A2))%nat with k by lia. exact Hkk. }
          pose proof (pd_elems _ _ _ _ _ HPD Hx Hy ltac:(rewrite HL2, length_app; cbn; lia)) as D. cbn [fst snd] in D.
          destruct (HFr f sz ltac:(rewrite HF2; exact Hf)) as (_ & _ & G64 & _). lia. }
      split.
      * split; [split; [exact (KEPT_stepA Ai A2 None rho rhoL _ s R _ _ _ HM HRok Hsub Hkept2)|]|split].
        --
           intros o' oR Hin' HinR. destruct (new_objs_not_pre _ _ _ Hin') as [A B0].
           assert (Ho' : o' = block_obj (SVar 12) DUnknown).
           { cbn [ax_S L_malloc_ok Pre_malloc mkA ss_objs] in A, B0.
             apply in_inv in A as [A|A]; [exfalso; apply B0; left; exact A|].
             apply in_app_or in A as [A|A]; [exfalso; apply B0; right; apply in_or_app; left; exact A|].
             apply in_app_or in A as [[A|[]]|A]; [symmetry; exact A|]. exfalso; apply B0; right; apply in_or_app; right; exact A. }
           subst o'. destruct (obj_range rho oR) as [lo hi] eqn:HR2.
           unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi block_obj].
           rewrite soff_lit_small by lia. unfold soff. cbn [eval]. fold p. rewrite bv_signed_U, (proj1 Hag1 12%positive ltac:(cbv; lia)) || idtac.
           assert (E12 : bv_unsigned (rw rhoL 12%positive) = n).
           { rewrite <- Hn12. f_equal. symmetry. apply (proj1 Hag1). cbv. reflexivity. }
           rewrite bv_signed_U, E12.
           apply ranges_disjoint_by_points. intros a Ha1 Ha2. apply (NEWFREE a).
           ++ destruct (Zsigned_spec n) as [[_ X]|[_ X]]; rewrite X in Ha1; lia.
           ++ apply (HRok oR a HinR). rewrite HR2. cbn [fst snd]. exact Ha2.
        --
           intros r a j oR Hr Ha Hj HoR. cbn [ax_X L_malloc_ok mkA] in Hr. destruct Hr as [<-|[]]. cbn [fst snd eval] in Ha.
           assert (E12 : bv_unsigned (rw rhoL 12%positive) = n).
           { rewrite <- Hn12. f_equal. symmetry. apply (proj1 Hag1). cbv. reflexivity. }
           fold p in Ha. rewrite E12 in Ha.
           intros Hrng. apply (shadow_not_in_R Ai None rho tp md R (bv_unsigned (word_byte (bv_unsigned (eval rhoL (ax_base (L_malloc_ok E W st))) + a / 8) j)) HM HRok).
           ++ cbn [ax_base L_malloc_ok mkA base_sv eval]. rewrite lit_unsigned. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF.
              replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia). apply word_byte_of_shadow; [apply Sh_is_shadow; lia | exact Hj].
           ++ rewrite Z_to_bv_bv_unsigned. exists oR. split; [exact HoR | exact Hrng].
        -- eapply (caller_X_kept Ai A2 None rho tp md R (vms md tp ms) s rhoL Cl); eauto.
           ++ eapply xrs_range; eauto.
           ++ intros o' Hin' w Hw. destruct (new_objs_not_pre _ _ _ Hin') as [A B0].
              assert (Ho' : o' = block_obj (SVar 12) DUnknown).
              { cbn [ax_S L_malloc_ok Pre_malloc mkA ss_objs] in A, B0.
                apply in_inv in A as [A|A]; [exfalso; apply B0; left; exact A|].
                apply in_app_or in A as [A|A]; [exfalso; apply B0; right; apply in_or_app; left; exact A|].
                apply in_app_or in A as [[A|[]]|A]; [symmetry; exact A|]. exfalso; apply B0; right; apply in_or_app; right; exact A. }
              subst o'. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi block_obj].
              rewrite soff_lit_small by lia. unfold soff. cbn [eval]. fold p.
              assert (E12 : bv_unsigned (rw rhoL 12%positive) = n).
              { rewrite <- Hn12. f_equal. symmetry. apply (proj1 Hag1). cbv. reflexivity. }
              rewrite bv_signed_U, E12.
              destruct (Zsigned_spec n) as [[_ X]|[_ X]]; rewrite X; cbn [fst snd]; intros Hr';
                exact (client_not_shadow A2 (bv_unsigned w) rhoL tpL md' HM2 ltac:(left; right; left; exists p, n; split; [exact HinNew | lia]) Hw).
      * intros rho' Hlink.
        eapply TR_pre; [ | apply (Tok Ebo (rho_patch rho' (patchf rho rho' R)) tpL)].
        intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
        destruct HJ' as (A3 & k1 & k2 & HM3 & HL3 & HLi3 & HF3 & HV3 & HKm3 & HKf3 & HG3 & Hkept3 & Hk3 & HC3).
        destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
        split; [exact (cont_smatchA Cl (Pre_malloc E W st) _ s R rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
        exists A3, kc.
        rewrite Hn12 in HL3. fold p in HL3.
        assert (Hsub' : forall a, cmaddrA Ai None a -> cmaddrA A3 None a).
        { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
          - right; right; left. exists b, m. rewrite HL3. split; [apply in_app_mid; rewrite <- HLi3; exact Hin | auto].
          - right; right; right. exists f, sz. rewrite HF3. auto. }
        destruct (law_budget _ _ _ ALA A3 _ _ _ HM3) as (_ & _ & HV0 & HKm0 & HKf0).
        destruct (law_blocks _ _ _ ALA A3 _ _ _ HM3) as (HPD3 & HBl3 & _).
        assert (HinNew3 : In (p, n) (aa_live A3)) by (rewrite HL3; apply in_or_app; right; left; reflexivity).
        destruct (HBl3 p n HinNew3) as (G1' & _ & G3' & _).
        assert (Hag' : agree_vals (ss_next (ax_S Cl)) rho rho') by exact (proj1 Hlink).
        assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
        { eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]. }
        assert (E1 : rw rho' (pos_add_nat (ss_next (ax_S Cl)) 10) = rw rhoL V_RES).
        { destruct Hlink as (_ & _ & _ & L4).
          specialize (L4 V_RES). change (ss_next (ax_S (Pre_malloc E W st))) with NF in L4.
          unfold import_subA in Hres. change (ss_next (ax_S (Pre_malloc E W st))) with NF in Hres.
          rewrite Hres in L4. cbn [eval] in L4. symmetry. apply L4; [reflexivity | cbv; lia]. }
        assert (E2 : bv_unsigned (eval rho' (wsub_get s 12)) = n).
        { unfold n, uval. f_equal. symmetry. eapply eval_agree_vals; [exact Hag' | exact Hs12]. }
        assert (Enew : tvv (rho_patch rho' (patchf rho rho' R)) (SVar (pos_add_nat (ss_next (ax_S Cl)) 10), wsub_get s 12) = (p, n)).
        { unfold tvv. cbn [fst snd eval]. rewrite !eval_patch. cbn [eval rho_patch rw]. rewrite E1, E2. reflexivity. }
        pose proof Hnb as Hnb0. destruct (nd_below_split _ _ Hnb) as (Hbt & _ & _ & _).
        pose proof (HPAK Ai A3 HPA ltac:(rewrite <- Hn12; exact HC3)) as HPA2.
        eapply (cont_JAi_PA PA' Cl (Pre_malloc E W st) (L_malloc_ok E W st) s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc A3 None
                  _ bd' (wsub_get s 12) KU He Hsm Hnf Hnb0 Hbb HJ HRok Hlink HM3 Hk3 Hsub'); try assumption.
        -- intros b Hb. rewrite HL3. apply in_app_mid. rewrite <- HLi3. exact (HB b Hb).
        -- rewrite HV3, Hn12. unfold n. lia.
        -- rewrite HKm3, HKf3. unfold KU. lia.
        -- cbn zeta. split; [|split].
           ++
              constructor.
              ** intros _. rewrite Enew. cbn [snd]. split; [lia|]. split; [exact HinNew3|].
                 intros HinFB. pose proof (HB _ HinFB) as Hold. rewrite HLi3 in Hold.
                 pose proof (pd_mid k1 (p, n) k2 (aa_frames A3) (p, n) ltac:(rewrite <- HL3; exact HPD3) Hold) as D. cbn [fst snd] in D. lia.
              ** apply (tvinA_agree FB A3 (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt |].
                 unfold tvinA in HN |- *. apply Forall_forall. intros t Ht Hnz.
                 destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [|exact X2].
                 rewrite HL3. apply in_app_mid. rewrite <- HLi3. exact X1.
           ++
              cbn [tvd]. split.
              ** intros t' Ht' _ Hnz'. rewrite Enew.
                 assert (Hbt' : (sv_below (ss_next (ax_S Cl)) (fst t') && sv_below (ss_next (ax_S Cl)) (snd t')) = true) by exact (proj1 (forallb_forall _ _) Hbt t' Ht').
                 rewrite (tvv_agree (ss_next (ax_S Cl)) rho _ t' HagP Hbt').
                 apply (proj1 (tnz_agree (ss_next (ax_S Cl)) rho _ t' HagP Hbt')) in Hnz'.
                 destruct (proj1 (Forall_forall _ _) HN t' Ht' Hnz') as (X0 & X1 & _).
                 intros Heq. rewrite HLi3 in X1.
                 pose proof (pd_mid k1 (p, n) k2 (aa_frames A3) (tvv rho t') ltac:(rewrite <- HL3; exact HPD3) X1) as D.
                 rewrite <- Heq in D. cbn [fst snd] in D. lia.
              ** apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HD].
           ++
              constructor.
              ** intros Hz. exfalso. apply Hz. unfold tnz. change (bv_unsigned (eval ?r (fst ?t))) with (fst (tvv r t)). rewrite Enew. cbn [fst]. lia.
              ** apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HZ].
        -- intros b m Hb _ _. rewrite HL3. apply in_app_mid. rewrite <- HLi3. exact Hb.
        --
           cbn zeta. intros b m Hb _ Hut. apply (proj2 (untracked_tv _ _ _)). intros t [<-|Ht] Hnz.
           ++ rewrite Enew. intros Heq. rewrite HLi3 in Hb.
              pose proof (pd_mid k1 (p, n) k2 (aa_frames A3) (b, m) ltac:(rewrite <- HL3; exact HPD3) Hb) as D. cbn [fst snd] in D.
              injection Heq as E1p E2n. destruct (HBl3 b m ltac:(rewrite HL3; apply in_app_mid; exact Hb)) as (Gm & _). lia.
           ++ revert t Ht Hnz. apply (proj1 (untracked_tv _ _ _)).
              eapply untracked_agree; [exact HagP | exact Hbt | exact Hut].
        -- cbn zeta. exact (cen_insert Ai A3 rho _ _ (nd_tv nd) _ k1 k2 p n HagP Hbt HL3 HLi3 Enew ltac:(destruct (HBl3 p n HinNew3) as (_ & _ & G & _); lia)).
        -- apply (capK_insert Ai A3 k1 k2 p n HCKi HLi3 HL3); [unfold n, uval; match goal with |- context [bv_unsigned ?x] => pose proof (bv_urange x) end; lia | rewrite HV3; try rewrite Hn12; reflexivity].
        -- exact (capN_insert Ai A3 _ rho _ (nd_tv nd) _ k1 k2 p n HCNi HLi3 HL3 HagP Hbt Enew ltac:(destruct (HBl3 p n HinNew3) as (_ & _ & G & _); lia)).
Qed.
Theorem malloc_callT_gen : ltac2:(tb__ "0|7|
SaSaS3bS1cOF_;F_;S3bOF_;SbSbcA1SbbS34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80SbS6fA1S9eS3bS1cG1VTR;S62Vsegs;S1cG1SbS6dA1S6cS4Sd1VAInv;R11R10R7VKc;S20PcM2A1R4R3R2R1AaR13R7R4A2A2Lm;Lt;Lp;Lr;SbaVE;RdRcA3R2R1A5S9aVsegs;S113R2R1S11fR11R10RdRcR3A5A5A2Ftp1;Frho1;FAi;S3S10G0A1S97R9SbaVE;RbRaA3R8A3S12G0R7A2A3S3SaS98RaSbaVE;RcRbA3R9R8S121R10RfRcRbA4A5ScA3S3SaSa3RaA1ScA3S3SaSf8VNP;S1dS35RcA1A1A2ScA3S3SaS82S1dS35RdA1A1R8A2ScA3S3SaS70S1dS35ReA1A1R8A2ScA3S3SaS28S1dS35RfA1A1S66ReG2A2A2ScA3S3S1bS66S99RfSbaVE;R12R11A3SbeVE;R12R11A3R10A4Sc3A2S20S109S1dS35R10A1A1UaM3A2A1A3S11bS21S35R11A1A1S66R10G2A2S71S81RcA1RbA5S3bS3bVPA;R2A1S42R3R2S6eR12S66R14G2A2A2A3R19R3A1F_;F_;FA';FA;S3bS7bS0VPA;R3A1S4bZ0R2A2S73S81R13A1S8eS75VBX;A1S91S7fR13A1M4R15A2R3A3S3eR5A1S41R5A1S40R5A1R15A6R1dR6S69S68R16R17R5A3R18A2A2F_;F_;F_;Fkc;Fms;FA;S11eR14R13R12R11RfS13S0A1S3bS7bS4S4S4bZ1S6eR13S66R15G2A2A2M5A2S4dG5S4eZ2Z27A2A2A2SbfR18R17S69S68R13R14R1A3R15A2A3A2Lms;LAi;A7S3SaR1bScA3M6S1cG1VTR;S62Vsegs;S87VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;R1bS7eS7cR13A1S7dR13A1R12G4A4AcSa2SbaVE;R1aR19A3R18R17R16Sc2VE;R1aR19A3A5R2R1A5R11A2Ftp';Frho';F_;G6S1cG1VTR;S62Vsegs;S87VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;R1cS7eSfSdS1bS1bA2SeS1bS1bS20S109S1dS35R19A1A1G3A2A1S66R18G2A2A4S7cR14A1A3S7dR14A1R13S7fR14A1A4AcSa2SbaVE;R1bR1aA3R19R18R17SbeVE;R1bR1aA3A5R2R1A5R12A2Ftp';Frho';F_;VTR;S62Vsegs;VJA;R12A1R17R14R13A5R10A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;FPA';FCF;Fbo;Fbn;").
Proof using ALA HCST HXGL HKc TR_callP TR_ex TR_facts TR_pre HBX.
  intros bn bo CF PA' W st Cl s R rho tp nd bd' Q CALLEE He Hchk Htp Hnf Hnb Hbb Hs12 Hres HPAY HPAK HCF HSITE Tnull Tok.
  apply (malloc_callT_gen_sec bn bo CF PA' W st Cl s R rho tp nd bd' Q CALLEE He Hchk Htp Hnf Hnb Hbb Hs12 Hres HPAY HPAK HCF); [| |exact HSITE | exact Tnull | exact Tok].
  - intros Ai kc tr md (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HXA & HBU & _ & HCKi & _).
    exact (sec_room_JA _ _ _ Ai rho (BXok_d_ok _ _ HBX) HCKi (proj1 (proj1 (apot_range (nd_am nd) rho))) ltac:(eapply XA_kc_nonneg; exact HXA) HBU).
  - intros Ai kc tr md (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HCNi).
    exact (prim_room_JA _ _ nd Ai rho HBX HCNi Hnb).
Qed.

Definition csz (s : wsub) : sv := ltac2:(tb__ "0|0|
S31S10fS66Vs;PcA2S66Vs;PdA2A3").

Lemma ECS : ltac2:(tb__ "0|0|
S67S1cSbS1eA1S7bS3S5fQ40A1S25S69S68R3R2R1A3R4A2SdbA2S25R3S11dR4A1A2A3Fms;FR;Frho;Fs;").
Proof using . clear. intros s rho R ms. unfold calloc_size, csz. cbn [eval]. rewrite !rw_call'. reflexivity. Qed.

Theorem calloc_callT : ltac2:(tb__ "0|4|
SbSbcA1SbbS34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80SbS6fA1S9eS3bS1cG1VTR;S62Vsegs;Sd1VAInv;RdRcR3VKc;SdbA6SbdVE;RdRcA3R2R1A5S9aVsegs;S113R2R1Se4VE;VAInv;VCST;VXGL;RdRcR3VKc;A8A5A2Ftp1;Frho1;FAi;S3S10G0A1S97R9SbdVE;RbRaA3R8A3S12G0R7A2A3S3SaS98RaSbdVE;RcRbA3R9R8SfS34Sc5VE;RcRbA3SfS34Sc1VE;RcRbA3S16S34A1A3A3A5ScA3S3SaSa3RaA1ScA3S3SaSf8VNP;S1dS35RcA1A1A2ScA3S3SaS82S1dS35RdA1A1R8A2ScA3S3SaS70S1dS35ReA1A1R8A2ScA3S3SaS28S1dS35RfA1A1S11dReA1A2ScA3S3S1bS66S99RfSbdVE;R12R11A3Sc1VE;R12R11A3R10A4Sc3A2S20S109S1dS35R10A1A1UaM2A2A1A3S11bS21S35R11A1A1S11dR10A1S71S81RcA1RbA5S3bS3bVPA;R2A1S42R3R2S6eR12S11dR14A1A2M3A3VPA;R3A1F_;F_;FA';FA;S11eR13R12R11R10ReS13S0A1S3bS7bS4S4S4bZ1G3A2S4dG3S4eZ2Z27A2A2A2S4S3S0S50S6eR12S66R14PcA2A2S6eR12S66R14PdA2A2A2G3A3SbfR17R16S69S68R12R13R1A3R14A2A3A2A2Lms;LAi;A7S1cG1VTR;S62Vsegs;VJA;S7eS7cR11A1S7dR11A1R10S7fR11A1A4A1Sa2SbdVE;R18R17A3R16R15R14Sc5VE;R18R17A3A5R2R1A5RfA2Ftp';Frho';S1cG1VTR;S62Vsegs;VJA;S7eSfSdS1bS1bA2SeS1bS1bS20S109S1dS35R17A1A1G2A2A1S11dR16A1A4S7cR12A1A3S7dR12A1R11S7fR12A1A4A1Sa2SbdVE;R19R18A3R17R16R15Sc1VE;R19R18A3A5R2R1A5R10A2Ftp';Frho';VTR;S62Vsegs;VJA;R11A1R16R13R12A5RfA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;").
Proof using ALA HCST HXGL HKc TR_callP TR_ex TR_facts TR_pre HBX.
  intros W st Cl s R rho tp nd bd' Q CALLEE He Hchk Htp Hnf Hnb Hbb Hs12 Hres HPAY HPAK HSITE Tnull Tok.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex AA (JAk nd)). intros Ai. apply (TR_ex Z (JAi nd Ai)). intros kc.
  eapply (TR_callP (JAi nd Ai kc) (J_alloc_pre AInv W st Ai Kc calloc_size) Cl (Pre_calloc E W st) s R
            (Posts_calloc E AInv CST XGL W st Ai Kc) (ax_X Cl) Q rho tp (fun r H => H) He).
  - exact Hchk.
  - intros rho1 tp1. apply CALLEE.
  -
    intros tr ms md Hsm HJ. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & Hn & Hcs & HU).
    split; [eapply AInv_absorb; [exact HM | exact HRok]|]. split; [exact Hk|]. split; [eapply tp_of_TPA; eauto|]. split; [exact HU|].
    pose proof HBU as (_ & _ & _ & _ & _ & HwF & HnF & _).
    destruct HPAY as (HwT & HcK & HPS). destruct (HPS rho HF (conj HP0 Hav) HwF HnF) as (P1 & P2 & NNT). pose proof (bsum_nonneg bd' rho HwT NNT) as [P3 P4].
    rewrite (ECS s rho R (vms md tp ms)). split; [|split; [exact Hn | exact (top_of_TPA Ai s rho _ _ Hav HT Htp)]].
    pose proof (bv_urange (eval rho (csz s))) as HR12. unfold uval in P1.
    apply budget_ok_alloc_intro; [eapply (BUD_limit_ok_alloc (nd_bd nd) _); [exact HBU | lia | lia | lia] | | exact (prim_room_JA _ _ nd Ai rho HBX HCNi Hnb)].
    exact (sec_room_JA _ _ _ Ai rho (BXok_d_ok _ _ HBX) HCKi (proj1 (proj1 (apot_range (nd_am nd) rho))) ltac:(eapply XA_kc_nonneg; exact HXA) HBU).
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & Hn & Hcs & HU).
    pose proof (entails_frA_base _ _ _ _ SHADOW_OFF He eq_refl) as HbC.
    set (n := uval rho (csz s)) in *.
    assert (Hn12 : bv_unsigned (rw (rho_sub (rho_absorb rho R (vms md tp ms)) s) 12%positive) * bv_unsigned (rw (rho_sub (rho_absorb rho R (vms md tp ms)) s) 13%positive) = n)
      by (rewrite !rw_call'; exact Hcs).
    assert (HnL : bv_unsigned (eval (rho_sub (rho_absorb rho R (vms md tp ms)) s) calloc_size) = n) by (rewrite ECS; reflexivity).
    cbn [Posts_calloc In] in HinL.
    destruct HinL as [HinL | [HinL | []]]; injection HinL as HL HJLe; subst L JL.
    +
      destruct HJL as (A2 & HM2 & HL2 & HF2 & HV2 & HKm2 & HKf2 & HG2 & Hkept2 & Hk2 & HC2).
      assert (Hsub : forall a, cmaddrA Ai None a -> cmaddrA A2 None a).
      { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
        - right; right; left. exists b, m. rewrite HL2. auto.
        - right; right; right. exists f, sz. rewrite HF2. auto. }
      split.
      * split; [split; [exact (KEPT_stepA Ai A2 None rho rhoL _ s R _ _ _ HM HRok Hsub Hkept2)|]|split].
        -- intros o' oR Hin' _. exfalso. destruct (new_objs_not_pre _ _ _ Hin') as [A B0]. exact (B0 A).
        -- intros r a j oR Hr. cbn in Hr. destruct Hr.
        -- eapply (caller_X_kept Ai A2 None rho tp md R (vms md tp ms) s rhoL Cl); eauto.
           ++ eapply xrs_range; eauto.
           ++ intros o' Hin'. exfalso. destruct (new_objs_not_pre _ _ _ Hin') as [A B0]. exact (B0 A).
      * intros rho' Hlink.
        eapply TR_pre; [ | apply (Tnull (rho_patch rho' (patchf rho rho' R)) tpL)].
        intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
        destruct HJ' as (A2' & HM2' & HL2' & HF2' & HV2' & HKm2' & HKf2' & HG2' & Hkept2' & Hk2' & HC2').
        destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
        split; [exact (cont_smatchA Cl (Pre_calloc E W st) _ s R rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
        exists A2', kc.
        assert (Hsub' : forall a, cmaddrA Ai None a -> cmaddrA A2' None a).
        { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
          - right; right; left. exists b, m. rewrite HL2'. auto.
          - right; right; right. exists f, sz. rewrite HF2'. auto. }
        destruct (law_budget _ _ _ ALA A2' _ _ _ HM2') as (_ & _ & HV0 & HKm0 & HKf0).
        pose proof (HPAK Ai A2' HPA ltac:(rewrite <- Hn12; exact HC2')) as HPA2.
        eapply (cont_JAi Cl (Pre_calloc E W st) (L_calloc_null E W st) s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc A2' None
                  (nd_tv nd) bd' (csz s) KU He Hsm Hnf Hnb Hbb HJ HRok Hlink HM2' Hk2' Hsub'); try assumption.
        -- intros b Hb. rewrite HL2'. exact (HB b Hb).
        -- rewrite HV2', Hn12. unfold n. lia.
        -- rewrite HKm2', HKf2'. unfold KU. lia.
        -- assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
           { eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]. }
           destruct (nd_below_split _ _ Hnb) as (Hbt & _ & _ & _).
           cbn zeta. split; [|split].
           ++ apply (tvinA_agree FB A2' (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt |].
              unfold tvinA in HN |- *. apply Forall_forall. intros t Ht Hnz.
              destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [rewrite HL2'; exact X1 | exact X2].
           ++ apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HD].
           ++ apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HZ].
        -- intros b m Hb _ _. rewrite HL2'. exact Hb.
        -- chain_same_tv Hlink Hnb.
        -- cen_same_tv Hlink Hnb HL2'.
        -- capK_same_tac HCKi HL2' HV2'.
        -- capN_same_tac HCNi Hlink Hnb HL2'.
    +
      destruct HJL as (A2 & l1 & l2 & HM2 & HL2 & HLi & HF2 & HV2 & HKm2 & HKf2 & HG2 & Hkept2 & Hk2 & HC2).
      set (p := bv_unsigned (rw rhoL V_RES)) in *.
      rewrite Hn12 in HL2.
      assert (HinNew : In (p, n) (aa_live A2)) by (rewrite HL2; apply in_or_app; right; left; reflexivity).
      assert (Hsub : forall a, cmaddrA Ai None a -> cmaddrA A2 None a).
      { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
        - right; right; left. exists b, m. rewrite HL2. split; [apply in_app_mid; rewrite <- HLi; exact Hin | auto].
        - right; right; right. exists f, sz. rewrite HF2. auto. }
      destruct (law_blocks _ _ _ ALA A2 _ _ _ HM2) as (HPD & HBl & HFr).
      destruct (HBl p n HinNew) as (G1 & G2 & G3 & G4 & G5). top_rng G4.
      assert (NEWFREE : forall a, p <= a < p + n -> cmaddrA Ai None a -> False).
      { intros a Ha [Hc|[Hc|[(b & m & Hb & _ & Hr)|(f & sz & Hf & Hr)]]].
        -   rewrite <- HG2 in Hc. lia.
        - hcst Hc. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
        - rewrite HLi in Hb. pose proof (pd_mid l1 (p, n) l2 (aa_frames A2) (b, m) ltac:(rewrite <- HL2; exact HPD) Hb) as D. cbn [fst snd] in D. lia.
        - assert (Hf2 : In (f, sz) (aa_frames A2)) by (rewrite HF2; exact Hf).
          apply In_nth_error in Hf2 as [k Hkk].
          assert (Hx : nth_error (aa_live A2 ++ aa_frames A2) (length l1) = Some (p, n)).
          { rewrite nth_error_app1 by (rewrite HL2, length_app; cbn; lia). rewrite HL2, nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
          assert (Hy : nth_error (aa_live A2 ++ aa_frames A2) (length (aa_live A2) + k) = Some (f, sz)).
          { rewrite nth_error_app2 by lia. replace (length (aa_live A2) + k - length (aa_live A2))%nat with k by lia. exact Hkk. }
          pose proof (pd_elems _ _ _ _ _ HPD Hx Hy ltac:(rewrite HL2, length_app; cbn; lia)) as D. cbn [fst snd] in D.
          destruct (HFr f sz ltac:(rewrite HF2; exact Hf)) as (_ & _ & G64 & _). lia. }
      split.
      * split; [split; [exact (KEPT_stepA Ai A2 None rho rhoL _ s R _ _ _ HM HRok Hsub Hkept2)|]|split].
        --
           intros o' oR Hin' HinR. destruct (new_objs_not_pre _ _ _ Hin') as [A B0].
           assert (Ho' : o' = block_obj calloc_size DZero).
           { cbn [ax_S L_calloc_ok Pre_calloc mkA ss_objs] in A, B0.
             apply in_inv in A as [A|A]; [exfalso; apply B0; left; exact A|].
             apply in_app_or in A as [A|A]; [exfalso; apply B0; right; apply in_or_app; left; exact A|].
             apply in_app_or in A as [[A|[]]|A]; [symmetry; exact A|]. exfalso; apply B0; right; apply in_or_app; right; exact A. }
           subst o'. destruct (obj_range rho oR) as [lo hi] eqn:HR2.
           unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi block_obj].
           rewrite soff_lit_small by lia. unfold soff. change (eval rhoL (SVar V_RES)) with (rw rhoL V_RES). fold p.
           assert (E12 : bv_unsigned (eval rhoL calloc_size) = n).
           { rewrite <- HnL. f_equal. symmetry. eapply eval_agree_vals; [exact Hag1 | reflexivity]. }
           rewrite bv_signed_U, E12.
           apply ranges_disjoint_by_points. intros a Ha1 Ha2. apply (NEWFREE a).
           ++ destruct (Zsigned_spec n) as [[_ X]|[_ X]]; rewrite X in Ha1; lia.
           ++ apply (HRok oR a HinR). rewrite HR2. cbn [fst snd]. exact Ha2.
        --
           intros r a j oR Hr Ha Hj HoR. cbn [ax_X L_calloc_ok mkA] in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Ha.
           assert (E12 : bv_unsigned (eval rhoL calloc_size) = n).
           { rewrite <- HnL. f_equal. symmetry. eapply eval_agree_vals; [exact Hag1 | reflexivity]. }
           change (eval rhoL (SVar V_RES)) with (rw rhoL V_RES) in Ha. fold p in Ha. rewrite E12 in Ha.
           intros Hrng. apply (shadow_not_in_R Ai None rho tp md R (bv_unsigned (word_byte (bv_unsigned (eval rhoL (ax_base (L_calloc_ok E W st))) + a / 8) j)) HM HRok).
           ++ cbn [ax_base L_calloc_ok mkA base_sv eval]. rewrite lit_unsigned. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF.
              replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia). apply word_byte_of_shadow; [apply Sh_is_shadow; lia | exact Hj].
           ++ rewrite Z_to_bv_bv_unsigned. exists oR. split; [exact HoR | exact Hrng].
        -- eapply (caller_X_kept Ai A2 None rho tp md R (vms md tp ms) s rhoL Cl); eauto.
           ++ eapply xrs_range; eauto.
           ++ intros o' Hin' w Hw. destruct (new_objs_not_pre _ _ _ Hin') as [A B0].
              assert (Ho' : o' = block_obj calloc_size DZero).
              { cbn [ax_S L_calloc_ok Pre_calloc mkA ss_objs] in A, B0.
                apply in_inv in A as [A|A]; [exfalso; apply B0; left; exact A|].
                apply in_app_or in A as [A|A]; [exfalso; apply B0; right; apply in_or_app; left; exact A|].
                apply in_app_or in A as [[A|[]]|A]; [symmetry; exact A|]. exfalso; apply B0; right; apply in_or_app; right; exact A. }
              subst o'. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi block_obj].
              rewrite soff_lit_small by lia. unfold soff. change (eval rhoL (SVar V_RES)) with (rw rhoL V_RES). fold p.
              assert (E12 : bv_unsigned (eval rhoL calloc_size) = n).
              { rewrite <- HnL. f_equal. symmetry. eapply eval_agree_vals; [exact Hag1 | reflexivity]. }
              rewrite bv_signed_U, E12.
              destruct (Zsigned_spec n) as [[_ X]|[_ X]]; rewrite X; cbn [fst snd]; intros Hr';
                exact (client_not_shadow A2 (bv_unsigned w) rhoL tpL md' HM2 ltac:(left; right; left; exists p, n; split; [exact HinNew | lia]) Hw).
      * intros rho' Hlink.
        eapply TR_pre; [ | apply (Tok (rho_patch rho' (patchf rho rho' R)) tpL)].
        intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
        destruct HJ' as (A3 & k1 & k2 & HM3 & HL3 & HLi3 & HF3 & HV3 & HKm3 & HKf3 & HG3 & Hkept3 & Hk3 & HC3).
        destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
        split; [exact (cont_smatchA Cl (Pre_calloc E W st) _ s R rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
        exists A3, kc.
        rewrite Hn12 in HL3. fold p in HL3.
        assert (Hsub' : forall a, cmaddrA Ai None a -> cmaddrA A3 None a).
        { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
          - right; right; left. exists b, m. rewrite HL3. split; [apply in_app_mid; rewrite <- HLi3; exact Hin | auto].
          - right; right; right. exists f, sz. rewrite HF3. auto. }
        destruct (law_budget _ _ _ ALA A3 _ _ _ HM3) as (_ & _ & HV0 & HKm0 & HKf0).
        destruct (law_blocks _ _ _ ALA A3 _ _ _ HM3) as (HPD3 & HBl3 & _).
        assert (HinNew3 : In (p, n) (aa_live A3)) by (rewrite HL3; apply in_or_app; right; left; reflexivity).
        destruct (HBl3 p n HinNew3) as (G1' & _ & G3' & _).
        assert (Hag' : agree_vals (ss_next (ax_S Cl)) rho rho') by exact (proj1 Hlink).
        assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
        { eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]. }
        assert (E1 : rw rho' (pos_add_nat (ss_next (ax_S Cl)) 10) = rw rhoL V_RES).
        { destruct Hlink as (_ & _ & _ & L4).
          specialize (L4 V_RES). change (ss_next (ax_S (Pre_calloc E W st))) with NF in L4.
          unfold import_subA in Hres. change (ss_next (ax_S (Pre_calloc E W st))) with NF in Hres.
          rewrite Hres in L4. cbn [eval] in L4. symmetry. apply L4; [reflexivity | cbv; lia]. }
        assert (E2 : bv_unsigned (eval rho' (csz s)) = n).
        { unfold n, uval. f_equal. symmetry. eapply eval_agree_vals; [exact Hag' | exact Hs12]. }
        assert (Enew : tvv (rho_patch rho' (patchf rho rho' R)) (SVar (pos_add_nat (ss_next (ax_S Cl)) 10), csz s) = (p, n)).
        { unfold tvv. cbn [fst snd eval]. rewrite !eval_patch. cbn [eval rho_patch rw]. rewrite E1, E2. reflexivity. }
        pose proof Hnb as Hnb0. destruct (nd_below_split _ _ Hnb) as (Hbt & _ & _ & _).
        pose proof (HPAK Ai A3 HPA ltac:(rewrite <- Hn12; exact HC3)) as HPA2.
        eapply (cont_JAi Cl (Pre_calloc E W st) (L_calloc_ok E W st) s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc A3 None
                  _ bd' (csz s) KU He Hsm Hnf Hnb0 Hbb HJ HRok Hlink HM3 Hk3 Hsub'); try assumption.
        -- intros b Hb. rewrite HL3. apply in_app_mid. rewrite <- HLi3. exact (HB b Hb).
        -- rewrite HV3, Hn12. unfold n. lia.
        -- rewrite HKm3, HKf3. unfold KU. lia.
        -- cbn zeta. split; [|split].
           ++
              constructor.
              ** intros _. rewrite Enew. cbn [snd]. split; [lia|]. split; [exact HinNew3|].
                 intros HinFB. pose proof (HB _ HinFB) as Hold. rewrite HLi3 in Hold.
                 pose proof (pd_mid k1 (p, n) k2 (aa_frames A3) (p, n) ltac:(rewrite <- HL3; exact HPD3) Hold) as D. cbn [fst snd] in D. lia.
              ** apply (tvinA_agree FB A3 (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt |].
                 unfold tvinA in HN |- *. apply Forall_forall. intros t Ht Hnz.
                 destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [|exact X2].
                 rewrite HL3. apply in_app_mid. rewrite <- HLi3. exact X1.
           ++
              cbn [tvd]. split.
              ** intros t' Ht' _ Hnz'. rewrite Enew.
                 assert (Hbt' : (sv_below (ss_next (ax_S Cl)) (fst t') && sv_below (ss_next (ax_S Cl)) (snd t')) = true) by exact (proj1 (forallb_forall _ _) Hbt t' Ht').
                 rewrite (tvv_agree (ss_next (ax_S Cl)) rho _ t' HagP Hbt').
                 apply (proj1 (tnz_agree (ss_next (ax_S Cl)) rho _ t' HagP Hbt')) in Hnz'.
                 destruct (proj1 (Forall_forall _ _) HN t' Ht' Hnz') as (X0 & X1 & _).
                 intros Heq. rewrite HLi3 in X1.
                 pose proof (pd_mid k1 (p, n) k2 (aa_frames A3) (tvv rho t') ltac:(rewrite <- HL3; exact HPD3) X1) as D.
                 rewrite <- Heq in D. cbn [fst snd] in D. lia.
              ** apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HD].
           ++
              constructor.
              ** intros Hz. exfalso. apply Hz. unfold tnz. change (bv_unsigned (eval ?r (fst ?t))) with (fst (tvv r t)). rewrite Enew. cbn [fst]. lia.
              ** apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HZ].
        -- intros b m Hb _ _. rewrite HL3. apply in_app_mid. rewrite <- HLi3. exact Hb.
        --
           cbn zeta. intros b m Hb _ Hut. apply (proj2 (untracked_tv _ _ _)). intros t [<-|Ht] Hnz.
           ++ rewrite Enew. intros Heq. rewrite HLi3 in Hb.
              pose proof (pd_mid k1 (p, n) k2 (aa_frames A3) (b, m) ltac:(rewrite <- HL3; exact HPD3) Hb) as D. cbn [fst snd] in D.
              injection Heq as E1p E2n. destruct (HBl3 b m ltac:(rewrite HL3; apply in_app_mid; exact Hb)) as (Gm & _). lia.
           ++ revert t Ht Hnz. apply (proj1 (untracked_tv _ _ _)).
              eapply untracked_agree; [exact HagP | exact Hbt | exact Hut].
        -- cbn zeta. exact (cen_insert Ai A3 rho _ _ (nd_tv nd) _ k1 k2 p n HagP Hbt HL3 HLi3 Enew ltac:(destruct (HBl3 p n HinNew3) as (_ & _ & G & _); lia)).
        -- apply (capK_insert Ai A3 k1 k2 p n HCKi HLi3 HL3); [unfold n, uval; match goal with |- context [bv_unsigned ?x] => pose proof (bv_urange x) end; lia | rewrite HV3; try rewrite Hn12; reflexivity].
        -- exact (capN_insert Ai A3 _ rho _ (nd_tv nd) _ k1 k2 p n HCNi HLi3 HL3 HagP Hbt Enew ltac:(destruct (HBl3 p n HinNew3) as (_ & _ & G & _); lia)).
Qed.

Definition Posts_calloc_sel (bn bo : bool) (W : list ulink) (st : ustop) (Ai : AA) : list (axst * jpostA) := ltac2:(tb__ "0|3|
S17SdS34S96A2M0SaSbG0A1M1Lbn;Vbn;SfG0SeS34S96Sc5VE;VW;Vst;A3SddVAInv;VCST;VXGL;VAi;VKc;A5A4S16G0A1M2A3G2Xax2SaG1Lbo;Vbo;SfG0SeS34S96Sc1VE;VW;Vst;A3SdeVAInv;VCST;VXGL;VAi;VKc;A5A4G2A3G2Xax2A3").
Definition Lbl_calloc_sel (bn bo : bool) (W : list ulink) (st : ustop) : list axst := ltac2:(tb__ "0|2|
S17S34SaSbS34A1M0Lbn;Vbn;SfS34Sc5VE;VW;Vst;A3S16S34A1M1A3G1Xax2SaG0Lbo;Vbo;SfS34Sc1VE;VW;Vst;A3G1A3G1Xax2A3").
Lemma map_fst_calloc_sel : ltac2:(tb__ "0|0|
SaSaSbSbcA1SbbS3bS3SbS34A1S127SdS34S96A2S34S15S34S96A2S120R5R4R3R2R1A5A4S122R5R4R3R2A4A3FAi;Fst;FW;Fbo;Fbn;").
Proof using . clear. intros [|] [|] W st Ai; reflexivity. Qed.
Lemma In_calloc_sel : ltac2:(tb__ "0|2|
SaSaSbSbcA1SbbS3bS34S96S58SdS34S96A2M0SeS34S96R2R1A4S120R7R6R5R4R3A5A3S6S4S3SaR8ScA3S3G0SeS34S96Sc5VE;R6R5A3SddVAInv;VCST;VXGL;R4VKc;A5A4SeS34S96R3R2A4M1A3A2S4S3SaR7ScA3S3G0SeS34S96Sc1VE;R6R5A3SdeVAInv;VCST;VXGL;R4VKc;A5A4G1A3A2A2F_;FJL;FL;FAi;Fst;FW;Fbo;Fbn;").
Proof using .
  clear. intros [|] [|] W st Ai L JL H; cbn [Posts_calloc_sel app In] in H; intuition.
Qed.
Lemma Posts_calloc_sel_all : ltac2:(tb__ "0|0|
SbSbcA1SbbS3bS3SbSdS34S96A2A1S120ScScR3R2R1A5Se4VE;VAInv;VCST;VXGL;R3R2R1VKc;A8A3FAi;Fst;FW;").
Proof using . clear. intros; reflexivity. Qed.

Theorem calloc_callT_gen : ltac2:(tb__ "0|6|
SaSaS3bS1cOF_;F_;S3bOF_;SbSbcA1SbbS34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80SbS6fA1S9eS3bS1cG1VTR;S62Vsegs;S1cG1SbS6dA1S6cS4Sd1VAInv;R11R10R7VKc;SdbR4R3R2R1AaR13R7R4A2A2Lm;Lt;Lp;Lr;SbdVE;RdRcA3R2R1A5S9aVsegs;S113R2R1S120R11R10RdRcR3A5A5A2Ftp1;Frho1;FAi;S3S10G0A1S97R9SbdVE;RbRaA3R8A3S12G0R7A2A3S3SaS98RaSbdVE;RcRbA3R9R8S122R10RfRcRbA4A5ScA3S3SaSa3RaA1ScA3S3SaSf8VNP;S1dS35RcA1A1A2ScA3S3SaS82S1dS35RdA1A1R8A2ScA3S3SaS70S1dS35ReA1A1R8A2ScA3S3SaS28S1dS35RfA1A1S11dReA1A2ScA3S3S1bS66S99RfSbdVE;R12R11A3Sc1VE;R12R11A3R10A4Sc3A2S20S109S1dS35R10A1A1UaM2A2A1A3S11bS21S35R11A1A1S11dR10A1S71S81RcA1RbA5S3bS3bVPA;R2A1M3S42R3R2S6eR12S11dR14A1A2A3R19R3A1F_;F_;FA';FA;S3bS7bG3R1aR3S69S68R13R14R2A3R15A2A2F_;Fms;FA;S11eR14R13R12R11RfS13S0A1S3bS7bS4S4S4bZ1S6eR13S11dR15A1A2M4A2S4dG4S4eZ2Z27A2A2A2S4S3S0S50S6eR13S66R15PcA2A2S6eR13S66R15PdA2A2A2G4A3SbfR18R17S69S68R13R14R1A3R15A2A3A2A2Lms;LAi;A7S3SaR1bScA3M5S1cG1VTR;S62Vsegs;S87VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;R1bS7eS7cR13A1S7dR13A1R12S7fR13A1A4AcSa2SbdVE;R1aR19A3R18R17R16Sc5VE;R1aR19A3A5R2R1A5R11A2Ftp';Frho';F_;G5S1cG1VTR;S62Vsegs;S87VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;R1cS7eSfSdS1bS1bA2SeS1bS1bS20S109S1dS35R19A1A1G2A2A1S11dR18A1A4S7cR14A1A3S7dR14A1R13S7fR14A1A4AcSa2SbdVE;R1bR1aA3R19R18R17Sc1VE;R1bR1aA3A5R2R1A5R12A2Ftp';Frho';F_;VTR;S62Vsegs;VJA;R12A1R17R14R13A5R10A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;FPA';FCF;Fbo;Fbn;").
Proof using ALA HCST HXGL HKc TR_callP TR_ex TR_facts TR_pre HBX.
  intros bn bo CF PA' W st Cl s R rho tp nd bd' Q CALLEE He Hchk Htp Hnf Hnb Hbb Hs12 Hres HPAY HPAK HCF HSITE Tnull Tok.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex AA (JAk nd)). intros Ai. apply (TR_ex Z (JAi nd Ai)). intros kc.
  eapply (TR_callP (JAi nd Ai kc) (fun r p t m => J_alloc_pre AInv W st Ai Kc calloc_size r p t m /\ CF Ai r) Cl (Pre_calloc E W st) s R
            (Posts_calloc_sel bn bo W st Ai) (ax_X Cl) Q rho tp (fun r H => H) He).
  - rewrite map_fst_calloc_sel. exact Hchk.
  - intros rho1 tp1. apply CALLEE.
  -
    intros tr ms md Hsm HJ. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    split; [|exact (HCF Ai (vms md tp ms) HPA)].
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & Hn & Hcs & HU).
    split; [eapply AInv_absorb; [exact HM | exact HRok]|]. split; [exact Hk|]. split; [eapply tp_of_TPA; eauto|]. split; [exact HU|].
    pose proof HBU as (_ & _ & _ & _ & _ & HwF & HnF & _).
    destruct HPAY as (HwT & HcK & HPS). destruct (HPS rho HF (conj HP0 Hav) HwF HnF) as (P1 & P2 & NNT). pose proof (bsum_nonneg bd' rho HwT NNT) as [P3 P4].
    rewrite (ECS s rho R (vms md tp ms)). split; [|split; [exact Hn | exact (top_of_TPA Ai s rho _ _ Hav HT Htp)]].
    pose proof (bv_urange (eval rho (csz s))) as HR12. unfold uval in P1.
    apply budget_ok_alloc_intro; [eapply (BUD_limit_ok_alloc (nd_bd nd) _); [exact HBU | lia | lia | lia] | | exact (prim_room_JA _ _ nd Ai rho HBX HCNi Hnb)].
    exact (sec_room_JA _ _ _ Ai rho (BXok_d_ok _ _ HBX) HCKi (proj1 (proj1 (apot_range (nd_am nd) rho))) ltac:(eapply XA_kc_nonneg; exact HXA) HBU).
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & Hn & Hcs & HU).
    pose proof (entails_frA_base _ _ _ _ SHADOW_OFF He eq_refl) as HbC.
    set (n := uval rho (csz s)) in *.
    assert (Hn12 : bv_unsigned (rw (rho_sub (rho_absorb rho R (vms md tp ms)) s) 12%positive) * bv_unsigned (rw (rho_sub (rho_absorb rho R (vms md tp ms)) s) 13%positive) = n)
      by (rewrite !rw_call'; exact Hcs).
    assert (HnL : bv_unsigned (eval (rho_sub (rho_absorb rho R (vms md tp ms)) s) calloc_size) = n) by (rewrite ECS; reflexivity).
    apply In_calloc_sel in HinL.
    destruct HinL as [[Ebn HinL] | [Ebo HinL]]; injection HinL as HL HJLe; subst L JL.
    +
      destruct HJL as (A2 & HM2 & HL2 & HF2 & HV2 & HKm2 & HKf2 & HG2 & Hkept2 & Hk2 & HC2).
      assert (Hsub : forall a, cmaddrA Ai None a -> cmaddrA A2 None a).
      { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
        - right; right; left. exists b, m. rewrite HL2. auto.
        - right; right; right. exists f, sz. rewrite HF2. auto. }
      split.
      * split; [split; [exact (KEPT_stepA Ai A2 None rho rhoL _ s R _ _ _ HM HRok Hsub Hkept2)|]|split].
        -- intros o' oR Hin' _. exfalso. destruct (new_objs_not_pre _ _ _ Hin') as [A B0]. exact (B0 A).
        -- intros r a j oR Hr. cbn in Hr. destruct Hr.
        -- eapply (caller_X_kept Ai A2 None rho tp md R (vms md tp ms) s rhoL Cl); eauto.
           ++ eapply xrs_range; eauto.
           ++ intros o' Hin'. exfalso. destruct (new_objs_not_pre _ _ _ Hin') as [A B0]. exact (B0 A).
      * intros rho' Hlink.
        eapply TR_pre; [ | apply (Tnull Ebn (rho_patch rho' (patchf rho rho' R)) tpL)].
        intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
        destruct HJ' as (A2' & HM2' & HL2' & HF2' & HV2' & HKm2' & HKf2' & HG2' & Hkept2' & Hk2' & HC2').
        destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
        split; [exact (cont_smatchA Cl (Pre_calloc E W st) _ s R rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
        exists A2', kc.
        assert (Hsub' : forall a, cmaddrA Ai None a -> cmaddrA A2' None a).
        { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
          - right; right; left. exists b, m. rewrite HL2'. auto.
          - right; right; right. exists f, sz. rewrite HF2'. auto. }
        destruct (law_budget _ _ _ ALA A2' _ _ _ HM2') as (_ & _ & HV0 & HKm0 & HKf0).
        pose proof (HPAK Ai A2' HPA ltac:(rewrite <- Hn12; exact HC2')) as HPA2.
        eapply (cont_JAi_PA PA' Cl (Pre_calloc E W st) (L_calloc_null E W st) s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc A2' None
                  (nd_tv nd) bd' (csz s) KU He Hsm Hnf Hnb Hbb HJ HRok Hlink HM2' Hk2' Hsub'); try assumption.
        -- intros b Hb. rewrite HL2'. exact (HB b Hb).
        -- rewrite HV2', Hn12. unfold n. lia.
        -- rewrite HKm2', HKf2'. unfold KU. lia.
        -- assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
           { eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]. }
           destruct (nd_below_split _ _ Hnb) as (Hbt & _ & _ & _).
           cbn zeta. split; [|split].
           ++ apply (tvinA_agree FB A2' (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt |].
              unfold tvinA in HN |- *. apply Forall_forall. intros t Ht Hnz.
              destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [rewrite HL2'; exact X1 | exact X2].
           ++ apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HD].
           ++ apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HZ].
        -- intros b m Hb _ _. rewrite HL2'. exact Hb.
        -- chain_same_tv Hlink Hnb.
        -- cen_same_tv Hlink Hnb HL2'.
        -- capK_same_tac HCKi HL2' HV2'.
        -- capN_same_tac HCNi Hlink Hnb HL2'.
    +
      destruct HJL as (A2 & l1 & l2 & HM2 & HL2 & HLi & HF2 & HV2 & HKm2 & HKf2 & HG2 & Hkept2 & Hk2 & HC2).
      set (p := bv_unsigned (rw rhoL V_RES)) in *.
      rewrite Hn12 in HL2.
      assert (HinNew : In (p, n) (aa_live A2)) by (rewrite HL2; apply in_or_app; right; left; reflexivity).
      assert (Hsub : forall a, cmaddrA Ai None a -> cmaddrA A2 None a).
      { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
        - right; right; left. exists b, m. rewrite HL2. split; [apply in_app_mid; rewrite <- HLi; exact Hin | auto].
        - right; right; right. exists f, sz. rewrite HF2. auto. }
      destruct (law_blocks _ _ _ ALA A2 _ _ _ HM2) as (HPD & HBl & HFr).
      destruct (HBl p n HinNew) as (G1 & G2 & G3 & G4 & G5). top_rng G4.
      assert (NEWFREE : forall a, p <= a < p + n -> cmaddrA Ai None a -> False).
      { intros a Ha [Hc|[Hc|[(b & m & Hb & _ & Hr)|(f & sz & Hf & Hr)]]].
        -   rewrite <- HG2 in Hc. lia.
        - hcst Hc. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
        - rewrite HLi in Hb. pose proof (pd_mid l1 (p, n) l2 (aa_frames A2) (b, m) ltac:(rewrite <- HL2; exact HPD) Hb) as D. cbn [fst snd] in D. lia.
        - assert (Hf2 : In (f, sz) (aa_frames A2)) by (rewrite HF2; exact Hf).
          apply In_nth_error in Hf2 as [k Hkk].
          assert (Hx : nth_error (aa_live A2 ++ aa_frames A2) (length l1) = Some (p, n)).
          { rewrite nth_error_app1 by (rewrite HL2, length_app; cbn; lia). rewrite HL2, nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
          assert (Hy : nth_error (aa_live A2 ++ aa_frames A2) (length (aa_live A2) + k) = Some (f, sz)).
          { rewrite nth_error_app2 by lia. replace (length (aa_live A2) + k - length (aa_live A2))%nat with k by lia. exact Hkk. }
          pose proof (pd_elems _ _ _ _ _ HPD Hx Hy ltac:(rewrite HL2, length_app; cbn; lia)) as D. cbn [fst snd] in D.
          destruct (HFr f sz ltac:(rewrite HF2; exact Hf)) as (_ & _ & G64 & _). lia. }
      split.
      * split; [split; [exact (KEPT_stepA Ai A2 None rho rhoL _ s R _ _ _ HM HRok Hsub Hkept2)|]|split].
        --
           intros o' oR Hin' HinR. destruct (new_objs_not_pre _ _ _ Hin') as [A B0].
           assert (Ho' : o' = block_obj calloc_size DZero).
           { cbn [ax_S L_calloc_ok Pre_calloc mkA ss_objs] in A, B0.
             apply in_inv in A as [A|A]; [exfalso; apply B0; left; exact A|].
             apply in_app_or in A as [A|A]; [exfalso; apply B0; right; apply in_or_app; left; exact A|].
             apply in_app_or in A as [[A|[]]|A]; [symmetry; exact A|]. exfalso; apply B0; right; apply in_or_app; right; exact A. }
           subst o'. destruct (obj_range rho oR) as [lo hi] eqn:HR2.
           unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi block_obj].
           rewrite soff_lit_small by lia. unfold soff. change (eval rhoL (SVar V_RES)) with (rw rhoL V_RES). fold p.
           assert (E12 : bv_unsigned (eval rhoL calloc_size) = n).
           { rewrite <- HnL. f_equal. symmetry. eapply eval_agree_vals; [exact Hag1 | reflexivity]. }
           rewrite bv_signed_U, E12.
           apply ranges_disjoint_by_points. intros a Ha1 Ha2. apply (NEWFREE a).
           ++ destruct (Zsigned_spec n) as [[_ X]|[_ X]]; rewrite X in Ha1; lia.
           ++ apply (HRok oR a HinR). rewrite HR2. cbn [fst snd]. exact Ha2.
        --
           intros r a j oR Hr Ha Hj HoR. cbn [ax_X L_calloc_ok mkA] in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Ha.
           assert (E12 : bv_unsigned (eval rhoL calloc_size) = n).
           { rewrite <- HnL. f_equal. symmetry. eapply eval_agree_vals; [exact Hag1 | reflexivity]. }
           change (eval rhoL (SVar V_RES)) with (rw rhoL V_RES) in Ha. fold p in Ha. rewrite E12 in Ha.
           intros Hrng. apply (shadow_not_in_R Ai None rho tp md R (bv_unsigned (word_byte (bv_unsigned (eval rhoL (ax_base (L_calloc_ok E W st))) + a / 8) j)) HM HRok).
           ++ cbn [ax_base L_calloc_ok mkA base_sv eval]. rewrite lit_unsigned. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF.
              replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia). apply word_byte_of_shadow; [apply Sh_is_shadow; lia | exact Hj].
           ++ rewrite Z_to_bv_bv_unsigned. exists oR. split; [exact HoR | exact Hrng].
        -- eapply (caller_X_kept Ai A2 None rho tp md R (vms md tp ms) s rhoL Cl); eauto.
           ++ eapply xrs_range; eauto.
           ++ intros o' Hin' w Hw. destruct (new_objs_not_pre _ _ _ Hin') as [A B0].
              assert (Ho' : o' = block_obj calloc_size DZero).
              { cbn [ax_S L_calloc_ok Pre_calloc mkA ss_objs] in A, B0.
                apply in_inv in A as [A|A]; [exfalso; apply B0; left; exact A|].
                apply in_app_or in A as [A|A]; [exfalso; apply B0; right; apply in_or_app; left; exact A|].
                apply in_app_or in A as [[A|[]]|A]; [symmetry; exact A|]. exfalso; apply B0; right; apply in_or_app; right; exact A. }
              subst o'. unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi block_obj].
              rewrite soff_lit_small by lia. unfold soff. change (eval rhoL (SVar V_RES)) with (rw rhoL V_RES). fold p.
              assert (E12 : bv_unsigned (eval rhoL calloc_size) = n).
              { rewrite <- HnL. f_equal. symmetry. eapply eval_agree_vals; [exact Hag1 | reflexivity]. }
              rewrite bv_signed_U, E12.
              destruct (Zsigned_spec n) as [[_ X]|[_ X]]; rewrite X; cbn [fst snd]; intros Hr';
                exact (client_not_shadow A2 (bv_unsigned w) rhoL tpL md' HM2 ltac:(left; right; left; exists p, n; split; [exact HinNew | lia]) Hw).
      * intros rho' Hlink.
        eapply TR_pre; [ | apply (Tok Ebo (rho_patch rho' (patchf rho rho' R)) tpL)].
        intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
        destruct HJ' as (A3 & k1 & k2 & HM3 & HL3 & HLi3 & HF3 & HV3 & HKm3 & HKf3 & HG3 & Hkept3 & Hk3 & HC3).
        destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
        split; [exact (cont_smatchA Cl (Pre_calloc E W st) _ s R rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
        exists A3, kc.
        rewrite Hn12 in HL3. fold p in HL3.
        assert (Hsub' : forall a, cmaddrA Ai None a -> cmaddrA A3 None a).
        { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
          - right; right; left. exists b, m. rewrite HL3. split; [apply in_app_mid; rewrite <- HLi3; exact Hin | auto].
          - right; right; right. exists f, sz. rewrite HF3. auto. }
        destruct (law_budget _ _ _ ALA A3 _ _ _ HM3) as (_ & _ & HV0 & HKm0 & HKf0).
        destruct (law_blocks _ _ _ ALA A3 _ _ _ HM3) as (HPD3 & HBl3 & _).
        assert (HinNew3 : In (p, n) (aa_live A3)) by (rewrite HL3; apply in_or_app; right; left; reflexivity).
        destruct (HBl3 p n HinNew3) as (G1' & _ & G3' & _).
        assert (Hag' : agree_vals (ss_next (ax_S Cl)) rho rho') by exact (proj1 Hlink).
        assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
        { eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]. }
        assert (E1 : rw rho' (pos_add_nat (ss_next (ax_S Cl)) 10) = rw rhoL V_RES).
        { destruct Hlink as (_ & _ & _ & L4).
          specialize (L4 V_RES). change (ss_next (ax_S (Pre_calloc E W st))) with NF in L4.
          unfold import_subA in Hres. change (ss_next (ax_S (Pre_calloc E W st))) with NF in Hres.
          rewrite Hres in L4. cbn [eval] in L4. symmetry. apply L4; [reflexivity | cbv; lia]. }
        assert (E2 : bv_unsigned (eval rho' (csz s)) = n).
        { unfold n, uval. f_equal. symmetry. eapply eval_agree_vals; [exact Hag' | exact Hs12]. }
        assert (Enew : tvv (rho_patch rho' (patchf rho rho' R)) (SVar (pos_add_nat (ss_next (ax_S Cl)) 10), csz s) = (p, n)).
        { unfold tvv. cbn [fst snd eval]. rewrite !eval_patch. cbn [eval rho_patch rw]. rewrite E1, E2. reflexivity. }
        pose proof Hnb as Hnb0. destruct (nd_below_split _ _ Hnb) as (Hbt & _ & _ & _).
        pose proof (HPAK Ai A3 HPA ltac:(rewrite <- Hn12; exact HC3)) as HPA2.
        eapply (cont_JAi_PA PA' Cl (Pre_calloc E W st) (L_calloc_ok E W st) s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc A3 None
                  _ bd' (csz s) KU He Hsm Hnf Hnb0 Hbb HJ HRok Hlink HM3 Hk3 Hsub'); try assumption.
        -- intros b Hb. rewrite HL3. apply in_app_mid. rewrite <- HLi3. exact (HB b Hb).
        -- rewrite HV3, Hn12. unfold n. lia.
        -- rewrite HKm3, HKf3. unfold KU. lia.
        -- cbn zeta. split; [|split].
           ++
              constructor.
              ** intros _. rewrite Enew. cbn [snd]. split; [lia|]. split; [exact HinNew3|].
                 intros HinFB. pose proof (HB _ HinFB) as Hold. rewrite HLi3 in Hold.
                 pose proof (pd_mid k1 (p, n) k2 (aa_frames A3) (p, n) ltac:(rewrite <- HL3; exact HPD3) Hold) as D. cbn [fst snd] in D. lia.
              ** apply (tvinA_agree FB A3 (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt |].
                 unfold tvinA in HN |- *. apply Forall_forall. intros t Ht Hnz.
                 destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [|exact X2].
                 rewrite HL3. apply in_app_mid. rewrite <- HLi3. exact X1.
           ++
              cbn [tvd]. split.
              ** intros t' Ht' _ Hnz'. rewrite Enew.
                 assert (Hbt' : (sv_below (ss_next (ax_S Cl)) (fst t') && sv_below (ss_next (ax_S Cl)) (snd t')) = true) by exact (proj1 (forallb_forall _ _) Hbt t' Ht').
                 rewrite (tvv_agree (ss_next (ax_S Cl)) rho _ t' HagP Hbt').
                 apply (proj1 (tnz_agree (ss_next (ax_S Cl)) rho _ t' HagP Hbt')) in Hnz'.
                 destruct (proj1 (Forall_forall _ _) HN t' Ht' Hnz') as (X0 & X1 & _).
                 intros Heq. rewrite HLi3 in X1.
                 pose proof (pd_mid k1 (p, n) k2 (aa_frames A3) (tvv rho t') ltac:(rewrite <- HL3; exact HPD3) X1) as D.
                 rewrite <- Heq in D. cbn [fst snd] in D. lia.
              ** apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HD].
           ++
              constructor.
              ** intros Hz. exfalso. apply Hz. unfold tnz. change (bv_unsigned (eval ?r (fst ?t))) with (fst (tvv r t)). rewrite Enew. cbn [fst]. lia.
              ** apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HZ].
        -- intros b m Hb _ _. rewrite HL3. apply in_app_mid. rewrite <- HLi3. exact Hb.
        --
           cbn zeta. intros b m Hb _ Hut. apply (proj2 (untracked_tv _ _ _)). intros t [<-|Ht] Hnz.
           ++ rewrite Enew. intros Heq. rewrite HLi3 in Hb.
              pose proof (pd_mid k1 (p, n) k2 (aa_frames A3) (b, m) ltac:(rewrite <- HL3; exact HPD3) Hb) as D. cbn [fst snd] in D.
              injection Heq as E1p E2n. destruct (HBl3 b m ltac:(rewrite HL3; apply in_app_mid; exact Hb)) as (Gm & _). lia.
           ++ revert t Ht Hnz. apply (proj1 (untracked_tv _ _ _)).
              eapply untracked_agree; [exact HagP | exact Hbt | exact Hut].
        -- cbn zeta. exact (cen_insert Ai A3 rho _ _ (nd_tv nd) _ k1 k2 p n HagP Hbt HL3 HLi3 Enew ltac:(destruct (HBl3 p n HinNew3) as (_ & _ & G & _); lia)).
        -- apply (capK_insert Ai A3 k1 k2 p n HCKi HLi3 HL3); [unfold n, uval; match goal with |- context [bv_unsigned ?x] => pose proof (bv_urange x) end; lia | rewrite HV3; try rewrite Hn12; reflexivity].
        -- exact (capN_insert Ai A3 _ rho _ (nd_tv nd) _ k1 k2 p n HCNi HLi3 HL3 HagP Hbt Enew ltac:(destruct (HBl3 p n HinNew3) as (_ & _ & G & _); lia)).
Qed.

Lemma in_mid_cases' {T} : ltac2:(tb__ "0|1|
SbVT;A1M0G0VT;VT;S58VT;R1S17VT;R4SfVT;R2R3A3A3A3S6S3VT;R2R3A3S58VT;R2S17VT;R5R4A3A3A2F_;Fy;Fx;Fl2;Fl1;").
Proof using . clear. intros l1 l2 x y H. apply in_app_or in H as [H|[H|H]]; [right | left; auto | right]; apply in_or_app; auto. Qed.

Theorem free_callT : ltac2:(tb__ "0|5|
SbSbcA1SbbS34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80S18SdS1bS1bA2M2SbS6fA1S9eS3bS1cG1VTR;S62Vsegs;SeeVAInv;RfReR3VKc;A5Sc7VE;RfReA3R2R1A5S9aVsegs;S113R2R1SfSdS34S96A2M3SeS34S96ScdVE;RfReA3SeaVAInv;VCST;VXGL;R3VKc;A5A4S16G3A1A3A5A2Ftp1;Frho1;FAi;S3S10G0A1S97RbSc7VE;RdRcA3RaA3S12G0R9A2A3S3SaS98RcSc7VE;ReRdA3RbRaSfS34ScdVE;ReRdA3S16S34A1A3A5ScA3S3SaSa3RcA1ScA3S3SaSf8VNP;S1dS35ReA1A1A2ScA3S3SaS82S1dS35RfA1A1RaA2ScA3S3SaS70S1dS35R10A1A1R8A2ScA3S3S10G2A1S59G2S7cRcA1RbA3S12G2RaA2A3S11bS21S35R12A1A1S23Z0A1S71S81RdA1RaA5S3bS3bVPA;R2A1S45R3R2A2VPA;R3A1F_;F_;FA';FA;S11eR14R13R12R11RfS12S0S6eR11S66R13PcM4A2A2A2S3bS7bS4S102R13RfA2S4S3SdS0S0A2S100R13RfA2SeS0S0S6eR13S66R15G4A2A2S6eR13S66R15PdA2A2A4A3SbfR18R17S69S68R13R14R1A3R15A2A3A2A2Lms;LAi;A7S1cG1VTR;S62Vsegs;VJA;S7eS101G2R11S7cR12A1A3S7dR12A1RfS7fR12A1A4A1Sa2Sc7VE;R19R18A3R17R16R15ScdVE;R19R18A3A5R2R1A5ReA2Ftp';Frho';VTR;S62Vsegs;VJA;R11A1R16R13R12A5RdA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Ft;Fi;Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;").
Proof using ALA HCST HXGL HKc TR_callP TR_ex TR_facts TR_pre.
  intros W st Cl s R rho tp nd i t bd' Q CALLEE He Hchk Htp Hnf Hnb Hbb Hnth HPAY HPAK HSITE Tfree.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex AA (JAk nd)). intros Ai. apply (TR_ex Z (JAi nd Ai)). intros kc.
  set (p := uval rho (wsub_get s 12)) in *. set (n := uval rho (wsub_get s 13)) in *.
  eapply (TR_callP (JAi nd Ai kc) (J_free_pre AInv W st Ai Kc) Cl (Pre_free E W st) s R
            [(L_free E W st, JL_free AInv CST XGL Ai Kc)] (ax_X Cl) Q rho tp (fun r H => H) He).
  - exact Hchk.
  - intros rho1 tp1. apply CALLEE.
  -
    intros tr ms md Hsm HJ. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & Hnz & Ht & HU).
    split; [eapply AInv_absorb; [exact HM | eapply robjs_okA_weaken; exact HRok]|]. split; [exact HU|].
    split.
    { rewrite !rw_call'. destruct (proj1 (Forall_forall _ _) HN t (nth_error_In _ _ Hnth) Hnz) as (_ & X1 & _). rewrite Ht in X1. exact X1. }
    split; [exact Hk|]. split; [eapply tp_of_TPA; eauto|].
    pose proof HBU as (_ & _ & _ & _ & _ & HwF & HnF & _).
    destruct HPAY as (HwT & HcK & HPS). destruct (HPS rho HF (conj HP0 Hav) HwF HnF) as (P1 & P2 & NNT). pose proof (bsum_nonneg bd' rho HwT NNT) as [P3 P4].
    split; [|exact (top_of_TPA Ai s rho _ _ Hav HT Htp)].
    eapply (BUD_limit_ok_free (nd_bd nd) _); [exact HBU | lia].
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & Hnz & Ht & HU).
    pose proof (entails_frA_base _ _ _ _ SHADOW_OFF He eq_refl) as HbC.
    destruct HinL as [HinL | []]; injection HinL as HL HJLe; subst L JL.
    destruct HJL as (A2 & l1 & l2 & HM2 & HLi & HL2 & HF2 & HV2 & HKm2 & HKf2 & HG2 & Hkept2 & Hk2 & HC2).
    rewrite !rw_call' in HLi. fold p n in HLi. change (bv_unsigned (eval rho (wsub_get s 12))) with p in HLi. change (bv_unsigned (eval rho (wsub_get s 13))) with n in HLi.
    destruct (proj1 (Forall_forall _ _) HN t (nth_error_In _ _ Hnth) Hnz) as (Tpos & Tin & TFB). rewrite Ht in Tpos, Tin, TFB. cbn [snd] in Tpos.
    destruct (law_blocks _ _ _ ALA Ai _ _ _ HM) as (HPD & HBl & HFr).
    assert (SAMEBASE : forall b m, In (b, m) (aa_live Ai) -> b <> p -> In (b, m) (l1 ++ l2)).
    { intros b m Hin Hne. rewrite HLi in Hin. destruct (in_mid_cases' l1 l2 (p, n) (b, m) Hin) as [E0|Hin']; [|exact Hin'].
      exfalso. injection E0. lia. }
    assert (Hsub : forall a, cmaddrA Ai (Some p) a -> cmaddrA A2 None a).
    { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
      - right; right; left. exists b, m. rewrite HL2. split; [apply SAMEBASE; [exact Hin | intros ->; apply Hx; reflexivity] | auto].
      - right; right; right. exists f, sz. rewrite HF2. auto. }
    assert (HFB2 : forall b, In b FB -> In b (aa_live A2)).
    { intros [b m] Hb. rewrite HL2. pose proof (HB _ Hb) as Hin. rewrite HLi in Hin.
      destruct (in_mid_cases' l1 l2 (p, n) (b, m) Hin) as [E0|Hin']; [|exact Hin']. exfalso. apply TFB. rewrite <- E0. exact Hb. }
    split.
    * split; [split; [exact (KEPT_stepA Ai A2 (Some p) rho rhoL _ s R _ _ _ HM HRok Hsub Hkept2)|]|split].
      -- intros o' oR Hin' _. exfalso. destruct (new_objs_not_pre _ _ _ Hin') as [A B0].
         cbn [ax_S L_free Pre_free mkA ss_objs] in A, B0. apply B0.
         apply in_inv in A as [A|A]; [left; exact A|]. right. apply in_app_or in A as [A|A]; apply in_or_app; [left; exact A | right; apply in_or_app; right; exact A].
      -- intros r a j oR Hr. cbn in Hr. destruct Hr.
      -- eapply (caller_X_kept Ai A2 (Some p) rho tp md R (vms md tp ms) s rhoL Cl); eauto.
         ++ eapply xrs_range; eauto.
         ++ intros o' Hin'. exfalso. destruct (new_objs_not_pre _ _ _ Hin') as [A B0].
            cbn [ax_S L_free Pre_free mkA ss_objs] in A, B0. apply B0.
            apply in_inv in A as [A|A]; [left; exact A|]. right. apply in_app_or in A as [A|A]; apply in_or_app; [left; exact A | right; apply in_or_app; right; exact A].
    * intros rho' Hlink.
      eapply TR_pre; [ | apply (Tfree (rho_patch rho' (patchf rho rho' R)) tpL)].
      intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
      destruct HJ' as (A3 & k1 & k2 & HM3 & HLi3 & HL3 & HF3 & HV3 & HKm3 & HKf3 & HG3 & Hkept3 & Hk3 & HC3).
      rewrite !rw_call' in HLi3. change (bv_unsigned (eval rho (wsub_get s 12))) with p in HLi3. change (bv_unsigned (eval rho (wsub_get s 13))) with n in HLi3.
      destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
      split; [exact (cont_smatchA Cl (Pre_free E W st) _ s R rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
      exists A3, kc.
      assert (SAMEBASE3 : forall b m, In (b, m) (aa_live Ai) -> b <> p -> In (b, m) (k1 ++ k2)).
      { intros b m Hin Hne. rewrite HLi3 in Hin. destruct (in_mid_cases' k1 k2 (p, n) (b, m) Hin) as [E0|Hin']; [|exact Hin'].
        exfalso. injection E0. lia. }
      assert (DIST3 : forall bm, In bm (aa_live Ai) -> bm <> (p, n) -> In bm (k1 ++ k2)).
      { intros bm Hin Hne. rewrite HLi3 in Hin. destruct (in_mid_cases' k1 k2 (p, n) bm Hin) as [E0|Hin']; [exfalso; exact (Hne E0)|exact Hin']. }
      assert (Hsub' : forall a, cmaddrA Ai (Some p) a -> cmaddrA A3 None a).
      { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
        - right; right; left. exists b, m. rewrite HL3. split; [apply SAMEBASE3; [exact Hin | intros ->; apply Hx; reflexivity] | auto].
        - right; right; right. exists f, sz. rewrite HF3. auto. }
      destruct (law_budget _ _ _ ALA A3 _ _ _ HM3) as (_ & _ & HV0 & HKm0 & HKf0).
      assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
      { eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]. }
      pose proof Hnb as Hnb0. destruct (nd_below_split _ _ Hnb) as (Hbt & _ & _ & _).
      assert (Hbt' : tv_below (ss_next (ax_S Cl)) (remove_nth i (nd_tv nd)) = true).
      { unfold tv_below in *. apply forallb_forall. intros t' Ht'. apply (proj1 (forallb_forall _ _) Hbt). eapply remove_nth_In. exact Ht'. }
      pose proof (HPAK Ai A3 HPA HC3) as HPA2.
      eapply (cont_JAi Cl (Pre_free E W st) (L_free E W st) s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc A3 (Some p)
                _ bd' (SLit 0) KU He Hsm Hnf Hnb0 Hbb HJ HRok Hlink HM3 Hk3 Hsub'); try assumption.
      -- intros [b m] Hb. rewrite HL3. apply DIST3; [exact (HB _ Hb)|]. intros E0. apply TFB. rewrite <- E0. exact Hb.
      -- rewrite HV3. pose proof (uval_range rho (SLit 0)). lia.
      -- rewrite HKm3, HKf3. unfold KU. lia.
      -- cbn zeta. split; [|split].
         ++ apply (tvinA_agree FB A3 (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt' |].
            unfold tvinA in HN |- *. apply Forall_forall. intros t' Ht' Hnz'.
            destruct (proj1 (Forall_forall _ _) HN t' (remove_nth_In _ _ _ Ht') Hnz') as (X0 & X1 & X2).
            split; [exact X0|]. split; [|exact X2]. rewrite HL3. apply DIST3; [exact X1|].
            rewrite <- Ht. exact (tvd_nth_distinct rho (nd_tv nd) i t t' HD Hnth Ht' Hnz Hnz').
         ++ apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt' | apply tvd_remove; exact HD].
         ++ apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt' |].
            unfold tvz in HZ |- *. apply Forall_forall. intros t' Ht'. apply (proj1 (Forall_forall _ _) HZ). eapply remove_nth_In. exact Ht'.
      --
         intros b m Hb _ Hut. rewrite HL3. apply DIST3; [exact Hb|]. intros E0.
         apply (proj1 (untracked_tv _ _ _) Hut t (nth_error_In _ _ Hnth) Hnz). rewrite Ht. symmetry. exact E0.
      -- cbn zeta. intros b m _ _ Hut. eapply untracked_agree; [exact HagP | exact Hbt' |].
         eapply untracked_sub; [| exact Hut]. intros t' Ht'. eapply remove_nth_In. exact Ht'.
      -- cbn zeta. destruct (HBl p n ltac:(rewrite HLi3; apply in_or_app; right; left; reflexivity)) as (Gn & _).
         exact (cen_remove Ai A3 rho _ _ (nd_tv nd) i t k1 k2 p n (aa_frames Ai) HagP Hbt Hnth Ht Gn HLi3 HL3 ltac:(rewrite <- HLi3; exact HPD)).
      -- apply (capK_remove Ai A3 k1 k2 p n HCKi HLi3 HL3). rewrite HV3. lia.
      -- exact (capN_remove Ai A3 _ rho _ (nd_tv nd) i t k1 k2 p n HCNi HLi3 HL3 HagP Hbt Hnth Ht Hnz).
Qed.

Theorem free_null_callT : ltac2:(tb__ "0|5|
SbSbcA1SbbS34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80SbS6fA1S9eS3bS1cG1VTR;S62Vsegs;SedVAInv;RdRcR3VKc;A5Sc8VE;RdRcA3R2R1A5S9aVsegs;S113R2R1SfSdS34S96A2M2SeS34S96SceVE;RdRcA3SebVAInv;VCST;VXGL;R3VKc;A5A4S16G2A1A3A5A2Ftp1;Frho1;FAi;S3S10G0A1S97R9Sc8VE;RbRaA3R8A3S12G0R7A2A3S3SaS98RaSc8VE;RcRbA3R9R8SfS34SceVE;RcRbA3S16S34A1A3A5ScA3S3SaSa3RaA1ScA3S3SaSf8VNP;S1dS35RcA1A1A2ScA3S3SaS82S1dS35RdA1A1R8A2ScA3S3SaS70S1dS35ReA1A1R8A2ScA3S11bS21S35RfA1A1S23Z0M3A1G3S81RaA1R9A5S3bS3bVPA;R2A1M4G4F_;FA';FA;S11eR11R10RfReRcS13S0A1S3bS7bSbfR15R14S69S68R10R11R1A3R12A2A3Lms;LAi;A7S1cG1VTR;S62Vsegs;VJA;S7eS7cRfA1S7dRfA1ReS7fRfA1A4A1Sa2Sc8VE;R16R15A3R14R13R12SceVE;R16R15A3A5R2R1A5RdA2Ftp';Frho';VTR;S62Vsegs;VJA;ReA1R13R10RfA5RcA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;").
Proof using ALA HCST HXGL HKc TR_callP TR_ex TR_facts TR_pre.
  intros W st Cl s R rho tp nd bd' Q CALLEE He Hchk Htp Hnf Hnb Hbb HPAY HPAK HSITE Tcont.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex AA (JAk nd)). intros Ai. apply (TR_ex Z (JAi nd Ai)). intros kc.
  eapply (TR_callP (JAi nd Ai kc) (J_free_null_pre AInv W st Ai Kc) Cl (Pre_free_null E W st) s R
            [(L_free_null E W st, JL_free_null AInv CST XGL Ai Kc)] (ax_X Cl) Q rho tp (fun r H => H) He).
  - exact Hchk.
  - intros rho1 tp1. apply CALLEE.
  -
    intros tr ms md Hsm HJ. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & HU).
    split; [eapply AInv_absorb; [exact HM | exact HRok]|]. split; [exact HU|]. split; [exact Hk|]. split; [eapply tp_of_TPA; eauto | exact (top_of_TPA Ai s rho _ _ Hav HT Htp)].
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & HU).
    pose proof (entails_frA_base _ _ _ _ SHADOW_OFF He eq_refl) as HbC.
    destruct HinL as [HinL | []]; injection HinL as HL HJLe; subst L JL.
    destruct HJL as (A2 & HM2 & HL2 & HF2 & HV2 & HKm2 & HKf2 & HG2 & Hkept2 & Hk2).
    assert (Hsub : forall a, cmaddrA Ai None a -> cmaddrA A2 None a).
    { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
      - right; right; left. exists b, m. rewrite HL2. auto.
      - right; right; right. exists f, sz. rewrite HF2. auto. }
    split.
    * split; [split; [exact (KEPT_stepA Ai A2 None rho rhoL _ s R _ _ _ HM HRok Hsub Hkept2)|]|split].
      -- intros o' oR Hin' _. exfalso. destruct (new_objs_not_pre _ _ _ Hin') as [A B0]. exact (B0 A).
      -- intros r a j oR Hr. cbn in Hr. destruct Hr.
      -- eapply (caller_X_kept Ai A2 None rho tp md R (vms md tp ms) s rhoL Cl); eauto.
         ++ eapply xrs_range; eauto.
         ++ intros o' Hin'. exfalso. destruct (new_objs_not_pre _ _ _ Hin') as [A B0]. exact (B0 A).
    * intros rho' Hlink.
      eapply TR_pre; [ | apply (Tcont (rho_patch rho' (patchf rho rho' R)) tpL)].
      intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
      destruct HJ' as (A3 & HM3 & HL3 & HF3 & HV3 & HKm3 & HKf3 & HG3 & Hkept3 & Hk3).
      destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
      split; [exact (cont_smatchA Cl (Pre_free_null E W st) _ s R rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
      exists A3, kc.
      assert (Hsub' : forall a, cmaddrA Ai None a -> cmaddrA A3 None a).
      { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & sz & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
        - right; right; left. exists b, m. rewrite HL3. auto.
        - right; right; right. exists f, sz. rewrite HF3. auto. }
      destruct (law_budget _ _ _ ALA A3 _ _ _ HM3) as (_ & _ & HV0 & HKm0 & HKf0).
      assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
      { eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]. }
      pose proof Hnb as Hnb0. destruct (nd_below_split _ _ Hnb) as (Hbt & _ & _ & _).
      pose proof (HPAK Ai A3 HPA) as HPA2.
      eapply (cont_JAi Cl (Pre_free_null E W st) (L_free_null E W st) s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc A3 None
                _ bd' (SLit 0) 0 He Hsm Hnf Hnb0 Hbb HJ HRok Hlink HM3 Hk3 Hsub'); try assumption.
      -- intros b Hb. rewrite HL3. exact (HB b Hb).
      -- rewrite HV3. pose proof (uval_range rho (SLit 0)). lia.
      -- rewrite HKm3, HKf3. lia.
      -- cbn zeta. split; [|split].
         ++ apply (tvinA_agree FB A3 (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt |].
            unfold tvinA in HN |- *. apply Forall_forall. intros t' Ht' Hnz'.
            destruct (proj1 (Forall_forall _ _) HN t' Ht' Hnz') as (X0 & X1 & X2). split; [exact X0|]. split; [rewrite HL3; exact X1 | exact X2].
         ++ apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HD].
         ++ apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HZ].
      -- intros b m Hb _ _. rewrite HL3. exact Hb.
      -- chain_same_tv Hlink Hnb0.
      -- cen_same_tv Hlink Hnb0 HL3.
      -- capK_same_tac HCKi HL3 HV3.
      -- capN_same_tac HCNi Hlink Hnb0 HL3.
Qed.

Theorem purec_callT_xp : ltac2:(tb__ "0|5|
S3bS1cOF_;F_;S34SbS34A1S34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80SbS6fA1S9eS3bS1cG1VTR;S62Vsegs;S1cG1SbS6dA1M2S6cS4Se1VAInv;R7VKc;R4R3R2R1A7R12R7R4A2A2Lm;Lt;Lp;Lr;RdR2R1A5S9aVsegs;S113R2R1S127S34SdS34S96A2S34SeS34S96R1Sd7VAInv;VCST;VXGL;R4VKc;A5A4LL;RcA4A5A2Ftp1;Frho1;FAi;S3S1S1dS35RbA1A1S113A3S3S1bS36RcA1S23S114A1A3S3S10G0A1S97RbRdRaA3S12G0R9A2A3S3SaS98RcReRbRaRdA5ScA3S3SaSa3RcA1ScA3S3SaSf8VNP;S1dS35ReA1A1A2ScA3S3SaS82S1dS35RfA1A1RaA2ScA3S3SaS70S1dS35R10A1A1RaA2ScA3S11bS21S35R11A1A1S23Z0M3A1G3S81RcA1RbA5S3SaS5aS34S34S19S19G0SaLx;S10bS35R15A1S35R1A1A2ScS1eG0S11Ll;Ls0;Xbx2S9cR15R1A2A2S27S36R1A1S36R15A1A2A2LL;R13A3ScA3S11eR13R12R11R10ReS13S0A1M4S3bS7bS8Lms;LAi;A7S3bG2S7bS6cS63Vsegs;R15R14R18SeG2S110R3S111R2R1A2A4A5VAInv;R5R16R15R2A4Sa6R6G4R17S37R1aA1A4R1eR7S69S68R18R19S112R4R17R5A3A3R1aA2A2F_;F_;F_;Fmd;Fms;Ftr;FAi;S34S1cG1S58S34R3R19A3VTR;S62Vsegs;VJA;S7eS7cR14A1S7dR14A1R13S7fR14A1A4A1Sa2R1bR19R18R17R4A5R3R2A5R12A2F_;Ftp';Frho';FL;VTR;S62Vsegs;VJA;R11A1R16R13R12A5RfA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;FLs;FPre;FXP;").
Proof using ALA HCST HXGL HKc TR_callP TR_ex TR_facts TR_pre.
  intros XP Pre Ls Cl s R rho tp nd bd' Q CALLEE HNF HbP He Hchk Htp Hnf Hnb Hbb HPAY Hshape HSITE HXP Tcont.
  apply Pos.leb_le in Hnf.
  apply TR_facts. intros HF.
  apply (TR_ex AA (JAk nd)). intros Ai. apply (TR_ex Z (JAi nd Ai)). intros kc.
  eapply (TR_callP (JAi nd Ai kc) (fun r p t m => J_pure_pre AInv Ai Kc r p t m /\ XP Ai r) Cl Pre s R
            (map (fun L => (L, JL_pure AInv CST XGL Ai Kc)) Ls) (ax_X Cl) Q rho tp (fun r H => H) He).
  - rewrite map_map. cbn [fst]. rewrite map_id. exact Hchk.
  - intros rho1 tp1. rewrite HNF. apply CALLEE.
  -
    intros tr ms md Hsm HJ. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & _).
    split; [|exact (HXP Ai tr ms md Hsm HM HX)].
    split; [eapply AInv_absorb; [exact HM | exact HRok]|]. split; [exact Hk|]. split; [eapply tp_of_TPA; eauto | exact (top_of_TPA Ai s rho _ _ Hav HT Htp)].
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & _).
    pose proof (entails_frA_base _ _ _ _ SHADOW_OFF He HbP) as HbC.
    apply in_map_iff in HinL as (L0 & Heq & HinL). injection Heq as HJLe HL. subst L JL.
    pose proof (proj1 (forallb_forall _ _) Hshape L0 HinL) as HS. apply andb_prop in HS as [HS HbL]. apply andb_prop in HS as [Hnonew Hxf].
    apply sv_eqb_sound in HbL. rewrite HbP in HbL.
    assert (NONEW : forall o', In o' (new_objs (ax_S Pre) (ax_S L0)) -> False).
    { intros o' Hin'. destruct (new_objs (ax_S Pre) (ax_S L0)); [destruct Hin' | discriminate]. }
    destruct HJL as (HM2 & Htp2 & Hkept2 & Hk2).
    assert (Hsub : forall a, cmaddrA Ai None a -> cmaddrA Ai None a) by (intros a H; exact H).
    split.
    * split; [split; [exact (KEPT_stepA Ai Ai None rho rhoL _ s R _ _ _ HM HRok Hsub Hkept2)|]|split].
      -- intros o' oR Hin' _. exfalso. exact (NONEW o' Hin').
      --
         intros r a j oR Hr Ha Hj HoR Hrng.
         unfold xs_framed in Hxf. pose proof (proj1 (forallb_forall _ _) Hxf r Hr) as Hrp. apply existsb_exists in Hrp as (rp & HinP & Heqr).
         apply xr_eqb_sound in Heqr. subst rp.
         pose proof Hsm as (HsmS & _ & HwfC & HshC & _).
         assert (HXcov : forallb (fun r0 => xr_covered (ss_facts (ax_S Cl)) (ax_X Cl) (xr_subst s r0)) (ax_X Pre) = true /\ axwf Pre = true).
         { clear - He. rewrite entails_frA_ref_eq in He. unfold entails_frA_ref in He. destruct (entails_fr (ax_S Cl) (ax_S Pre) s); [|discriminate].
           match type of He with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
           apply andb_prop in Hc as [Hc Hwf]. apply andb_prop in Hc as [Hc _]. auto. }
         destruct HXcov as [HXcov HwfP].
         pose proof (xr_covered_sound rho (ss_facts (ax_S Cl)) (ss_objs (ax_S Cl)) (bv_unsigned (eval rho (ax_base Cl))) (ax_X Cl) (xr_subst s r)
                       HF (proj1 (forallb_forall _ _) HXcov r HinP) HshC) as Hok.
         unfold axwf in HwfP. apply andb_prop in HwfP as [HwfX _]. pose proof (proj1 (forallb_forall _ _) HwfX r HinP) as Hrb.
         unfold xr_below in Hrb. apply andb_prop in Hrb as [Hrb1 Hrb2].
         assert (EV : forall e, sv_below (ss_next (ax_S Pre)) e = true -> eval rhoL e = eval rho (sv_subst s e)).
         { intros e He0. rewrite <- (eval_agree_vals _ _ _ e Hag1 He0). rewrite <- eval_subst. apply eval_absorb. }
         destruct r as [b l]. cbn [fst snd] in Ha, Hrb1, Hrb2. rewrite (EV b Hrb1), (EV l Hrb2) in Ha.
         unfold xr_ok, xr_subst in Hok. cbn [fst snd] in Hok. rewrite <- !eval_subst in Hok || idtac.
         destruct Hok as (_ & _ & Hok). destruct (Hok a ltac:(rewrite !eval_subst; rewrite !eval_subst in Ha || idtac; exact Ha)) as (_ & _ & Hwd & _).
         destruct (Hwd j Hj) as [Hout _].
         rewrite HbL in Hrng. rewrite HbC in Hout. cbn [eval] in Hrng, Hout.
         exact (proj1 (Forall_forall _ _) Hout oR (proj2 (proj2 (proj2 (proj2 (entails_frA_sound segs Cl Pre s R rho tp tr ms md He Hsm)))) oR HoR) Hrng).
      -- eapply (caller_X_kept Ai Ai None rho tp md R (vms md tp ms) s rhoL Cl); eauto.
         all: try (eapply xrs_range; eauto). all: intros o' Hin'; exfalso; exact (NONEW o' Hin').
    * intros rho' Hlink.
      eapply TR_pre; [ | apply (Tcont L0 (rho_patch rho' (patchf rho rho' R)) tpL HinL)].
      intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
      destruct HJ' as (HM3 & Htp3 & Hkept3 & Hk3).
      destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
      split; [exact (cont_smatchA Cl Pre _ s R rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
      exists Ai, kc.
      destruct (law_budget _ _ _ ALA Ai _ _ _ HM3) as (_ & _ & HV0 & HKm0 & HKf0).
      assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
      { eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch]. }
      pose proof Hnb as Hnb0. destruct (nd_below_split _ _ Hnb) as (Hbt & _ & _ & _).
      eapply (cont_JAi Cl Pre L0 s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc Ai None
                _ bd' (SLit 0) 0 He Hsm Hnf Hnb0 Hbb HJ HRok Hlink HM3 Hk3 Hsub); try assumption; try reflexivity.
      -- pose proof (uval_range rho (SLit 0)). lia.
      -- lia.
      -- cbn zeta. split; [|split].
         ++ apply (tvinA_agree FB Ai (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HN].
         ++ apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HD].
         ++ apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HZ].
      -- intros b m Hb _ _. exact Hb.
      -- chain_same_tv Hlink Hnb0.
      -- cen_same_tv Hlink Hnb0 (eq_refl (aa_live Ai)).
      -- capN_same_tac HCNi Hlink Hnb0 (eq_refl (aa_live Ai)).
Qed.

Theorem purec_callT : ltac2:(tb__ "0|3|
S34SbS34A1S34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80SbS6fA1S9eS3bS1cG1VTR;S62Vsegs;Se1VAInv;R3VKc;A3RdR2R1A5S9aVsegs;S113R2R1S127S34SdS34S96A2S34SeS34S96R1Sd7VAInv;VCST;VXGL;R4VKc;A5A4LL;RcA4A5A2Ftp1;Frho1;FAi;S3S1S1dS35RbA1A1S113A3S3S1bS36RcA1S23S114A1A3S3S10G0A1S97RbRdRaA3S12G0R9A2A3S3SaS98RcReRbRaRdA5ScA3S3SaSa3RcA1ScA3S3SaSf8VNP;S1dS35ReA1A1A2ScA3S3SaS82S1dS35RfA1A1RaA2ScA3S3SaS70S1dS35R10A1A1RaA2ScA3S11bS21S35R11A1A1S23Z0M2A1G2S81RcA1RbA5S3SaS5aS34S34S19S19G0SaLx;S10bS35R15A1S35R1A1A2ScS1eG0S11Ll;Ls0;Xbx2S9cR15R1A2A2S27S36R1A1S36R15A1A2A2LL;R13A3ScA3S11eR13R12R11R10ReS13S0A1S3bS7bS8Lms;LAi;A7S34S1cG1S58S34R3R18A3VTR;S62Vsegs;VJA;S7eS7cR13A1S7dR13A1R12S7fR13A1A4A1Sa2R1aR18R17R16R4A5R3R2A5R11A2F_;Ftp';Frho';FL;VTR;S62Vsegs;VJA;R10A1R15R12R11A5ReA2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;FLs;FPre;").
Proof using ALA HCST HXGL HKc TR_callP TR_ex TR_facts TR_pre.
  intros Pre Ls Cl s R rho tp nd bd' Q CALLEE. intros.
  eapply (purec_callT_xp (fun _ _ => True)); eauto.
  intros Ai rho1 tp1. eapply TR_pre; [|apply CALLEE]. intros w [Hsm [HJ _]]. exact (conj Hsm HJ).
Qed.

Lemma new_frame_free : ltac2:(tb__ "0|4|
S3bS3bS1cSbS5fQ40A1A1S6cSbSdS0S0A2M0A1M1G1S0S0S0VAInv;R9R8R7R6A4S3G1S3cRaA1S3cRbA1A3S3G1S3fRcA1M2S17G0R7R6A3A3S3G1G2S17G0R8SfG0SeS0S0R6R5A4R7A3A3A3S3S44S3dRdA1S3dReA1M3A3S6S4S4bR8R6A2S4dR6S4cR8R7A2A2A2S3S0R6ScfG3SeS0S0R8R7A4A2A3A2SfbR10S13S0A1R7A3S9F_;F_;F_;F_;F_;F_;F_;Fa;Fsz;Fp;Fl2;Fl1;Fmd;Ftp;Frho;FA2;FAi;").
Proof using ALA HCST.
  intros Ai A2 rho tp md l1 l2 p sz a HM2 HL2 HLi HF2 HG2 Ha Hc.
  destruct (law_blocks _ _ _ ALA A2 _ _ _ HM2) as (HPD & HBl & HFr).
  assert (HinNew : In (p, sz) (aa_frames A2)) by (rewrite HF2; apply in_or_app; right; left; reflexivity).
  destruct (HFr p sz HinNew) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9). top_rng F5.
  destruct Hc as [Hs|[Hs|[(b & m & Hb & _ & Hr)|(f & s' & Hf & Hr)]]].
  - rewrite <- HG2 in Hs. lia.
  - hcst Hs. unfold IMG_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia.
  - rewrite <- HL2 in Hb. destruct Ha as [Ha| ->].
    + assert (Hx : nth_error (aa_live A2 ++ aa_frames A2) (length (aa_live A2) + length l1) = Some (p, sz)).
      { rewrite nth_error_app2 by lia. replace (length (aa_live A2) + length l1 - length (aa_live A2))%nat with (length l1) by lia.
        rewrite HF2, nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
      apply In_nth_error in Hb as [k Hk].
      assert (Hy : nth_error (aa_live A2 ++ aa_frames A2) k = Some (b, m)).
      { rewrite nth_error_app1; [exact Hk | apply nth_error_Some; congruence]. }
      assert (Hk2 : (k < length (aa_live A2))%nat) by (apply nth_error_Some; congruence).
      pose proof (pd_elems _ _ _ _ _ HPD Hx Hy ltac:(lia)) as D. cbn [fst snd] in D. lia.
    + destruct (F8 b m Hb); lia.
  - assert (Hf2 : In (f, s') (l1 ++ l2)) by (rewrite <- HLi; exact Hf). destruct Ha as [Ha| ->].
    + pose proof (pd_mid2 (aa_live A2) l1 (p, sz) l2 (f, s') ltac:(rewrite <- HF2; exact HPD) ltac:(apply in_or_app; right; exact Hf2)) as D.
      cbn [fst snd] in D. lia.
    + destruct (F9 f s' ltac:(rewrite HF2; apply in_app_mid; exact Hf2)); lia.
Qed.

Lemma fs_frame_size_bounds : ltac2:(tb__ "0|1|
S0S4S4bZ0R1A2S4bR1Z6A2A2S4S4bZ40S117R2A1M0A2S4bG0Z1000A2A2F_;Fc;").
Proof using .
  clear. intros c Hc.
  assert (X : c = 0 \/ c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6) by lia.
  unfold fs_frame_size. rewrite Z.shiftl_mul_pow2 by lia.
  destruct X as [->|[->|[->|[->|[->|[->| ->]]]]]]; lia.
Qed.

Theorem smalloc_callT : ltac2:(tb__ "0|8|
S0S34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80S1S1S9eS3bS1cG1VTR;S62Vsegs;Sf1VAInv;RdR3VKc;A4Sc0VE;RdA2M2R2R1A5S9aVsegs;S113R2R1SfSdS34S96A2M3SeS34S96Sc4VE;RdA2M4SecVAInv;VCST;VXGL;RdR3VKc;A6A4S16G3A1A3A5A2Ftp1;Frho1;FAi;S4S4bZ0RbA2S4bRbZ6A2A2S3S10G0A1S97RbSc0VE;RcA2RaA3S12G0R9A2A3S3SaS98RcG2RbRaSfS34G4S16S34A1A3A5ScA3S3SaSa3RcA1ScA3S3SaSf8VNP;S1dS35ReA1A1A2ScA3S3SaS82S1dS35RfA1A1RaA2ScA3S3SaS74S81RbA1A1ScA3S3S1bS66S99R10Sc0VE;R12A2Sc4VE;R12A2R11A4Sc3A2S20RbA1A3S3SaSf8S1dS35R12A1A1RcA2ScA3S3S1bS66S99R12Sc0VE;R14A2Sc4VE;R14A2R13A4Sd9A2S20RcA1A3S3SaSf8S1dS35R14A1A1RdA2ScA3S3bS3bVPA;R2A1M5G5F_;FA';FA;S11eR16R15R14R13R11S13S0A1S3bS7bS4S4bS6eR15S66R17PcA2A2S117R19A1A2S12eS12dS11cR19S123A2S11cR19S127SdSdS1bS0A2M6S1bA2M7SdS0S0A2S8cR15A1S7dR13A1A4A2A2U8A2A2Lms;LAi;A7S1cG1VTR;S62Vsegs;VJA;S7eS7cR14A1SfG7SeG6S1bSeS1bS0S20R13A1R1aA4S20R12A1A4S7dR14A1A3S81R14A1S7fR14A1A4A1Sa2Sc0VE;R1aA2R19R18R17Sc4VE;R1aA2A5R2R1A5R11A2Ftp';Frho';VTR;S62Vsegs;VJA;R13A1R18R15R14A5R10A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;FpF;FpR;Fnd;Ftp;Frho;FR;Fs;FCl;Fc;").
Proof using ALA HCST HXGL HKc TR_callP TR_ex TR_facts TR_pre.
  intros c Cl s R rho tp nd pR pF Q CALLEE Hc6 He Hchk Htp Hnf Hnb Hwp HresR HpR HresF HpF HPAK HSITE Tcont.
  assert (Hc : 0 <= c) by lia. pose proof (fs_frame_size_bounds c Hc6) as Hszb.
  apply Pos.leb_le in Hnf. apply Pos.leb_le in HpR. apply Pos.leb_le in HpF.
  apply TR_facts. intros HF.
  apply (TR_ex AA (JAk nd)). intros Ai. apply (TR_ex Z (JAi nd Ai)). intros kc.
  set (sz := fs_frame_size c) in *. assert (Esz : sz = fs_frame_size c) by reflexivity.
  eapply (TR_callP (JAi nd Ai kc) (J_stack_malloc_pre AInv c Ai Kc) Cl (Pre_stack_malloc E c) s R
            [(L_stack_malloc E c, JL_stack_malloc AInv CST XGL c Ai Kc)] (ax_X Cl) Q rho tp (fun r H => H) He).
  - exact Hchk.
  - intros rho1 tp1. apply CALLEE.
  -
    intros tr ms md Hsm HJ. pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & Hsz & Hcnt).
    split; [eapply AInv_absorb; [exact HM | exact HRok]|]. split; [exact Hk|]. split; [eapply tp_of_TPA; eauto|].
    split; [pose proof (n_frames_bound Ai rho tp md (nd_fr nd) c Hc HM HFR); lia|].
    rewrite rw_call'. split; [exact Hsz | exact (top_of_TPA Ai s rho _ _ Hav HT Htp)].
  -
    intros L JL tr ms md rhoL tpL tr' ms' md' HinL Hsm HJ Hag1 HsmL HJL.
    pose proof HJ as (Hav & Hk & HM & HT & HB & HFF & (HN & HD & HZ) & HFR & HK0 & HP0 & HXA & HBU & HPA & HCKi & HCNi).
    destruct (HSITE Ai (vms md tp ms) HF HP0 Hav HB HFF HN HD HZ HFR (ex_intro _ rho (ex_intro _ tp (ex_intro _ md HM))) HT (T_of_chkA Ai s rho Hav HT Htp)) as (HRok & HX & Hsz & Hcnt).
    pose proof (entails_frA_base _ _ _ _ SHADOW_OFF He eq_refl) as HbC.
    cbn [In] in HinL. destruct HinL as [HinL | []]; injection HinL as HL HJLe; subst L JL.
    destruct HJL as (A2 & l1 & l2 & HM2 & HL2 & HLi & HF2 & HFL2 & HV2 & HKm2 & HKf2 & HG2 & Hkept2 & Hk2 & Htp2).
    set (p := bv_unsigned (rw rhoL V_RES)) in *. set (fl := bv_unsigned (rw rhoL V_FLAG)) in *. fold sz in HF2, HFL2.
    assert (HinNew : In (p, sz) (aa_frames A2)) by (rewrite HF2; apply in_or_app; right; left; reflexivity).
    assert (Hsub : forall a, cmaddrA Ai None a -> cmaddrA A2 None a).
    { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & s' & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
      - right; right; left. exists b, m. rewrite HL2. auto.
      - right; right; right. exists f, s'. rewrite HF2. split; [apply in_app_mid; rewrite <- HLi; exact Hin | exact Hr]. }
    destruct (law_blocks _ _ _ ALA A2 _ _ _ HM2) as (HPD & HBl & HFr).
    destruct (HFr p sz HinNew) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9). top_rng F5.
    rewrite HG2, <- HFL2 in F6, F7, F8, F9.

    assert (NEWR : forall o', In o' (new_objs (ax_S (Pre_stack_malloc E c)) (ax_S (L_stack_malloc E c))) ->
              forall a, fst (obj_range rhoL o') <= a < snd (obj_range rhoL o') -> p <= a < p + sz \/ a = fl).
    { intros o' Hin' a Ha. destruct (new_objs_not_pre _ _ _ Hin') as [A B0].
      cbn [ax_S L_stack_malloc Pre_stack_malloc mkA ss_objs app] in A, B0.
      destruct A as [A|[A|[A|[A|A]]]].
      - exfalso. apply B0. left. exact A.
      - subst o'. unfold obj_range, obj_lo_of, obj_hi_of, frame_obj in Ha. cbn [ob_base ob_lo ob_hi eval] in Ha.
        fold p in Ha. fold sz in Ha. rewrite !soff_lit_small in Ha by lia. cbn [fst snd] in Ha. left. lia.
      - subst o'. unfold obj_range, obj_lo_of, obj_hi_of, flag_obj in Ha. cbn [ob_base ob_lo ob_hi eval] in Ha.
        fold p in Ha. fold sz in Ha. rewrite !soff_lit_small in Ha by lia. cbn [fst snd] in Ha. left. lia.
      - subst o'. unfold obj_range, obj_lo_of, obj_hi_of, flagbyte_obj in Ha. cbn [ob_base ob_lo ob_hi eval] in Ha.
        fold fl in Ha. rewrite !soff_lit_small in Ha by lia. cbn [fst snd] in Ha. right. lia.
      - exfalso. apply B0. right. exact A. }
    split.
    + split; [split; [exact (KEPT_stepA Ai A2 None rho rhoL _ s R _ _ _ HM HRok Hsub Hkept2)|]|split].
      *
        intros o' oR Hin' HinR. apply ranges_disjoint_by_points. intros a Ha1 Ha2.
        apply (new_frame_free Ai A2 rhoL tpL md' l1 l2 p sz a HM2 HL2 HLi HF2 HG2).
        -- destruct (NEWR o' Hin' a Ha1) as [H| ->]; [left; exact H | right; rewrite HG2; exact HFL2].
        -- exact (HRok oR a HinR Ha2).
      *
        intros r a j oR Hr Ha Hj HoR. cbn [ax_X L_stack_malloc mkA] in Hr. destruct Hr as [<-|[]]. cbn [fst snd eval] in Ha. fold p in Ha.
        rewrite lit_unsigned in Ha. rewrite Z.mod_small in Ha by lia. fold sz in Ha.
        intros Hrng. apply (shadow_not_in_R Ai None rho tp md R (bv_unsigned (word_byte (bv_unsigned (eval rhoL (ax_base (L_stack_malloc E c))) + a / 8) j)) HM HRok).
        -- cbn [ax_base L_stack_malloc mkA base_sv eval]. rewrite lit_unsigned. change (SHADOW_OFF mod 2 ^ 64) with SHADOW_OFF.
           replace (SHADOW_OFF + a / 8) with (Sh a) by (unfold Sh; lia). apply word_byte_of_shadow; [apply Sh_is_shadow | exact Hj].
           unfold IMG_HI in F4, F6. lia.
        -- rewrite Z_to_bv_bv_unsigned. exists oR. split; [exact HoR | exact Hrng].
      * eapply (caller_X_kept Ai A2 None rho tp md R (vms md tp ms) s rhoL Cl); eauto.
        -- eapply xrs_range; eauto.
        --
           intros o' Hin' w Hw Hr. destruct (NEWR o' Hin' _ Hr) as [H|H]; apply (client_not_shadow A2 (bv_unsigned w) rhoL tpL md' HM2); [|exact Hw| |exact Hw];
             [left; right; right; left; exists p, sz; split; [exact HinNew | exact H] | right; exists (p, sz); split; [exact HinNew | rewrite HG2, <- HFL2; exact H]].
    +
      intros rho' Hlink.
      eapply TR_pre; [ | apply (Tcont (rho_patch rho' (patchf rho rho' R)) tpL)].
      intros w [Hsm' HJ']. cbn [J_ofPA] in HJ'.
      destruct HJ' as (A3 & k1 & k2 & HM3 & HL3 & HLi3 & HF3 & HFL3 & HV3 & HKm3 & HKf3 & HG3 & Hkept3 & Hk3 & Htp3).
      destruct w as [trw [msw mdw]]. cbn [w_tr w_cfg fst snd cfg_model] in *.
      split; [exact (cont_smatchA Cl (Pre_stack_malloc E c) _ s R rho rho' tp tpL tr ms md _ He Hsm (proj1 Hlink) Hsm')|].
      exists A3, kc.
      fold p in HF3, HFL3. fold sz in HF3, HFL3.
      assert (HinNew3 : In (p, sz) (aa_frames A3)) by (rewrite HF3; apply in_or_app; right; left; reflexivity).
      assert (Hsub' : forall a, cmaddrA Ai None a -> cmaddrA A3 None a).
      { intros a [H|[H|[(b & m & Hin & Hx & Hr)|(f & s' & Hin & Hr)]]]; [left; cm_stack H | right; left; exact H | |].
        - right; right; left. exists b, m. rewrite HL3. auto.
        - right; right; right. exists f, s'. rewrite HF3. split; [apply in_app_mid; rewrite <- HLi3; exact Hin | exact Hr]. }
      destruct (law_budget _ _ _ ALA A3 _ _ _ HM3) as (_ & _ & HV0 & HKm0 & HKf0).
      destruct (law_blocks _ _ _ ALA A3 _ _ _ HM3) as (HPD3 & HBl3 & HFr3).
      assert (Hag' : agree_vals (ss_next (ax_S Cl)) rho rho') by exact (proj1 Hlink).
      assert (HagP : agree_vals (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R))).
      { eapply agree_vals_trans; [exact Hag' | apply agree_vals_patch]. }
      assert (E1 : rw rho' pR = rw rhoL V_RES).
      { destruct Hlink as (_ & _ & _ & L4). specialize (L4 V_RES). change (ss_next (ax_S (Pre_stack_malloc E c))) with NF in L4.
        unfold import_subA in HresR. change (ss_next (ax_S (Pre_stack_malloc E c))) with NF in HresR.
        rewrite HresR in L4. cbn [eval] in L4. symmetry. apply L4; [reflexivity | cbv; lia]. }
      assert (E2 : rw rho' pF = rw rhoL V_FLAG).
      { destruct Hlink as (_ & _ & _ & L4). specialize (L4 V_FLAG). change (ss_next (ax_S (Pre_stack_malloc E c))) with NF in L4.
        unfold import_subA in HresF. change (ss_next (ax_S (Pre_stack_malloc E c))) with NF in HresF.
        rewrite HresF in L4. cbn [eval] in L4. symmetry. apply L4; [reflexivity | cbv; lia]. }
      assert (Enew : frv (rho_patch rho' (patchf rho rho' R)) (SVar pR, c, SVar pF) = (p, sz)).
      { unfold frv, uval. cbn [fst snd eval]. cbn [rho_patch rw]. rewrite E1. reflexivity. }
      assert (Efl : uval (rho_patch rho' (patchf rho rho' R)) (SVar pF) = fl).
      { unfold uval. cbn [eval rho_patch rw]. rewrite E2. reflexivity. }
      pose proof Hnb as Hnb0. destruct (nd_below_split _ _ Hnb) as (Hbt & Hbf & _ & _).
      assert (EMF : map (frv (rho_patch rho' (patchf rho rho' R))) (nd_fr nd) = map (frv rho) (nd_fr nd)).
      { eapply frv_map_agree; [exact HagP | exact Hbf]. }
      assert (HPAY : payA (ss_facts (ax_S Cl)) (SLit 0) 0 (nd_bd nd) (nd_bd nd)).
      { split; [exact Hwp|]. split; [lia|]. intros r _ _ _ Hnn. split; [unfold uval; rewrite U_lit; change (0 mod M64v) with 0; lia|]. split; [lia | exact Hnn]. }
      pose proof (HPAK Ai A3 HPA) as HPA2.
      eapply (cont_JAi_fr Cl (Pre_stack_malloc E c) (L_stack_malloc E c) s R rho tp tr ms md rhoL tpL trw mdw rho' nd Ai kc A3 None
                (nd_tv nd) _ (nd_bd nd) (SLit 0) 0 He Hsm Hnf Hnb0 (proj1 (proj2 (proj2 (nd_below_split _ _ Hnb0)))) HJ HRok Hlink HM3 Hk3
                (fun o a Ho Hr => Hsub' a (HRok o a Ho Hr))); try assumption.
      * intros b Hb. rewrite HL3. exact (HB b Hb).
      * intros f s' fl' Hin. rewrite HF3. apply in_app_mid. rewrite <- HLi3. exact (proj1 (HFF f s' fl' Hin)).
      * rewrite HV3. unfold uval. rewrite U_lit. change (0 mod M64v) with 0. lia.
      * rewrite HKm3, HKf3. lia.
      * cbn zeta. split; [|split].
        -- apply (tvinA_agree FB A3 (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt |].
           unfold tvinA in HN |- *. apply Forall_forall. intros t Ht Hnz.
           destruct (proj1 (Forall_forall _ _) HN t Ht Hnz) as (X0 & X1 & X2). split; [exact X0|]. split; [rewrite HL3; exact X1 | exact X2].
        -- apply (tvd_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HD].
        -- apply (tvz_agree (ss_next (ax_S Cl)) rho); [exact HagP | exact Hbt | exact HZ].
      *
        destruct HFR as (HFR0 & HCEN & HND). split; [|split].
        -- constructor.
           ++ cbn [snd]. rewrite Enew, Efl. split; [exact HinNew3|]. split; [rewrite HG3; unfold fl; exact HFL3|].
              intros [[y1 y2] y3] Hy Ey. cbn [fst] in Ey. destruct (HFF _ _ _ Hy) as [HyA _]. subst y1.
              rewrite HLi3 in HyA.
              pose proof (pd_mid2 (aa_live A3) k1 (p, sz) k2 (p, y2) ltac:(rewrite <- HF3; exact HPD3) ltac:(apply in_or_app; right; exact HyA)) as D.
              cbn [fst snd] in D. destruct (HFr3 p y2 ltac:(rewrite HF3; apply in_app_mid; exact HyA)) as (_ & _ & G64 & _). lia.
           ++ unfold frinA0 in HFR0 |- *. apply Forall_forall. intros x Hx. pose proof (proj1 (Forall_forall _ _) HFR0 x Hx) as (Y1 & Y2 & Y3).
              destruct (frv_agree (ss_next (ax_S Cl)) rho (rho_patch rho' (patchf rho rho' R)) x HagP (proj1 (forallb_forall _ _) Hbf x Hx)) as [EA EB].
              rewrite EA, EB. split; [rewrite HF3; apply in_app_mid; rewrite <- HLi3; exact Y1|]. split; [rewrite HG3; exact Y2 | exact Y3].
        -- intros x Hx. cbn [map]. rewrite Enew, EMF. rewrite HF3 in Hx. apply in_mid_cases in Hx as [->|Hx]; [right; left; reflexivity|].
           rewrite <- HLi3 in Hx. destruct (HCEN x Hx) as [H|H]; [left; exact H | right; right; exact H].
        -- cbn [map]. rewrite Enew, EMF. constructor; [|exact HND].
           intros Hin. unfold frinA0 in HFR0. apply in_map_iff in Hin as (x & Ex & Hx).
           pose proof (proj1 (Forall_forall _ _) HFR0 x Hx) as (Y1 & _ & _). rewrite Ex in Y1. rewrite HLi3 in Y1.
           pose proof (pd_mid2 (aa_live A3) k1 (p, sz) k2 (p, sz) ltac:(rewrite <- HF3; exact HPD3) ltac:(apply in_or_app; right; exact Y1)) as D.
           cbn [fst snd] in D. lia.
      * intros b m Hb _ _. rewrite HL3. exact Hb.
      * chain_same_tv Hlink Hnb.
      * cen_same_tv Hlink Hnb HL3.
      * capK_same_tac HCKi HL3 HV3.
      * capN_same_tac HCNi Hlink Hnb HL3.
Qed.

End CallT.

Let TRs (ok : world -> Prop) : assn -> assn -> Prop := triple segs ok.
Let TRe : assn -> assn -> Prop := etriple segs.
Lemma TRs_facts : ltac2:(tb__ "0|1|
Sa1OF_;S64S34S1cSbS5fQ40A1A1S9eS126S22S26R3A1S21S35R4A1A1A3VTRs;R7S62Vsegs;R6R5R4R3A5R2A3M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;Fok;").
Proof using . intros ok. exact (triple_factsA segs ok). Qed.
Lemma TRs_ex : forall ok (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TRs ok (SPA segs (J x) S rho tp) Q) -> TRs ok (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Proof using . intros ok. exact (triple_SPA_ex segs ok). Qed.
Lemma TRs_pre : ltac2:(tb__ "0|0|
Sa1OF_;S9eS9eS9eSa1R3R1A1R5R2A1F_;Fw;VTRs;R5R4R2A3VTRs;R6R4R3A3F_;F_;FQ;FP';FP;Fok;").
Proof using segs. intros ok P P' Q HP H. eapply triple_conseq; [exact HP | intros w Hw; exact Hw | exact H]. Qed.
Lemma TRe_facts : ltac2:(tb__ "0|1|
S64S34S1cSbS5fQ40A1A1S9eS126S22S26R3A1S21S35R4A1A1A3VTRe;S62Vsegs;R6R5R4R3A5R2A2M0F_;G0F_;FQ;Ftp;Frho;FS;FJ;").
Proof using . exact (etriple_factsA segs). Qed.
Lemma TRe_ex : forall (T : Type) (J : T -> jpredA) S rho tp (Q : assn),
  (forall x, TRe (SPA segs (J x) S rho tp) Q) -> TRe (SPA segs (fun r p t m => exists x, J x r p t m) S rho tp) Q.
Proof using . exact (etriple_SPA_ex segs). Qed.
Lemma TRe_pre : ltac2:(tb__ "0|0|
S9eS9eS9eSa1R3R1A1R5R2A1F_;Fw;VTRe;R4R2A2VTRe;R4R3A2F_;F_;FQ;FP';FP;").
Proof using segs. intros P P' Q HP H. eapply etriple_conseq; [exact HP | intros w Hw; exact Hw | exact H]. Qed.

Lemma TRe_pureP : ltac2:(tb__ "0|1|
S9eOS9eSa1R4R1A1R4F_;Fw;R3VTRe;R5R3A2M0F_;G0F_;F_;FQ;FX;FP;").
Proof using . clear. intros P X Q HX H w Hw. exact (H (HX w Hw) w Hw). Qed.
Lemma TRs_pureP : ltac2:(tb__ "0|1|
Sa1OF_;S9eOS9eSa1R4R1A1R4F_;Fw;R3VTRs;R6R5R3A3M0F_;G0F_;F_;FQ;FX;FP;Fok;").
Proof using . clear. intros ok P X Q HX H n Hg w Hw. exact (H (HX w Hw) n Hg w Hw). Qed.

Ltac by_callT_safety ok lem :=
  apply (lem (triple segs ok) (TRs_facts ok) (TRs_ex ok) (TRs_pre ok) (call_soundPA3 segs ok)).
Ltac by_callT_ex lem :=
  apply (lem (etriple segs) TRe_facts TRe_ex TRe_pre (call_completePA3 segs)).

Lemma ok_frameA_of_K : ltac2:(tb__ "0|0|
Sa1OF_;S64S88Vsegs;VKc;R2A3S1cSbS5fQ40A1A1SbS6dA1S6cR6R4R3R2R1A4VKc;R3R2A2F_;Fmd;Ftr;Ftp;Frho;S65Vsegs;R4R3A3F_;F_;FJ;Fok;").
Proof using .
  intros ok J H HJ rho tp tr ms md msv' Hj HMI Hh Hp Hs. eapply (proj1 H rho tp tr ms md msv'); eauto. exact (HJ _ _ _ _ Hj).
Qed.

Theorem malloc_callA : ltac2:(tb__ "0|5|
Sa1OF_;SbSbcA1SbbS34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80SbS6fA1S9eSdcRaR9A2S88Vsegs;VKc;RcA3Sd0Vsegs;VE;VAInv;VCST;VXGL;A5S3S10G0A1S97RbSbaVE;RdRcA3RaA3S12G0R9A2A3S3SaS98RcSbaVE;ReRdA3RbRaSfS34Sc2VE;ReRdA3SfS34SbeVE;ReRdA3S16S34A1A3A3A5ScA3S3SaSa3RcA1ScA3S3SaSf8VNP;S1dS35ReA1A1A2ScA3S3SaS82S1dS35RfA1A1RaA2ScA3S3SaS70S1dS35R10A1A1RaA2ScA3S3SaS28S1dS35R11A1A1S66R10PcM2A2A2ScA3S3S1bS66S99R11SbaVE;R14R13A3SbeVE;R14R13A3R12A4Sc3A2S20S109S1dS35R12A1A1UaM3A2A1A3Sa5S21S35R13A1A1S66R12G2A2S71S81ReA1RdA5S3bS3bVPA;R2A1S42R3R2S6eR14S66R16G2A2A2M4A3VPA;R3A1F_;F_;FA';FA;Sa4R15R14R13R12R10S13S0A1S3bS7bS4S4S4bZ1G4A2S4dG4S4eZ2Z27A2A2A2SbfR19R18S69S68R14R15R1A3R16A2A3A2Lms;LAi;A7S1cG1S9fVsegs;R1bS62Vsegs;VJA;S7eS7cR13A1S7dR13A1R12S7fR13A1A4A1Sa2SbaVE;R1aR19A3R18R17R16Sc2VE;R1aR19A3A5R2R1A5R11A4Ftp';Frho';S1cG1S9fVsegs;R1cS62Vsegs;VJA;S7eSfSdS1bS1bA2SeS1bS1bS20S109S1dS35R19A1A1G3A2A1S66R18G2A2A4S7cR14A1A3S7dR14A1R13S7fR14A1A4A1Sa2SbaVE;R1bR1aA3R19R18R17SbeVE;R1bR1aA3A5R2R1A5R12A4Ftp';Frho';S9fVsegs;R1bS62Vsegs;VJA;R13A1R18R15R14A5R11A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;Fok;").
Proof using ALA HCST HXGL HKc HBX.
  intros ok W st Cl s R rho tp nd bd' Q HW Hok AC. by_callT_safety ok malloc_callT.
  intros Ai rho1 tp1. apply (aca_malloc _ _ _ _ _ AC); [exact HW | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
Qed.

Theorem malloc_callA_ex : ltac2:(tb__ "0|5|
SbSbcA1SbbS34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80SbS6fA1S9eSdcRaR9A2Sd3Vsegs;VE;VAInv;VCST;VXGL;A5S3S10G0A1S97RaSbaVE;RcRbA3R9A3S12G0R8A2A3S3SaS98RbSbaVE;RdRcA3RaR9SfS34Sc2VE;RdRcA3SfS34SbeVE;RdRcA3S16S34A1A3A3A5ScA3S3SaSa3RbA1ScA3S3SaSf8VNP;S1dS35RdA1A1A2ScA3S3SaS82S1dS35ReA1A1R9A2ScA3S3SaS70S1dS35RfA1A1R9A2ScA3S3SaS28S1dS35R10A1A1S66RfPcM2A2A2ScA3S3S1bS66S99R10SbaVE;R13R12A3SbeVE;R13R12A3R11A4Sc3A2S20S109S1dS35R11A1A1UaM3A2A1A3Sa5S21S35R12A1A1S66R11G2A2S71S81RdA1RcA5S3bS3bVPA;R2A1S42R3R2S6eR13S66R15G2A2A2M4A3VPA;R3A1F_;F_;FA';FA;Sa4R14R13R12R11RfS13S0A1S3bS7bS4S4S4bZ1G4A2S4dG4S4eZ2Z27A2A2A2SbfR18R17S69S68R13R14R1A3R15A2A3A2Lms;LAi;A7S1cG1Sa0Vsegs;S62Vsegs;VJA;S7eS7cR12A1S7dR12A1R11S7fR12A1A4A1Sa2SbaVE;R19R18A3R17R16R15Sc2VE;R19R18A3A5R2R1A5R10A3Ftp';Frho';S1cG1Sa0Vsegs;S62Vsegs;VJA;S7eSfSdS1bS1bA2SeS1bS1bS20S109S1dS35R18A1A1G3A2A1S66R17G2A2A4S7cR13A1A3S7dR13A1R12S7fR13A1A4A1Sa2SbaVE;R1aR19A3R18R17R16SbeVE;R1aR19A3A5R2R1A5R11A3Ftp';Frho';Sa0Vsegs;S62Vsegs;VJA;R12A1R17R14R13A5R10A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;").
Proof using ALA HCST HXGL HKc HBX.
  intros W st Cl s R rho tp nd bd' Q HW ACX. by_callT_ex malloc_callT.
  intros Ai rho1 tp1. apply (acx_malloc _ _ _ _ _ ACX); [exact HW | exact HKc].
Qed.

Theorem malloc_callA_tr : ltac2:(tb__ "0|5|
S3bOF_;Sa1OF_;SbSbcA1SbbS34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80SbS6fA1S9eSdcRaR9A2S88Vsegs;VKc;RcA3Sd0Vsegs;VE;VAInv;VCST;VXGL;A5S3S10G0A1S97RbSbaVE;RdRcA3RaA3S12G0R9A2A3S3SaS98RcSbaVE;ReRdA3RbRaSfS34Sc2VE;ReRdA3SfS34SbeVE;ReRdA3S16S34A1A3A3A5ScA3S3SaSa3RcA1ScA3S3SaSf8VNP;S1dS35ReA1A1A2ScA3S3SaS82S1dS35RfA1A1RaA2ScA3S3SaS70S1dS35R10A1A1RaA2ScA3S3SaS28S1dS35R11A1A1S66R10PcM2A2A2ScA3S3S1bS66S99R11SbaVE;R14R13A3SbeVE;R14R13A3R12A4Sc3A2S20S109S1dS35R12A1A1UaM3A2A1A3Sa5S21S35R13A1A1S66R12G2A2S71S81ReA1RdA5S3bS3bVPA;R2A1S42R3R2S6eR14S66R16G2A2A2M4A3R1cR3A1F_;F_;FA';FA;Sa4R15R14R13R12R10S13S0A1S3bS7bS4S4S4bZ1G4A2S4dG4S4eZ2Z27A2A2A2SbfR19R18S69S68R14R15R1A3R16A2A3A2Lms;LAi;A7S1cG1S9fVsegs;R1bS62Vsegs;S87VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;R1cS7eS7cR13A1S7dR13A1R12S7fR13A1A4AcSa2SbaVE;R1aR19A3R18R17R16Sc2VE;R1aR19A3A5R2R1A5R11A4Ftp';Frho';S1cG1S9fVsegs;R1cS62Vsegs;S87VAInv;VCST;VXGL;VNP;VKc;Vrho0;VP0f;VFB;VFF;VBX;R1dS7eSfSdS1bS1bA2SeS1bS1bS20S109S1dS35R19A1A1G3A2A1S66R18G2A2A4S7cR14A1A3S7dR14A1R13S7fR14A1A4AcSa2SbaVE;R1bR1aA3R19R18R17SbeVE;R1bR1aA3A5R2R1A5R12A4Ftp';Frho';S9fVsegs;R1bS62Vsegs;VJA;R13A1R18R15R14A5R11A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;Fok;FPA';").
Proof using ALA HCST HXGL HKc HBX.
  intros PA' ok W st Cl s R rho tp nd bd' Q HW Hok AC He Hchk Htp Hnf Hnb Hbb Hs12 Hres HPAY HPAK HSITE Tnull Tok.
  apply (malloc_callT_gen (triple segs ok) (TRs_facts ok) (TRs_ex ok) (TRs_pre ok) (call_soundPA3 segs ok) true true (fun _ _ => True) PA'
           W st Cl s R rho tp nd bd' Q); try assumption.
  - intros Ai rho1 tp1.
    apply (TRs_pre ok (SPA segs (J_alloc_pre AInv W st Ai Kc (SVar 12)) (Pre_malloc E W st) rho1 tp1)); [intros w [Hsm [HJ _]]; exact (conj Hsm HJ)|].
    apply (aca_malloc _ _ _ _ _ AC); [exact HW | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
  - intros A ms _ _ _ _. exact I.
  - intros _. exact Tnull.
  - intros _. exact Tok.
Qed.

Theorem calloc_callA : ltac2:(tb__ "0|4|
Sa1OF_;SbSbcA1SbbS34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80SbS6fA1S9eSe7RaR9A2S88Vsegs;VKc;RcA3Sd0Vsegs;VE;VAInv;VCST;VXGL;A5S3S10G0A1S97RbSbdVE;RdRcA3RaA3S12G0R9A2A3S3SaS98RcSbdVE;ReRdA3RbRaSfS34Sc5VE;ReRdA3SfS34Sc1VE;ReRdA3S16S34A1A3A3A5ScA3S3SaSa3RcA1ScA3S3SaSf8VNP;S1dS35ReA1A1A2ScA3S3SaS82S1dS35RfA1A1RaA2ScA3S3SaS70S1dS35R10A1A1RaA2ScA3S3SaS28S1dS35R11A1A1Sa7R10A1A2ScA3S3S1bS66S99R11SbdVE;R14R13A3Sc1VE;R14R13A3R12A4Sc3A2S20S109S1dS35R12A1A1UaM2A2A1A3Sa5S21S35R13A1A1Sa7R12A1S71S81ReA1RdA5S3bS3bVPA;R2A1S42R3R2S6eR14Sa7R16A1A2M3A3VPA;R3A1F_;F_;FA';FA;Sa4R15R14R13R12R10S13S0A1S3bS7bS4S4S4bZ1G3A2S4dG3S4eZ2Z27A2A2A2S4S3S0S50S6eR14S66R16PcA2A2S6eR14S66R16PdA2A2A2G3A3SbfR19R18S69S68R14R15R1A3R16A2A3A2A2Lms;LAi;A7S1cG1S9fVsegs;R1bS62Vsegs;VJA;S7eS7cR13A1S7dR13A1R12S7fR13A1A4A1Sa2SbdVE;R1aR19A3R18R17R16Sc5VE;R1aR19A3A5R2R1A5R11A4Ftp';Frho';S1cG1S9fVsegs;R1cS62Vsegs;VJA;S7eSfSdS1bS1bA2SeS1bS1bS20S109S1dS35R19A1A1G2A2A1Sa7R18A1A4S7cR14A1A3S7dR14A1R13S7fR14A1A4A1Sa2SbdVE;R1bR1aA3R19R18R17Sc1VE;R1bR1aA3A5R2R1A5R12A4Ftp';Frho';S9fVsegs;R1bS62Vsegs;VJA;R13A1R18R15R14A5R11A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;Fok;").
Proof using ALA HCST HXGL HKc HBX.
  intros ok W st Cl s R rho tp nd bd' Q HW Hok AC. by_callT_safety ok calloc_callT.
  intros Ai rho1 tp1. apply (aca_calloc _ _ _ _ _ AC); [exact HW | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
Qed.

Theorem calloc_callA_ex : ltac2:(tb__ "0|4|
SbSbcA1SbbS34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80SbS6fA1S9eSe7RaR9A2Sd3Vsegs;VE;VAInv;VCST;VXGL;A5S3S10G0A1S97RaSbdVE;RcRbA3R9A3S12G0R8A2A3S3SaS98RbSbdVE;RdRcA3RaR9SfS34Sc5VE;RdRcA3SfS34Sc1VE;RdRcA3S16S34A1A3A3A5ScA3S3SaSa3RbA1ScA3S3SaSf8VNP;S1dS35RdA1A1A2ScA3S3SaS82S1dS35ReA1A1R9A2ScA3S3SaS70S1dS35RfA1A1R9A2ScA3S3SaS28S1dS35R10A1A1Sa7RfA1A2ScA3S3S1bS66S99R10SbdVE;R13R12A3Sc1VE;R13R12A3R11A4Sc3A2S20S109S1dS35R11A1A1UaM2A2A1A3Sa5S21S35R12A1A1Sa7R11A1S71S81RdA1RcA5S3bS3bVPA;R2A1S42R3R2S6eR13Sa7R15A1A2M3A3VPA;R3A1F_;F_;FA';FA;Sa4R14R13R12R11RfS13S0A1S3bS7bS4S4S4bZ1G3A2S4dG3S4eZ2Z27A2A2A2S4S3S0S50S6eR13S66R15PcA2A2S6eR13S66R15PdA2A2A2G3A3SbfR18R17S69S68R13R14R1A3R15A2A3A2A2Lms;LAi;A7S1cG1Sa0Vsegs;S62Vsegs;VJA;S7eS7cR12A1S7dR12A1R11S7fR12A1A4A1Sa2SbdVE;R19R18A3R17R16R15Sc5VE;R19R18A3A5R2R1A5R10A3Ftp';Frho';S1cG1Sa0Vsegs;S62Vsegs;VJA;S7eSfSdS1bS1bA2SeS1bS1bS20S109S1dS35R18A1A1G2A2A1Sa7R17A1A4S7cR13A1A3S7dR13A1R12S7fR13A1A4A1Sa2SbdVE;R1aR19A3R18R17R16Sc1VE;R1aR19A3A5R2R1A5R11A3Ftp';Frho';Sa0Vsegs;S62Vsegs;VJA;R12A1R17R14R13A5R10A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;").
Proof using ALA HCST HXGL HKc HBX.
  intros W st Cl s R rho tp nd bd' Q HW ACX. by_callT_ex calloc_callT.
  intros Ai rho1 tp1. apply (acx_calloc _ _ _ _ _ ACX); [exact HW | exact HKc].
Qed.

Theorem free_callA : ltac2:(tb__ "0|4|
Sa1OF_;SbSbcA1SbbS34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80S18SdS1bS1bA2M2SbS6fA1S9eSe8RcRbA2S88Vsegs;VKc;ReA3Sd0Vsegs;VE;VAInv;VCST;VXGL;A5S3S10G0A1S97RdSc7VE;RfReA3RcA3S12G0RbA2A3S3SaS98ReSc7VE;R10RfA3RdRcSfS34ScdVE;R10RfA3S16S34A1A3A5ScA3S3SaSa3ReA1ScA3S3SaSf8VNP;S1dS35R10A1A1A2ScA3S3SaS82S1dS35R11A1A1RcA2ScA3S3SaS70S1dS35R12A1A1RaA2ScA3S3S10G2A1S59G2S7cReA1RdA3S12G2RcA2A3Sa5S21S35R14A1A1S23Z0A1S71S81RfA1RcA5S3bS3bVPA;R2A1S45R3R2A2VPA;R3A1F_;F_;FA';FA;Sa4R16R15R14R13R11S12S0S6eR13S66R15PcM3A2A2A2S3bS7bS4S102R15R11A2S4S3SdS0S0A2S100R15R11A2SeS0S0S6eR15S66R17G3A2A2S6eR15S66R17PdA2A2A4A3SbfR1aR19S69S68R15R16R1A3R17A2A3A2A2Lms;LAi;A7S1cG1S9fVsegs;R1cS62Vsegs;VJA;S7eS101G2R13S7cR14A1A3S7dR14A1R11S7fR14A1A4A1Sa2Sc7VE;R1bR1aA3R19R18R17ScdVE;R1bR1aA3A5R2R1A5R10A4Ftp';Frho';S9fVsegs;R1bS62Vsegs;VJA;R13A1R18R15R14A5RfA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Ft;Fi;Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;Fok;").
Proof using ALA HCST HXGL HKc.
  intros ok W st Cl s R rho tp nd i t bd' Q HW Hok AC. by_callT_safety ok free_callT.
  intros Ai rho1 tp1. apply (aca_free _ _ _ _ _ AC); [exact HW | exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
Qed.

Theorem free_callA_ex : ltac2:(tb__ "0|4|
SbSbcA1SbbS34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80S18SdS1bS1bA2M2SbS6fA1S9eSe8RcRbA2Sd3Vsegs;VE;VAInv;VCST;VXGL;A5S3S10G0A1S97RcSc7VE;ReRdA3RbA3S12G0RaA2A3S3SaS98RdSc7VE;RfReA3RcRbSfS34ScdVE;RfReA3S16S34A1A3A5ScA3S3SaSa3RdA1ScA3S3SaSf8VNP;S1dS35RfA1A1A2ScA3S3SaS82S1dS35R10A1A1RbA2ScA3S3SaS70S1dS35R11A1A1R9A2ScA3S3S10G2A1S59G2S7cRdA1RcA3S12G2RbA2A3Sa5S21S35R13A1A1S23Z0A1S71S81ReA1RbA5S3bS3bVPA;R2A1S45R3R2A2VPA;R3A1F_;F_;FA';FA;Sa4R15R14R13R12R10S12S0S6eR12S66R14PcM3A2A2A2S3bS7bS4S102R14R10A2S4S3SdS0S0A2S100R14R10A2SeS0S0S6eR14S66R16G3A2A2S6eR14S66R16PdA2A2A4A3SbfR19R18S69S68R14R15R1A3R16A2A3A2A2Lms;LAi;A7S1cG1Sa0Vsegs;S62Vsegs;VJA;S7eS101G2R12S7cR13A1A3S7dR13A1R10S7fR13A1A4A1Sa2Sc7VE;R1aR19A3R18R17R16ScdVE;R1aR19A3A5R2R1A5RfA3Ftp';Frho';Sa0Vsegs;S62Vsegs;VJA;R12A1R17R14R13A5ReA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Ft;Fi;Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;").
Proof using ALA HCST HXGL HKc.
  intros W st Cl s R rho tp nd i t bd' Q HW ACX. by_callT_ex free_callT.
  intros Ai rho1 tp1. apply (acx_free _ _ _ _ _ ACX); [exact HW | exact HKc].
Qed.

Theorem free_null_callA : ltac2:(tb__ "0|5|
Sa1OF_;SbSbcA1M0SbbS34S67SbS1eA1M1S1cSbS5fQ40A1A1M2S80SbS6fA1S9eS3SdG0SbbA2SeG0SbbRaR9A4SeG0SbbS16SbcA1Se6A4A3S88Vsegs;VKc;RcA3Sd0Vsegs;VE;VAInv;VCST;VXGL;A5S3S10G1A1S97RbSc8VE;RdRcA3RaA3S12G1R9A2A3S3SaS98RcSc8VE;ReRdA3RbRaSfS34SceVE;ReRdA3S16S34A1A3A5ScA3S3SaSa3RcA1ScA3S3SaSf8VNP;S1dS35ReA1A1A2ScA3S3SaS82S1dS35RfA1A1RaA2ScA3S3SaS70S1dS35R10A1A1RaA2ScA3Sa5S21S35R11A1A1S23Z0M3A1G3S81RcA1RbA5S3bS3bVPA;R2A1M4G4F_;FA';FA;Sa4R13R12R11R10ReS13S0A1S3bS7bSbfR17R16S69S68R12R13R1A3R14A2A3Lms;LAi;A7S1cG2S9fVsegs;R19S62Vsegs;VJA;S7eS7cR11A1S7dR11A1R10S7fR11A1A4A1Sa2Sc8VE;R18R17A3R16R15R14SceVE;R18R17A3A5R2R1A5RfA4Ftp';Frho';S9fVsegs;R18S62Vsegs;VJA;R10A1R15R12R11A5ReA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;Fok;").
Proof using ALA HCST HXGL HKc.
  intros ok W st Cl s R rho tp nd bd' Q HW Hok AC. injection HW as -> ->. by_callT_safety ok free_null_callT.
  intros Ai rho1 tp1. apply (aca_free_null _ _ _ _ _ AC); [exact HKc| |]. exact (proj1 Hok). exact (proj2 Hok).
Qed.

Theorem free_null_callA_ex : ltac2:(tb__ "0|5|
SbSbcA1M0SbbS34S67SbS1eA1M1S1cSbS5fQ40A1A1M2S80SbS6fA1S9eS3SdG0SbbA2SeG0SbbRaR9A4SeG0SbbS16SbcA1Se6A4A3Sd3Vsegs;VE;VAInv;VCST;VXGL;A5S3S10G1A1S97RaSc8VE;RcRbA3R9A3S12G1R8A2A3S3SaS98RbSc8VE;RdRcA3RaR9SfS34SceVE;RdRcA3S16S34A1A3A5ScA3S3SaSa3RbA1ScA3S3SaSf8VNP;S1dS35RdA1A1A2ScA3S3SaS82S1dS35ReA1A1R9A2ScA3S3SaS70S1dS35RfA1A1R9A2ScA3Sa5S21S35R10A1A1S23Z0M3A1G3S81RbA1RaA5S3bS3bVPA;R2A1M4G4F_;FA';FA;Sa4R12R11R10RfRdS13S0A1S3bS7bSbfR16R15S69S68R11R12R1A3R13A2A3Lms;LAi;A7S1cG2Sa0Vsegs;S62Vsegs;VJA;S7eS7cR10A1S7dR10A1RfS7fR10A1A4A1Sa2Sc8VE;R17R16A3R15R14R13SceVE;R17R16A3A5R2R1A5ReA3Ftp';Frho';Sa0Vsegs;S62Vsegs;VJA;RfA1R14R11R10A5RdA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fst;FW;").
Proof using ALA HCST HXGL HKc.
  intros W st Cl s R rho tp nd bd' Q HW ACX. injection HW as -> ->. by_callT_ex free_null_callT.
  intros Ai rho1 tp1. apply (acx_free_null _ _ _ _ _ ACX). exact HKc.
Qed.

Definition XP_memset (Ai : AA) (r : valuation) : Prop := ltac2:(tb__ "0|1|
Sd4S60Q40M0S24Vr;P35A2A2S60G0S24Vr;P36A2A2A2").
Definition XP_memcpy (Ai : AA) (r : valuation) : Prop := ltac2:(tb__ "0|1|
S4Sd4S60Q40M0S24Vr;P35A2A2S60G0S24Vr;P36A2A2A2Sd4S60G0S24Vr;P37A2A2S60G0S24Vr;P38A2A2A2A2").

Ltac hfact HF f H := pose proof (proj1 (Forall_forall _ _) HF f ltac:(cbn; tauto)) as H; cbn [holds] in H.
Lemma memset_len_pos : ltac2:(tb__ "0|0|
S0S1cS126S22S26R1A1S21S35SccR2A1A1A1A3S4bZ1S60Q40S24R2P36A2A2A2F_;Fr;Fentry;").
Proof using .
  clear. intros entry r HF. cbn [ax_S Pre_memset mkA ss_facts] in HF. apply Forall_app in HF as [HF _]. unfold memset_facts in HF.
  hfact HF (SPUle (SVar 53) (SVar 12)) A1. hfact HF (SPUle (SAlu ALU_ADD (SVar 12) (SVar 14)) (SAlu ALU_ADD (SVar 53) (SVar 54))) A2.
  hfact HF (SPUle (SVar 14) (SLit (2 ^ 32))) A3. hfact HF (SPUle (SLit 1) (SVar 14)) A7.
  hfact HF (SPUle (SVar 53) (SLit (2 ^ 47 - 8))) A8. hfact HF (SPUle (SVar 12) (SLit (2 ^ 47))) A9. hfact HF (SPUle (SVar 54) (SLit (2 ^ 40))) A6.
  cbn [eval] in A1, A2, A3, A6, A7, A8, A9. rewrite !add_val in A2. rewrite !lit_unsigned in A3, A6, A7, A8, A9.
  pose proof (urange (rw r 53)). pose proof (urange (rw r 54)). pose proof (urange (rw r 12)). pose proof (urange (rw r 14)).
  rewrite !Z.mod_small in A3, A6, A7, A8, A9 by lia. rewrite !Z.mod_small in A2 by lia. lia.
Qed.
Lemma memcpy_len_pos : ltac2:(tb__ "0|2|
S0S1cS126S22S26R1A1S21S35ScbR2A1A1A1A3S4S4bZ1M0S60Q40M1S24R2P36A2A2A2S4bG0S60G1S24R2P38A2A2A2A2F_;Fr;Fentry;").
Proof using .
  clear. intros entry r HF. cbn [ax_S Pre_memcpy mkA ss_facts] in HF. apply Forall_app in HF as [HF _]. unfold memcpy_facts in HF.
  hfact HF (SPUle (SVar 53) (SVar 12)) A1. hfact HF (SPUle (SAlu ALU_ADD (SVar 12) (SVar 14)) (SAlu ALU_ADD (SVar 53) (SVar 54))) A2.
  hfact HF (SPUle (SVar 55) (SVar 13)) B1. hfact HF (SPUle (SAlu ALU_ADD (SVar 13) (SVar 14)) (SAlu ALU_ADD (SVar 55) (SVar 56))) B2.
  hfact HF (SPUle (SVar 14) (SLit (2 ^ 32))) A3. hfact HF (SPUle (SLit 1) (SVar 14)) A7.
  hfact HF (SPUle (SVar 53) (SLit (2 ^ 47 - 8))) A8. hfact HF (SPUle (SVar 12) (SLit (2 ^ 47))) A9. hfact HF (SPUle (SVar 54) (SLit (2 ^ 40))) A6.
  hfact HF (SPUle (SVar 55) (SLit (2 ^ 47 - 8))) B8. hfact HF (SPUle (SVar 13) (SLit (2 ^ 47))) B9. hfact HF (SPUle (SVar 56) (SLit (2 ^ 40))) B6.
  cbn [eval] in A1, A2, A3, A6, A7, A8, A9, B1, B2, B6, B8, B9. rewrite !add_val in A2, B2. rewrite !lit_unsigned in A3, A6, A7, A8, A9, B6, B8, B9.
  pose proof (urange (rw r 53)). pose proof (urange (rw r 54)). pose proof (urange (rw r 12)). pose proof (urange (rw r 14)).
  pose proof (urange (rw r 55)). pose proof (urange (rw r 56)). pose proof (urange (rw r 13)).
  rewrite !Z.mod_small in A3, A6, A7, A8, A9, B6, B8, B9 by lia. rewrite !Z.mod_small in A2, B2 by lia. lia.
Qed.

Lemma XP_memset_site : ltac2:(tb__ "0|2|
S3bS34S0S67SbS1eA1M0S1cSbS5fQ40A1A1SbS6dA1M1S7bS6cS63Vsegs;R5R4R9SeG1S110R3S111R2R1A2A4A5VAInv;RbR6R5R2A4Sa6RcS13S0A1R7S37RbA1A4S3S10G0A1S97RcSccRbA1RaA3S12G0R9A2A3Sb9ReS69S68R9RaS112R5R8R6A3A3RbA2A2F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;FR;Fs;Fentry;FCl;FAi;").
Proof using ALA HCST HXGL.
  intros Ai Cl entry s R rho tp tr ms md Hsm HM HX He. unfold XP_memset.
  destruct (entails_frA_sound segs Cl (Pre_memset entry) s R rho tp tr ms md He Hsm) as (HsmPre & _).
  pose proof (memset_len_pos entry _ (smatchA_facts segs _ _ _ _ HsmPre)) as Hlen. repeat rewrite rw_call' in Hlen. repeat rewrite rw_call'.
  exact (band_free_site Ai Cl (Pre_memset entry) s R rho tp tr ms md (SVar 53%positive, SVar 54%positive) Hsm HM HX He ltac:(left; reflexivity) Hlen).
Qed.
Lemma XP_memcpy_site : ltac2:(tb__ "0|2|
S3bS34S0S67SbS1eA1M0S1cSbS5fQ40A1A1SbS6dA1M1S7bS6cS63Vsegs;R5R4R9SeG1S110R3S111R2R1A2A4A5VAInv;RbR6R5R2A4Sa6RcS13S0A1R7S37RbA1A4S3S10G0A1S97RcScbRbA1RaA3S12G0R9A2A3Sb8ReS69S68R9RaS112R5R8R6A3A3RbA2A2F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;FR;Fs;Fentry;FCl;FAi;").
Proof using ALA HCST HXGL.
  intros Ai Cl entry s R rho tp tr ms md Hsm HM HX He. unfold XP_memcpy.
  destruct (entails_frA_sound segs Cl (Pre_memcpy entry) s R rho tp tr ms md He Hsm) as (HsmPre & _).
  pose proof (memcpy_len_pos entry _ (smatchA_facts segs _ _ _ _ HsmPre)) as [Hlen1 Hlen2]. repeat rewrite rw_call' in Hlen1. repeat rewrite rw_call' in Hlen2. repeat rewrite rw_call'.
  split.
  - exact (band_free_site Ai Cl (Pre_memcpy entry) s R rho tp tr ms md (SVar 53%positive, SVar 54%positive) Hsm HM HX He ltac:(left; reflexivity) Hlen1).
  - exact (band_free_site Ai Cl (Pre_memcpy entry) s R rho tp tr ms md (SVar 55%positive, SVar 56%positive) Hsm HM HX He ltac:(right; left; reflexivity) Hlen2).
Qed.

Theorem memset_callA : ltac2:(tb__ "0|3|
Sa1OF_;S0S0S34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80SbS6fA1S9eS88Vsegs;VKc;RbA3Sf5Vsegs;VAInv;VCST;VXGL;RbRaA6S3S10G0A1S97RaSccRcA1R9A3S12G0R8A2A3S3SaS98RbSccRdA1RaR9SfS34Sd2RcA1S16S34A1A3A5ScA3S3SaSa3RbA1ScA3S3SaSf8VNP;S1dS35RdA1A1A2ScA3S3SaS82S1dS35ReA1A1R9A2ScA3S3SaS70S1dS35RfA1A1R9A2ScA3Sa5S21S35R10A1A1S23Z0M2A1G2S81RbA1RaA5Sa4R11R10RfReRcS13S0A1S3bS7bS8Lms;LAi;A7S1cG1S9fVsegs;R17S62Vsegs;VJA;S7eS7cRfA1S7dRfA1ReS7fRfA1A4A1Sa2SccR16A1R14R13R12Sd2R15A1A5R2R1A5RdA4Ftp';Frho';S9fVsegs;R16S62Vsegs;VJA;ReA1R13R10RfA5RcA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fretpc;Fentry;Fok;").
Proof using ALA HCST HXGL HKc.
  intros ok entry retpc Cl s R rho tp nd bd' Q Hok MC He Hchk Htp Hnf Hnb Hbb HPAY HSITE Tcont.
  apply (purec_callT_xp (triple segs ok) (TRs_facts ok) (TRs_ex ok) (TRs_pre ok) (call_soundPA3 segs ok) XP_memset (Pre_memset entry) [L_memset retpc] Cl s R rho tp nd bd' Q);
    try assumption; try reflexivity.
  - intros Ai rho1 tp1. cbn [map]. apply MC; [exact HKc|]. apply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & X & _). exact X.
  - intros Ai tr ms md Hsm HM HX. exact (XP_memset_site Ai Cl entry s R rho tp tr ms md Hsm HM HX He).
  - intros L rho' tp' [<-|[]]. apply Tcont.
Qed.

Theorem memset_callA_ex : ltac2:(tb__ "0|4|
S0S0S34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80SbS6fA1S9eS3bSe2S1cG1Se3R3A1Sa0Vsegs;S62Vsegs;Sf0VAInv;R5R4A3SccRfA1R3R2A5S9aVsegs;S113R3R2SfSdS34S96A2M2SeS34S96Sd2ReA1Sd7VAInv;VCST;VXGL;R5R4A5A4S16G2A1A3A5A3F_;Ftp1;Frho1;FKc';FA;S3S10G0A1S97R9SccRbA1R8A3S12G0R7A2A3S3SaS98RaSccRcA1R9R8SfS34Sd2RbA1S16S34A1A3A5ScA3S3SaSa3RaA1ScA3S3SaSf8VNP;S1dS35RcA1A1A2ScA3S3SaS82S1dS35RdA1A1R8A2ScA3S3SaS70S1dS35ReA1A1R8A2ScA3Sa5S21S35RfA1A1S23Z0M3A1G3S81RaA1R9A5Sa4R10RfReRdRbS13S0A1S3bS7bS8Lms;LAi;A7S1cG1Sa0Vsegs;S62Vsegs;VJA;S7eS7cReA1S7dReA1RdS7fReA1A4A1Sa2SccR15A1R13R12R11Sd2R14A1A5R2R1A5RcA3Ftp';Frho';Sa0Vsegs;S62Vsegs;VJA;RdA1R12RfReA5RbA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fretpc;Fentry;").
Proof using ALA HCST HXGL HKc.
  intros entry retpc Cl s R rho tp nd bd' Q MCX He Hchk Htp Hnf Hnb Hbb HPAY HSITE Tcont.
  apply (purec_callT_xp (etriple segs) TRe_facts TRe_ex TRe_pre (call_completePA3 segs) XP_memset (Pre_memset entry) [L_memset retpc] Cl s R rho tp nd bd' Q);
    try assumption; try reflexivity.
  - intros Ai rho1 tp1. cbn [map]. apply MCX. exact HKc.
  - intros Ai tr ms md Hsm HM HX. exact (XP_memset_site Ai Cl entry s R rho tp tr ms md Hsm HM HX He).
  - intros L rho' tp' [<-|[]]. apply Tcont.
Qed.

Theorem memcpy_callA : ltac2:(tb__ "0|4|
Sa1OF_;S0S0S0S34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80SbS6fA1S9eS88Vsegs;VKc;RcA3Sf4Vsegs;VAInv;VCST;VXGL;RcRbRaA7S3S10G0A1S97RaScbRdA1R9A3S12G0R8A2A3S3SaS98RbScbReA1RaR9SfS34Sc6RdA1SfS34Sc6RcA1S16S34A1M2A3A3A5ScA3S3SaSa3RbA1ScA3S3SaSf8VNP;S1dS35RdA1A1A2ScA3S3SaS82S1dS35ReA1A1R9A2ScA3S3SaS70S1dS35RfA1A1R9A2ScA3Sa5S21S35R10A1A1S23Z0M3A1G3S81RbA1RaA5Sa4R11R10RfReRcS13S0A1S3bS7bS8Lms;LAi;A7S34S1cG1S58S34R3SfS34Sc6R17A1SfS34Sc6R16A1G2A3A3A3S9fVsegs;R1aS62Vsegs;VJA;S7eS7cR11A1S7dR11A1R10S7fR11A1A4A1Sa2ScbR19A1R16R15R14R4A5R3R2A5RfA4F_;Ftp';Frho';FL;S9fVsegs;R17S62Vsegs;VJA;ReA1R13R10RfA5RcA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fretpc2;Fretpc;Fentry;Fok;").
Proof using ALA HCST HXGL HKc.
  intros ok entry retpc retpc2 Cl s R rho tp nd bd' Q Hok MC He Hchk Htp Hnf Hnb Hbb HPAY HSITE Tcont.
  apply (purec_callT_xp (triple segs ok) (TRs_facts ok) (TRs_ex ok) (TRs_pre ok) (call_soundPA3 segs ok) XP_memcpy (Pre_memcpy entry) [L_memcpy retpc; L_memcpy retpc2] Cl s R rho tp nd bd' Q);
    try assumption; try reflexivity.
  - intros Ai rho1 tp1. cbn [map]. eapply (TRs_pre ok); [|apply MC; [exact HKc|]; apply ok_frameA_of_K; [exact Hok|]; intros r p t m (_ & X & _); exact X].
    intros w [HsmW [HJ [HB1 HB2]]]. split; [exact HsmW|]. exact (conj HJ (conj HB1 HB2)).
  - intros Ai tr ms md Hsm HM HX. exact (XP_memcpy_site Ai Cl entry s R rho tp tr ms md Hsm HM HX He).
Qed.

Theorem memcpy_callA_ex : ltac2:(tb__ "0|6|
S0S0S0S34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80SbS6fA1S9eS3bSe2S1cG1Se3R3A1Sa0Vsegs;S62Vsegs;SefVAInv;R5R4A3ScbR10A1R3R2A5S9aVsegs;S113R3R2SfSdS34S96A2M2SeS34S96Sc6RfA1Sd7VAInv;VCST;VXGL;R5R4A5M3A4SfG2SeS34S96Sc6ReA1G3A4S16G2A1A3A3A5A3F_;Ftp1;Frho1;FKc';FA;S3S10G0A1S97R9ScbRcA1R8A3S12G0R7A2A3S3SaS98RaScbRdA1R9R8SfS34Sc6RcA1SfS34Sc6RbA1S16S34A1M4A3A3A5ScA3S3SaSa3RaA1ScA3S3SaSf8VNP;S1dS35RcA1A1A2ScA3S3SaS82S1dS35RdA1A1R8A2ScA3S3SaS70S1dS35ReA1A1R8A2ScA3Sa5S21S35RfA1A1S23Z0M5A1G5S81RaA1R9A5Sa4R10RfReRdRbS13S0A1S3bS7bS8Lms;LAi;A7S34S1cG1S58S34R3SfS34Sc6R16A1SfS34Sc6R15A1G4A3A3A3Sa0Vsegs;S62Vsegs;VJA;S7eS7cR10A1S7dR10A1RfS7fR10A1A4A1Sa2ScbR18A1R15R14R13R4A5R3R2A5ReA3F_;Ftp';Frho';FL;Sa0Vsegs;S62Vsegs;VJA;RdA1R12RfReA5RbA3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;Fbd';Fnd;Ftp;Frho;FR;Fs;FCl;Fretpc2;Fretpc;Fentry;").
Proof using ALA HCST HXGL HKc.
  intros entry retpc retpc2 Cl s R rho tp nd bd' Q MCX He Hchk Htp Hnf Hnb Hbb HPAY HSITE Tcont.
  apply (purec_callT_xp (etriple segs) TRe_facts TRe_ex TRe_pre (call_completePA3 segs) XP_memcpy (Pre_memcpy entry) [L_memcpy retpc; L_memcpy retpc2] Cl s R rho tp nd bd' Q);
    try assumption; try reflexivity.
  - intros Ai rho1 tp1. cbn [map]. eapply TRe_pre; [|apply MCX; exact HKc].
    intros w [HsmW [HJ [HB1 HB2]]]. split; [exact HsmW|]. exact (conj HJ (conj HB1 HB2)).
  - intros Ai tr ms md Hsm HM HX. exact (XP_memcpy_site Ai Cl entry s R rho tp tr ms md Hsm HM HX He).
Qed.

Lemma in_cls_range : ltac2:(tb__ "0|2|
S0S58S0R1SfS0Z0M0SfS0Z1SfS0Z2SfS0Z3SfS0Z5SfS0Z6M1S16S0A1A3A3A3A3A3A3A3S4S4bG0R2A2S4bR2G1A2A2F_;Fc;").
Proof using . intros c H. cbn in H. lia. Qed.

Theorem smalloc_callA : ltac2:(tb__ "0|5|
Sa1OF_;S0S34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80S1S1S9eS88Vsegs;VKc;RbA3Sd0Vsegs;VE;VAInv;VCST;VXGL;A5S58S0RcSfS0Z0SfS0Z1SfS0Z2SfS0Z3SfS0Z5SfS0Z6S16S0A1A3A3A3A3A3A3A3S3S10G0A1S97RcSc0VE;RdA2RbA3S12G0RaA2A3S3SaS98RdSc0VE;ReA2RcRbSfS34Sc4VE;ReA2S16S34A1A3A5ScA3S3SaSa3RdA1ScA3S3SaSf8VNP;S1dS35RfA1A1A2ScA3S3SaS82S1dS35R10A1A1RbA2ScA3S3SaS74S81RcA1A1ScA3S3S1bS66S99R11Sc0VE;R13A2Sc4VE;R13A2R12A4Sc3A2S20RcA1A3S3SaSf8S1dS35R13A1A1RdA2ScA3S3S1bS66S99R13Sc0VE;R15A2Sc4VE;R15A2R14A4Sd9A2S20RdA1A3S3SaSf8S1dS35R15A1A1ReA2ScA3S3bS3bVPA;R2A1M2G2F_;FA';FA;Sa4R17R16R15R14R12S13S0A1S3bS7bS4S4bS6eR16S66R18PcA2A2S117R1aA1A2S12eS12dSa9R1aSaeA2Sa9R1aS127SdSdS1bS0A2M3S1bA2M4SdS0S0A2S8cR16A1S7dR14A1A4A2A2U8A2A2Lms;LAi;A7S1cG1S9fVsegs;R1cS62Vsegs;VJA;S7eS7cR15A1SfG4SeG3S1bSeS1bS0S20R14A1R1bA4S20R13A1A4S7dR15A1A3S81R15A1S7fR15A1A4A1Sa2Sc0VE;R1bA2R1aR19R18Sc4VE;R1bA2A5R2R1A5R12A4Ftp';Frho';S9fVsegs;R1bS62Vsegs;VJA;R14A1R19R16R15A5R11A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;FpF;FpR;Fnd;Ftp;Frho;FR;Fs;FCl;Fc;Fok;").
Proof using ALA HCST HXGL HKc.
  intros ok c Cl s R rho tp nd pR pF Q Hok AC Hin. pose proof (in_cls_range c Hin) as Hc6. revert Hc6. by_callT_safety ok smalloc_callT.
  intros Ai rho1 tp1. apply (aca_stack_malloc _ _ _ _ _ AC c Hin); [exact HKc|]. apply ok_frameA_of_K; [exact Hok|]. intros r p t m (_ & X & _). exact X.
Qed.

Theorem smalloc_callA_ex : ltac2:(tb__ "0|5|
S0S34S67SbS1eA1M0S1cSbS5fQ40A1A1M1S80S1S1S9eSd3Vsegs;VE;VAInv;VCST;VXGL;A5S58S0RbSfS0Z0SfS0Z1SfS0Z2SfS0Z3SfS0Z5SfS0Z6S16S0A1A3A3A3A3A3A3A3S3S10G0A1S97RbSc0VE;RcA2RaA3S12G0R9A2A3S3SaS98RcSc0VE;RdA2RbRaSfS34Sc4VE;RdA2S16S34A1A3A5ScA3S3SaSa3RcA1ScA3S3SaSf8VNP;S1dS35ReA1A1A2ScA3S3SaS82S1dS35RfA1A1RaA2ScA3S3SaS74S81RbA1A1ScA3S3S1bS66S99R10Sc0VE;R12A2Sc4VE;R12A2R11A4Sc3A2S20RbA1A3S3SaSf8S1dS35R12A1A1RcA2ScA3S3S1bS66S99R12Sc0VE;R14A2Sc4VE;R14A2R13A4Sd9A2S20RcA1A3S3SaSf8S1dS35R14A1A1RdA2ScA3S3bS3bVPA;R2A1M2G2F_;FA';FA;Sa4R16R15R14R13R11S13S0A1S3bS7bS4S4bS6eR15S66R17PcA2A2S117R19A1A2S12eS12dSa9R19SaeA2Sa9R19S127SdSdS1bS0A2M3S1bA2M4SdS0S0A2S8cR15A1S7dR13A1A4A2A2U8A2A2Lms;LAi;A7S1cG1Sa0Vsegs;S62Vsegs;VJA;S7eS7cR14A1SfG4SeG3S1bSeS1bS0S20R13A1R1aA4S20R12A1A4S7dR14A1A3S81R14A1S7fR14A1A4A1Sa2Sc0VE;R1aA2R19R18R17Sc4VE;R1aA2A5R2R1A5R11A3Ftp';Frho';Sa0Vsegs;S62Vsegs;VJA;R13A1R18R15R14A5R10A3F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FQ;FpF;FpR;Fnd;Ftp;Frho;FR;Fs;FCl;Fc;").
Proof using ALA HCST HXGL HKc.
  intros c Cl s R rho tp nd pR pF Q ACX Hin. pose proof (in_cls_range c Hin) as Hc6. revert Hc6. by_callT_ex smalloc_callT.
  intros Ai rho1 tp1. apply (acx_stack_malloc _ _ _ _ _ ACX c Hin). exact HKc.
Qed.

End Sum.
End WithSegs.

Ltac cen_same_tvG Hlink Hnb HLeq :=
  cbn zeta; intros ? Hcl _ _ Hut; split; [first [exact Hcl | rewrite <- HLeq; exact Hcl]|];
  eapply untracked_agree; [apply agree_vals_sym; eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch] | | exact Hut];
  exact (proj1 (nd_below_split _ _ Hnb)).
Ltac capK_sameG HCK HLeq HVeq :=
  eapply capK_same; [exact HCK | exact HLeq | rewrite HVeq;
  repeat match goal with |- context [bv_unsigned ?x] => lazymatch goal with H : 0 <= bv_unsigned x < _ |- _ => fail | _ => pose proof (bv_urange x) end end; lia].

Ltac capN_sameG HCN Hlink Hnb HLeq :=
  eapply capN_same_live;
  [exact HCN | first [exact HLeq | symmetry; exact HLeq] | eapply agree_vals_trans; [exact (proj1 Hlink) | apply agree_vals_patch] | exact (proj1 (nd_below_split _ _ Hnb))].
