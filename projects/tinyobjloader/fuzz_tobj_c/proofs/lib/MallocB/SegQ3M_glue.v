(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "prod"; "list"; "app"; "cons"; "nat"; "pair"; "andb"; "nil"; "length"; "option"; "bool"; "true"; "Some"; "fst"; "negb"; "S"; "false"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "qb_addr"; "qb_items"; "aa_geom"; "qb_size"; "ag_thread"; "topG"; "mkQB"; "AA"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "ex"; "True"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "pow"; "sub"; "opp"; "mul"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "sv"; "valuation"; "sprop"; "rm"; "ss_objs"; "eval"; "ss_facts"; "obj_range"; "holds"; "rw"; "sv_eqb"; "ob_base"; "ob_hi"; "ob_lo"; "ss_next"; "swf"; "SLit"; "cell"; "mkSS"; "ranges_disjoint"; "sprop_below"; "sprop_eqb"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue.MGlue"; "dspec"; "dobj"; "w_ok"; "t_C"; "with_objs"; "TJ"; "dzone"; "same_rng"; "t_Cd"; "t_F"; "t_OC"; "t_bs"; "FIX9"; "JRM"; "apart_d"; "carve_cond"; "diss_cond"; "diss_res"; "forallb2"; "keepN"; "t_Ca"; "t_M"; "t_T"; "t_k"; "addF"; "addO"; "dcs"; "dropN"; "in_ext"; "t_Cc"; "t_ok"; "trans"; "@Stdlib.Lists.List"; "In"; "forallb"; "ForallOrdPairs"; "nth_error"; "Exists"; "combine"; "existsb"; "fold_right"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "firstn"; "skipn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "bview"; "cell_ok"; "mkACell"; "view"; "present"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_setS"; "ax_X"; "axst"; "ax_base"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue"; "GI"; "capb"; "MMEM"; "COPIED"; "mergeb"; "isum"; "emptyb"; "emptied"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop"; "benv"; "fixed_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states"; "ZQ"; "STK"; "SW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "qitems"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel"; "FRM"; "tlinks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "batch_mem"; "QW"; "item_mem"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep"; "qlinks_to"; "ifoot"; "hd_addr"; "last_addr"; "bfoot"; "@Corelib.Init.Nat"; "add"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kQuarantineBatchSize"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kQuarantineBatchCount"; "HIGH_SHADOW_END"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "qlinks"; "qhdr_repr"; "qsize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE";
"@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "cells_inside"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "pre_facts"; "top_high"; "A_globals"; "V_DEPTH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "DEPTH_R"; "QG"; "O_gmax"; "O_gq"; "O_mtx"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "leb"; "@Stdlib.Sorting.Permutation"; "Permutation"; "@stdpp.base"; "NoDup"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all"; "sv_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue"; "notin_vars"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM"; "entsM"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ic.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ie.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ij.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require il.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition capb (b : qbatch) : Prop := ltac2:(tb__ "0|0|
S24S26SaS2S0S0A2S16Vb;A1A2A1Sa9A2").
Definition emptied (b : qbatch) : Prop := ltac2:(tb__ "0|1|
S1dS1eS3S2S0S0A2M0A1S16Vb;A1S9G0A1A3S1eS0S18Vb;A1Sa6A3A2").
Definition mergeb (c n : qbatch) : qbatch := ltac2:(tb__ "0|0|
S1bS15Vc;A1S4S2S0S0A2S16Vc;A1S16Vn;A1A3S28S23S18Vc;A1S18Vn;A1A2Sa6A2A3").
Definition emptyb (n : qbatch) : qbatch := ltac2:(tb__ "0|0|
S1bS15Vn;A1S9S2S0S0A2A1Sa6A3").
Definition isum (l : list (Z * Z)) : Z := ltac2:(tb__ "0|1|
S70S0S2S0S0A2M0G0S0S23S13S0S0R2A3R1A2Lacc;Lit;Z0Vl;A5").
Lemma isum_app : ltac2:(tb__ "0|2|
S3S2S0S0A2M0A1M1G1S1eS0S87S4G0R2R1A3A1S23S87R2A1S87R1A1A2A3Fl2;Fl1;").
Proof. intros l1 l2. unfold isum. induction l1 as [|x r IH]; cbn [app fold_right]; [lia | rewrite IH; lia]. Qed.

Definition GI (all E glob : list qbatch) : Prop := ltac2:(tb__ "0|1|
S1dSc1S0S71S14S0S15Vall;A4S71S14S0S15S4S14VE;Vglob;A3M0A4A3S1dSc1S2S0S0A2S95Vall;A1S95G0A1A3S1dS72S14S83G0A3S1dS72S14S89VE;A3S1eS0SadG0A1SadVall;A1A3A2A2A2A2").

Lemma GI_init : ltac2:(tb__ "0|0|
S3S14A1S72S14S83R1A3S82R2S9S14A1R2A3F_;Fall;").
Proof. intros all H. split; [apply Permutation_refl|]. split; [apply Permutation_refl|]. split; [exact H|]. split; [constructor | reflexivity]. Qed.

Lemma GI_merge : ltac2:(tb__ "0|1|
S3S14A1M0G0G0S14S14G0S82R6R5S4S14R4S5S14R3S5S14R2R1A3A3A3A3S83S86R4R3A2A1S82R8S4S14R7S5S14S88R4A1S9S14A1A3A3S4S14R6S5S14S86R5R4A2R3A3A3A3F_;F_;FL;Fn;Fc;FD;FE;Fall;").
Proof.
  intros all E D c n L (P1 & P2 & FC & FE & QS) HC. split; [|split; [|split; [|split]]].
  - eapply Permutation_trans; [exact P1|]. rewrite !map_app. cbn [map mergeb emptyb qb_addr]. rewrite <- app_assoc. apply Permutation_app_head. cbn [app].
    symmetry. replace (map qb_addr D ++ qb_addr c :: qb_addr n :: map qb_addr L) with ((map qb_addr D ++ [qb_addr c]) ++ qb_addr n :: map qb_addr L) by (rewrite <- app_assoc; reflexivity).
    replace (map qb_addr D ++ qb_addr c :: map qb_addr L) with ((map qb_addr D ++ [qb_addr c]) ++ map qb_addr L) by (rewrite <- app_assoc; reflexivity).
    apply Permutation_middle.
  - assert (EQ : qitems ((E ++ [emptyb n]) ++ D ++ mergeb c n :: L) = qitems (E ++ D ++ c :: n :: L)).
    { unfold qitems. rewrite !flat_map_app. cbn [flat_map emptyb mergeb qb_items app]. rewrite app_nil_r, <- !app_assoc. reflexivity. }
    rewrite EQ. exact P2.
  - apply Forall_app in FC as [FC1 FC2]. apply Forall_app in FC2 as [FC2 FC3]. inversion FC3 as [|? ? Hc FC4]; subst. inversion FC4 as [|? ? Hn FC5]; subst.
    apply Forall_app; split; [apply Forall_app; split; [exact FC1 | constructor; [unfold capb, emptyb; cbn; unfold kQuarantineBatchCount; lia | constructor]]|].
    apply Forall_app; split; [exact FC2 | constructor; [exact HC | exact FC5]].
  - apply Forall_app; split; [exact FE | constructor; [split; reflexivity | constructor]].
  - rewrite <- QS. rewrite !qsize_app, !qsize_cons. cbn [qb_size mergeb emptyb]. change (qsize []) with 0. lia.
Qed.

Lemma ND_permM : forall {X} (l k : list X), Permutation l k -> NoDup l -> NoDup k.
Proof. intros X l k HP ND. apply (proj2 (NoDup_ListNoDup _)). apply (Permutation_NoDup HP). apply (proj1 (NoDup_ListNoDup _)). exact ND. Qed.
Lemma nodup_mid_ne : ltac2:(tb__ "0|1|
S3S14A1M0G0S14S14Sc2S0S71S14S0S15S4S14R4S5S14R2R3A3A3A4A2S69S14R2S4S14R5R4A3A3S1fS1eS0S15R3A1S15R4A1A3A1F_;F_;Fb;Fx;Fl2;Fl1;").
Proof.
  intros l1 l2 x b ND Hb E. rewrite map_app in ND. cbn [map] in ND. apply (proj1 (NoDup_ListNoDup _)) in ND. apply List.NoDup_remove_2 in ND. apply ND.
  rewrite <- E. rewrite <- map_app. apply in_map. exact Hb.
Qed.

Definition MMEM (m : bview) (G : ageom) (E glob : list qbatch) : Prop := ltac2:(tb__ "0|0|
S1dS72S14S98Vm;A1S4S14VE;Vglob;A3A3S1dSabVm;VE;A2S1dSabVm;Vglob;A2SacVm;S23S19VG;A1Z50A2S9S14A1A3A2A2A2").
Definition COPIED (m : bview) (c n : qbatch) (j : nat) : Prop := ltac2:(tb__ "0|1|
S6S2S0S0A2M0Sc3R2Vj;A2S1eSbG0A1S6cG0S16Vn;A1R3A3SeG0R2A2A3S79Vm;S7aS23S23S15Vc;A1Z18A2S2aZ8S26Sa0SaG0S16Vc;A1A2R4A2A1A2A2U8S28SfS0S0R3A3Z10A2A3A2F_;F_;Fit;Fi;").

Lemma bm_frame : ltac2:(tb__ "0|0|
S78S78S14S83R1A1S0S9fR3R1A2S1eSbS76Q8A1A1R5R2A1R6R2A1A3F_;Fz;S98R5R3A2S98R5R4A2F_;F_;F_;Fb;Fm';Fm;").
Proof.
  intros m m' b HL Hm (H1 & H2 & H3 & H4 & H5). unfold bfoot, kQuarantineBatchSize in Hm. unfold capb, kQuarantineBatchCount in HL.
  assert (HB : forall z, qb_addr b + 8 <= z < qb_addr b + 8192 -> m' z = m z) by (intros z Hz; apply Hm; left; exact Hz).
  split; [eapply cell_ok_frame1; [|exact H1]; cbn; intros z Hz; apply HB; lia|].
  split; [eapply cell_ok_frame1; [|exact H2]; cbn; intros z Hz; apply HB; lia|].
  split; [exact H3|]. split; [eapply present_frame; [|exact H4]; intros z Hz; apply HB; unfold kQuarantineBatchSize in Hz; lia|].
  intros i it Hi. destruct (H5 i it Hi) as [C I]. pose proof (nth_error_In _ _ Hi) as Hin.
  assert (Hi' : (i < length (qb_items b))%nat) by (apply (proj1 (nth_error_Some (qb_items b) i)); rewrite Hi; discriminate).
  split.
  - eapply cell_ok_frame1; [|exact C]. cbn. intros z Hz. apply HB. lia.
  - eapply item_mem_frame; [apply (proj1 (rz_facts (snd it))) | | exact I]. intros z Hz. apply Hm. right. apply List.Exists_exists. exists it. split; [exact Hin | exact Hz].
Qed.

Lemma qlinks_to_split : ltac2:(tb__ "0|1|
S78S3S14A1M0G0S0S1fS1eG0R2S9S14A1A3A1S9bR5S4S14R4R3A3R2A3S1dS9bR6R5S9dR4A1A3S9bR6R4R3A3A2F_;F_;Ft;Fl2;Fl1;Fm;").
Proof.
  intros m l1 l2 t Hne. induction l1 as [|b r IH]; cbn [app]; intros H; [split; [exact I | exact H]|].
  cbn [qlinks_to] in H |- *. destruct H as [Hc Hr]. destruct (IH Hr) as [I1 I2]. split; [|exact I2]. split; [|exact I1].
  destruct r as [|b' r']; cbn [app] in Hc |- *; [|exact Hc]. destruct l2 as [|c l2']; [congruence|]. unfold hd_addr. cbn. exact Hc.
Qed.
Lemma qlinks_tlinks : ltac2:(tb__ "0|0|
S78S3S14A1SabR2R1A2S97R3R2A2F_;Fl;Fm;").
Proof.
  intros m l H. unfold tlinks. destruct l as [|b r]; [exact I|]. set (l := b :: r) in *. assert (NE : l <> []) by (unfold l; discriminate).
  apply qlinks_to_0 in H. rewrite (app_removelast_last qb_dflt NE) in H. destruct (qlinks_to_split m (removelast l) [last l qb_dflt] 0 ltac:(discriminate) H) as [H1 _]. exact H1.
Qed.
Lemma list_eq_nilq : ltac2:(tb__ "0|2|
S3S14A1M0S20S1eG0R1S9S14A1A3M1S1fG1A1A2Fl;").
Proof. intros [|x r]; [left; reflexivity | right; discriminate]. Qed.

Section MGlue.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A0 : AA) (rho0 : valuation) (A1 : AA).
Hypothesis HTH : aa_q_thread A1 = [].
Hypothesis HCI : aa_cache_inited A1 = true.
Hypothesis HQW : ltac2:(tb__ "0|0|
S0S99VA1;R1A2S99VA0;R2A2F_;Fz;").
Let all := aa_q_global A1.

Lemma addr_facts : ltac2:(tb__ "0|2|
S2eS0S8aVA1;R2A2S69S0R2S71S14S0S15Vall;A4A3S1dS24Z643000R3A2S1dS24S23R3Z2000M0A2M1S1aS17VA1;A1A1A2S1dS24G1S27Z2Z3eA2A2S1dS24SaaR3A2S1eS0S2bR3G0A2Z0A3A2A2A2A2F_;F_;Fa;Frho;").
Proof. intros rho a BE Ha. apply in_map_iff in Ha as (b & <- & Hb). exact (batch_addr_facts A1 HTH rho b BE Hb). Qed.
Lemma addrs_apart : ltac2:(tb__ "0|2|
S2eS0S0S8aVA1;R3A2S69S0R3S71S14S0S15Vall;A4A3M0G0S1fS1eS0R5R4A3A1S20S24S23R6Z2000M1A2R5A2S24S23R5G1A2R6A2A2F_;F_;F_;F_;Fa2;Fa1;Frho;").
Proof. intros rho a1 a2 BE H1 H2 NE. apply in_map_iff in H1 as (b1 & <- & Hb1). apply in_map_iff in H2 as (b2 & <- & Hb2). exact (batches_apart1 A1 HTH rho b1 b2 BE Hb1 Hb2 NE). Qed.
Lemma ifoot_not_addr : ltac2:(tb__ "0|1|
S2eS2S0S0A2M0S0S8aVA1;R3A2S69G0R3S95Vall;A1A3S69S0R3S71S14S0S15Vall;A4A3S0S9cR6R1A2S1fS1dS24R6R2A2S25R2S23R6Z2000A2A2A2A1F_;Fz;F_;F_;F_;Fa;Fit;Frho;").
Proof. intros rho it a BE Hit Ha z Hz. apply in_map_iff in Ha as (b & <- & Hb). exact (ifoot_not_batch A1 HTH rho it b BE Hit Hb z Hz). Qed.
Lemma addr_in_QW : ltac2:(tb__ "0|0|
S2eS0S0S8aVA1;R3A2S69S0R3S71S14S0S15Vall;A4A3S1dS24R4R3A2S25R3S23R4Z2000A2A2A2S1dS99VA1;R4A2S1fS1dS24Sa8R4A2S25R4Sa7A2A2A1A2F_;F_;F_;Fz;Fa;Frho;").
Proof. intros rho a z BE Ha Hz. apply in_map_iff in Ha as (b & <- & Hb). exact (batch_in_QW A1 HTH rho b z BE Hb Hz). Qed.
Lemma addr_not_thread : ltac2:(tb__ "0|1|
S2eS0S0S8aVA1;R3A2S69S0R3S71S14S0S15Vall;A4A3S1dS24R4R3A2S25R3S23R4Z2000A2A2A2S1fS1dS24S19S17VA1;A1A1M0R4A2S25R4S23G0Z1000A2A2A2A1F_;F_;F_;Fz;Fa;Frho;").
Proof.
  intros rho a z BE Ha Hz. apply in_map_iff in Ha as (b & <- & Hb). apply (be_sep _ _ BE z). unfold q_foot. apply Exists_exists. exists b.
  split; [rewrite HTH; exact Hb | left; unfold kQuarantineBatchSize; lia].
Qed.

Lemma GI_addr : ltac2:(tb__ "0|1|
S3S14A1M0G0S14S82Vall;R3R2A3S69S14R2S4S14R4R3A3A3S69S0S15R3A1S71S14S0S15Vall;A4A3F_;F_;Fb;Fglob;FE;").
Proof. intros E glob b (P1 & _) Hb. eapply Permutation_in; [symmetry; exact P1 | apply in_map; exact Hb]. Qed.
Lemma GI_item : ltac2:(tb__ "0|2|
S3S14A1M0G0S14S2S0S0A2M1S82Vall;R4R3A3S69S14R3S4S14R5R4A3A3S69G1R3S16R4A1A3S69G1R4S95Vall;A1A3F_;F_;F_;Fit;Fb;Fglob;FE;").
Proof. intros E glob b it (_ & P2 & _) Hb Hit. eapply Permutation_in; [symmetry; exact P2|]. unfold qitems. apply in_flat_map. exists b. split; assumption. Qed.
Lemma GI_nodup : ltac2:(tb__ "0|1|
S2eS3S14A1M0G0S8aVA1;R3A2S82Vall;R3R2A3Sc2S0S71S14S0S15S4S14R4R3A3A4A2F_;F_;Fglob;FE;Frho;").
Proof. intros rho E glob BE (P1 & _). exact (ND_permM _ _ P1 (NoDup_addr_all A1 HTH rho BE)). Qed.
Lemma GI_cap : ltac2:(tb__ "0|1|
S3S14A1M0G0S14S82Vall;R3R2A3S69S14R2S4S14R4R3A3A3S83R3A1F_;F_;Fb;Fglob;FE;").
Proof. intros E glob b (_ & _ & FC & _) Hb. exact (proj1 (Forall_forall _ _) FC b Hb). Qed.

Definition w_ok (W : Z -> Prop) : Prop := ltac2:(tb__ "0|2|
S1dS2S0S0A2M0S0S69G0R2S95Vall;A1A3S9cR3R2A2S1fVW;R3A1A1F_;F_;Fz;Fit;S0S1dS24S23S19S17VA1;A1A1M1Z50A2R1A2S25R1S23G1Z70A2A2A2S1fVW;R2A1A1F_;Fz;A2").
Definition in_ext (W : Z -> Prop) : Prop := ltac2:(tb__ "0|0|
S0VW;R1A1S21S0S0S1dS69S0R1S71S14S0S15Vall;A4A3S1dS24R1R3A2S25R3S23R1Z2000A2A2A2A2La;A2F_;Fz;").
Lemma in_ext_ok : ltac2:(tb__ "0|0|
S2eS0OF_;S8aVA1;R2A2S65R2A1S4bR3A1F_;F_;FW;Frho;").
Proof.
  intros rho W BE HW. split.
  - intros it z Hit Hz HP. destruct (HW z HP) as (a & Ha & Hza). exact (ifoot_not_addr rho it a BE Hit Ha z Hz Hza).
  - intros z Hz HP. destruct (HW z HP) as (a & Ha & Hza). apply (addr_not_thread rho a z BE Ha Hza). lia.
Qed.
Lemma ifoot_high : ltac2:(tb__ "0|1|
S2eS2S0S0A2M0S0S8aVA1;R3A2S69G0R3S95Vall;A1A3S9cR4R3A2S24Z643000R4A2F_;F_;F_;Fz;Fit;Frho;").
Proof.
  intros rho it z BE Hit Hz. pose proof (proj1 (be_qp _ _ BE)) as HBP. rewrite (qall_A1 A1 HTH) in HBP. unfold all, qitems in Hit. apply in_flat_map in Hit as (b & Hb & Hit).
  pose proof (proj1 (Forall_forall _ _) HBP b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (IP1 & IP2 & _).
  pose proof (rz_facts (snd it)) as [RZ1 RZ2]. unfold IMG_HI in IP1. unfold ifoot, it_ab in Hz.
  assert (SHlo : 0x7fff8000 <= Sh (fst it)) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos (fst it) 8 ltac:(lia) ltac:(lia)); lia).
  destruct Hz; lia.
Qed.
Lemma hdr_ok : ltac2:(tb__ "0|0|
S2eS8aVA1;R1A2S4bS0S1dS24S23SbbZa0A2R1A2S25R1S23SbbZc0A2A2A2Lz;A1F_;Frho;").
Proof.
  intros rho BE. split.
  - intros it z Hit Hz HP. pose proof (ifoot_high rho it z BE Hit Hz). unfold QG in HP. lia.
  - intros z Hz HP. pose proof (geom_bands _ (be_geom _ _ BE)) as (_ & _ & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI. pose proof (geom_old _ (be_geom _ _ BE)) as (_ & _ & _ & _ & G5 & _).
    unfold QG in HP. lia.
Qed.

Lemma items_frame : ltac2:(tb__ "0|2|
S78S78S3S14A1M0G0S0OF_;S82Vall;R3R2A3S4bR2A1S0S1fR4R1A1A1S1eSbS76Q8A1A1R8R2A1R9R2A1A3F_;Fz;S14S2S0S0A2M1S69S14R2S4S14R8R7A3A3S69G1R2S16R3A1A3S9aRcR3A2S9aRcR4A2F_;F_;F_;Fit;Fb;F_;F_;F_;FW;Fglob;FE;Fv3;Fv;").
Proof.
  intros v v3 E glob W HGI [HW _] FR b it Hb Hit HI.
  eapply item_mem_frame; [apply (proj1 (rz_facts (snd it))) | | exact HI]. intros z Hz. apply FR. exact (HW it z (GI_item E glob b it HGI Hb Hit) Hz).
Qed.
Lemma bm_frame_ext : ltac2:(tb__ "0|3|
S78S78S3S14A1M0G0S0OF_;S82Vall;R3R2A3S4bR2A1S0S1fR4R1A1A1S1eSbS76Q8A1A1R8R2A1M1R9R2A1A3F_;Fz;S14S69S14R1S4S14R7R6A3A3S0S1dS24S23S15R3A1M2Z8A2R1A2S25R1S23G2Z2000A2A2A2S1fG1A1F_;Fz;S98RbR3A2S98RbR4A2F_;F_;F_;Fb;F_;F_;F_;FW;Fglob;FE;Fv3;Fv;").
Proof.
  intros v v3 E glob W HGI [HW _] FR b Hb HX HM. apply (bm_frame v v3 b (GI_cap E glob b HGI Hb)); [|exact HM].
  intros z Hz. apply FR. destruct Hz as [Hz|Hz]; [unfold kQuarantineBatchSize in Hz; exact (HX z Hz)|].
  apply List.Exists_exists in Hz as (it & Hit & Hz). exact (HW it z (GI_item E glob b it HGI Hb Hit) Hz).
Qed.
Lemma thd_frame : ltac2:(tb__ "0|1|
S78S78S0OF_;S4bR1A1S0S1fR3R1A1A1S1eSbS76Q8A1A1R5R2A1R6R2A1A3F_;Fz;SacR5S23S19S17VA1;A1A1Z50A2S9S14A1A3M0G0F_;F_;F_;FW;Fv3;Fv;").
Proof.
  intros v v3 W [_ HW] FR (T0 & T1 & T2 & T3).
  assert (QF : forall z, ag_thread (aa_geom A1) + 80 <= z < ag_thread (aa_geom A1) + 112 -> v3 z = v z) by (intros z Hz; apply FR; exact (HW z Hz)).
  split; [eapply cell_ok_frame1; [|exact T0]; cbn; intros z Hz; apply QF; lia|]. split; [intros X; exfalso; exact (X eq_refl)|].
  split; [eapply present_frame; [|exact T2]; intros z Hz; apply QF; lia | eapply cell_ok_frame1; [|exact T3]; cbn; intros z Hz; apply QF; lia].
Qed.

Lemma links_frame : ltac2:(tb__ "0|1|
S78S78S0OF_;S3S14A1S0S0S1fR4R1A1A1S1eSbS76Q8A1A1R6R2A1R7R2A1A3F_;Fz;S14S0S69S14R2R5A3S1dS24S15R3A1M0R2A2S25R2S23G0Z8A2A2A2S1fR8R3A1A1F_;F_;Fz;Fb;S9bR7R4R3A3S9bR7R5R4A3F_;F_;F_;Ft;Fl;FW;Fv3;Fv;").
Proof. intros v v3 W l t FR HX H. apply (qlinks_to_frame v v3 l t); [|exact H]. intros b z Hb Hz. apply FR. exact (HX b z Hb Hz). Qed.

Lemma mmem_copy : ltac2:(tb__ "0|5|
S2eS78S78S3S14A1M0G0S14S14G0S6S2S0S0A2M1S8aVA1;RaA2S82Vall;R8S4S14R7S5S14R6S5S14R5R4A3A3A3A3S84RbS17VA1;A1M2R9S4S14R8S5S14R7S5S14R6R5A3A3A3A4S85RcR8R7R5A4S1eSbG1A1S6cG1S16R8A1R6A3SeG1R5A2A3S25S26Sa0SaG1S16RaA1A2R7A2A1Sa9A2S0S1fS1dS24S23S23S15RcA1Z18A2S2aZ8M3S26Sa0SaG1S16RcA1A2R9A2A1A2A2M4R1A2S25R1S23G4G3A2A2A2A1S1eSbS76Q8A1A1R10R2A1R11R2A1A3F_;Fz;S79RfS7aG4U8S28SfS0S0R8A3Z10A2A3A2S1dS84R10G2RfS4S14ReS5S14RdS5S14RcRbA3A3A3A4S85R10RdRcS11RaA1A4A2F_;F_;F_;F_;F_;F_;F_;F_;Fit;Fj;FL;Fn;Fc;FD;FE;Fv3;Fv;Frho;").
Proof.
  intros rho v v3 E D c n L j it BE HGI (HBM & HLE & HLG & HTD) HCP Hnth HJ FR CD.
  set (dst := qb_addr c + 24 + 8 * Z.of_nat (length (qb_items c) + j)) in *. unfold kQuarantineBatchCount in HJ.
  set (W := fun z => dst <= z < dst + 8).
  assert (INC : In c (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  pose proof (GI_addr _ _ c HGI INC) as AC. pose proof (GI_nodup rho _ _ BE HGI) as ND.
  assert (HW : w_ok W) by (apply (in_ext_ok rho W BE); intros z Hz; exists (qb_addr c); split; [exact AC | unfold W in Hz; lia]).
  assert (FRW : forall z, ~ W z -> v3 z = v z) by (intros z Hz; apply FR; exact Hz).
  assert (OTH : forall b, In b (E ++ D ++ c :: n :: L) -> qb_addr b <> qb_addr c -> forall z, qb_addr b <= z < qb_addr b + 8192 -> ~ W z).
  { intros b Hb NE z Hz HP. pose proof (addrs_apart rho _ _ BE (GI_addr _ _ b HGI Hb) AC NE). unfold W in HP. lia. }
  split; [split; [|split; [|split]]|].
  - apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) HBM b Hb) as Mb.
    destruct (Z.eq_dec (qb_addr b) (qb_addr c)) as [EQ|NE].
    + assert (b = c) by exact (NoDup_map_In_inj qb_addr _ b c ND Hb INC EQ). subst b. destruct Mb as (H1 & H2 & H3 & H4 & H5).
      split; [eapply cell_ok_frame1; [|exact H1]; cbn; intros z Hz; apply FR; lia|].
      split; [eapply cell_ok_frame1; [|exact H2]; cbn; intros z Hz; apply FR; lia|].
      split; [exact H3|]. split.
      * intros z Hz. destruct (Z_lt_dec z dst) as [L1|L1]; [rewrite FR by lia; exact (H4 z Hz)|]. destruct (Z_lt_dec z (dst + 8)) as [L2|L2]; [|rewrite FR by lia; exact (H4 z Hz)].
        pose proof (CD (Z.to_nat (z - dst)) ltac:(cbn; lia)) as X. cbn [c_addr c_w RtCells.c_val] in X. replace (dst + Z.of_nat (Z.to_nat (z - dst))) with z in X by lia. eexists. exact X.
      * intros i it' Hi. destruct (H5 i it' Hi) as [C I]. assert (Hi' : (i < length (qb_items c))%nat) by (apply (proj1 (nth_error_Some (qb_items c) i)); rewrite Hi; discriminate).
        split; [eapply cell_ok_frame1; [|exact C]; cbn; intros z Hz; apply FR; lia|].
        exact (items_frame v v3 _ _ W HGI HW FRW c it' INC (nth_error_In _ _ Hi) I).
    + apply (bm_frame_ext v v3 _ _ W HGI HW FRW b Hb); [|exact Mb]. intros z Hz. apply (OTH b Hb NE). lia.
  - apply qlinks_to_0. apply qlinks_to_0 in HLE. apply (links_frame v v3 W E 0 FRW); [|exact HLE]. intros b z Hb Hz HP.
    assert (Hb' : In b (E ++ D ++ c :: n :: L)) by (apply in_or_app; left; exact Hb).
    destruct (Z.eq_dec (qb_addr b) (qb_addr c)) as [EQ|NE]; [unfold W in HP; lia | apply (OTH b Hb' NE z); [lia | exact HP]].
  - apply qlinks_to_0. apply qlinks_to_0 in HLG. apply (links_frame v v3 W _ 0 FRW); [|exact HLG]. intros b z Hb Hz HP.
    assert (Hb' : In b (E ++ D ++ c :: n :: L)) by (apply in_or_app; right; exact Hb).
    destruct (Z.eq_dec (qb_addr b) (qb_addr c)) as [EQ|NE]; [unfold W in HP; lia | apply (OTH b Hb' NE z); [lia | exact HP]].
  - exact (thd_frame v v3 W HW FRW HTD).
  - intros i it' Hi Hn. destruct (Nat.eq_dec i j) as [->|NEi].
    + rewrite Hnth in Hn. injection Hn as <-. exact CD.
    + eapply cell_ok_frame1; [|exact (HCP i it' ltac:(lia) Hn)]. cbn. intros z Hz. apply FR. lia.
Qed.

Lemma mmem_merge : ltac2:(tb__ "0|e|
S2eS78S78S3S14A1M0G0S14S14G0S8aVA1;R8A2S82Vall;R6S4S14R5S5S14R4S5S14R3R2A3A3A3A3S84R9S17VA1;A1M1R7S4S14R6S5S14R5S5S14R4R3A3A3A3A4S85RaR6R5SaS2S0S0A2M2S16R5A1A2A4S83S86R7R6A2A1S0S1fS20S1dS24S15R9A1M3R1A2S25R1S23G3Z18M4A2A2A2S20S1dS24S15R8A1M5R1A2S25R1S23G5G4A2A2A2S1dS1fS1eG0RbS9S14A1M6A3A1S1dS24S9eRbA1M7R1A2S25R1S23G7Z8M8A2A2A2A2A2A2A1S1eSbS76Q8A1A1RdR2A1ReR2A1A3F_;Fz;S79RcS7aG3U8M9S9dR7A1A3A2S79RdS7aS23S15RaA1G8A2G9S28S23S18RaA1S18R9A1A2Z2000MaA2A3A2S79ReS7aS23S15RbA1MbZ10McA2G9S26Sa0SaG2S16RbA1A2SaG2S16RaA1A2A2A1A3A2S79RfS7aGbG9Z0MdA3A2S79R10S7aS23S15RcA1G8A2G9GaA3A2S79R11S7aS23S15RdA1GcA2G9GdA3A2S1fS1eG0R11G6A3A1S79R13S7aS9eR12A1G9S15RfA1A3A2F_;S84R13G1S4S14R12S5S14S88RfA1G6A3A3S4S14R11S5S14S86R10RfA2ReA3A3A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;FL;Fn;Fc;FD;FE;Fv3;Fv;Frho;").
Proof.
  intros rho v v3 E D c n L BE HGI (HBM & HLE & HLG & HTD) HCP HCAP FR Cc0 Cc1 Cc2 Cn0 Cn1 Cn2 CE.
  unfold capb, kQuarantineBatchCount in HCAP. cbn [mergeb qb_items] in HCAP. rewrite length_app in HCAP.
  set (W := fun z => (qb_addr c <= z < qb_addr c + 24) \/ (qb_addr n <= z < qb_addr n + 24) \/ (E <> [] /\ last_addr E <= z < last_addr E + 8)) in *.
  set (old := E ++ D ++ c :: n :: L) in *.
  assert (INC : In c old) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
  assert (INN : In n old) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
  assert (INL : E <> [] -> In (last E qb_dflt) old) by (intros NE; apply in_or_app; left; apply In_last; exact NE).
  pose proof (GI_addr _ _ c HGI INC) as AC. pose proof (GI_addr _ _ n HGI INN) as AN. pose proof (GI_nodup rho _ _ BE HGI) as ND. fold old in ND.
  assert (HW : w_ok W).
  { apply (in_ext_ok rho W BE). intros z [Hz|[Hz|[NE Hz]]]; [exists (qb_addr c); split; [exact AC | lia] | exists (qb_addr n); split; [exact AN | lia] |].
    exists (last_addr E). split; [exact (GI_addr _ _ _ HGI (INL NE)) | lia]. }
  assert (APT : forall b b', In b old -> In b' old -> qb_addr b <> qb_addr b' -> qb_addr b + 8192 <= qb_addr b' \/ qb_addr b' + 8192 <= qb_addr b).
  { intros b b' Hb Hb' NE. exact (addrs_apart rho _ _ BE (GI_addr _ _ b HGI Hb) (GI_addr _ _ b' HGI Hb') NE). }

  assert (ONE : forall b, In b (E ++ D ++ L) -> qb_addr b <> qb_addr c /\ qb_addr b <> qb_addr n /\ In b old).
  { intros b Hb. split; [|split].
    - apply (nodup_mid_ne (E ++ D) (n :: L) c b); [unfold old in ND; rewrite <- app_assoc; exact ND|]. rewrite <- app_assoc. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|].
      apply in_or_app; right. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; right; exact Hb].
    - apply (nodup_mid_ne (E ++ D ++ [c]) L n b); [unfold old in ND; rewrite <- !app_assoc; exact ND|]. rewrite <- !app_assoc. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|].
      apply in_or_app; right. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; right; exact Hb].
    - unfold old. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb|]. apply in_or_app; right.
      apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; right; right; exact Hb]. }
  assert (NCN : qb_addr c <> qb_addr n).
  { intros EQ. unfold old in ND. rewrite !map_app in ND. cbn [map] in ND. apply NoDup_app_r in ND. apply NoDup_app_r in ND. inversion ND as [|x l Hn Hd]; subst. apply Hn. rewrite EQ. apply list_elem_of_In. left. reflexivity. }
  assert (ELN : E <> [] -> last_addr E <> qb_addr c /\ last_addr E <> qb_addr n).
  { intros NE. assert (X : In (last E qb_dflt) (E ++ D ++ L)) by (apply in_or_app; left; apply In_last; exact NE). destruct (ONE _ X) as (X1 & X2 & _). split; assumption. }

  assert (EXT : forall b, In b (E ++ D ++ L) -> forall z, qb_addr b + 8 <= z < qb_addr b + 8192 -> ~ W z).
  { intros b Hb z Hz. destruct (ONE b Hb) as (N1 & N2 & Hbo). pose proof (APT b c Hbo INC N1) as P1. pose proof (APT b n Hbo INN N2) as P2.
    intros [HP|[HP|[NE HP]]]; [lia | lia |]. destruct (Z.eq_dec (qb_addr b) (last_addr E)) as [EQ|NQ]; [lia|]. pose proof (APT b _ Hbo (INL NE) NQ). unfold last_addr in *. lia. }
  assert (SLOTS : forall z, (qb_addr c + 24 <= z < qb_addr c + 8192 \/ qb_addr n + 24 <= z < qb_addr n + 8192) -> ~ W z).
  { intros z Hz. pose proof (APT c n INC INN NCN) as P1. intros [HP|[HP|[NE HP]]]; [lia | lia |]. destruct (ELN NE) as [X1 X2].
    pose proof (APT _ c (INL NE) INC X1) as P2. pose proof (APT _ n (INL NE) INN X2) as P3. unfold last_addr in *. lia. }
  pose proof (proj1 (Forall_forall _ _) HBM c INC) as (Hc1 & Hc2 & Hc3 & Hc4 & Hc5). pose proof (proj1 (Forall_forall _ _) HBM n INN) as (Hn1 & Hn2 & Hn3 & Hn4 & Hn5).
  fold (isum (qb_items c)) in Hc3. fold (isum (qb_items n)) in Hn3.
  assert (BMO : forall b, In b (E ++ D ++ L) -> batch_mem v3 b).
  { intros b Hb. destruct (ONE b Hb) as (_ & _ & Hbo). exact (bm_frame_ext v v3 _ _ W HGI HW FR b Hbo (EXT b Hb) (proj1 (Forall_forall _ _) HBM b Hbo)). }
  assert (BMC : batch_mem v3 (mergeb c n)).
  { unfold batch_mem. cbn [mergeb qb_addr qb_size qb_items]. unfold kQuarantineBatchSize in *. split; [exact Cc1|]. split; [rewrite length_app; exact Cc2|].
    split; [fold (isum (qb_items c ++ qb_items n)); rewrite isum_app; lia|].
    split; [intros z Hz; rewrite FR by (apply SLOTS; left; lia); exact (Hc4 z Hz)|].
    intros i it Hi. destruct (Nat.lt_ge_cases i (length (qb_items c))) as [LT|GE].
    - rewrite nth_error_app1 in Hi by exact LT. destruct (Hc5 i it Hi) as [C I]. pose proof (proj1 (Forall_forall _ _) (proj1 (proj2 (proj2 HGI))) c INC) as CAPC. unfold capb, kQuarantineBatchCount in CAPC.
      split; [eapply cell_ok_frame1; [|exact C]; cbn; intros z Hz; apply FR; apply SLOTS; left; lia|].
      exact (items_frame v v3 _ _ W HGI HW FR c it INC (nth_error_In _ _ Hi) I).
    - rewrite nth_error_app2 in Hi by exact GE. assert (LTn : (i - length (qb_items c) < length (qb_items n))%nat) by (apply (proj1 (nth_error_Some _ _)); rewrite Hi; discriminate).
      destruct (Hn5 _ it Hi) as [_ I]. pose proof (HCP _ it LTn Hi) as C. replace (length (qb_items c) + (i - length (qb_items c)))%nat with i in C by lia.
      split; [|exact (items_frame v v3 _ _ W HGI HW FR n it INN (nth_error_In _ _ Hi) I)].
      eapply cell_ok_frame1; [|exact C]. cbn. intros z Hz. apply FR. apply SLOTS. left.
      lia. }
  assert (BMN : batch_mem v3 (emptyb n)).
  { unfold batch_mem. cbn [emptyb qb_addr qb_size qb_items length]. unfold kQuarantineBatchSize in *. split; [exact Cn1|]. split; [exact Cn2|]. split; [cbn; lia|].
    split; [intros z Hz; rewrite FR by (apply SLOTS; right; lia); exact (Hn4 z Hz)|]. intros i it Hi. destruct i; discriminate Hi. }
  assert (LNK : forall b, In b (E ++ D ++ L) -> (E <> [] -> qb_addr b <> last_addr E) -> forall z, qb_addr b <= z < qb_addr b + 8 -> ~ W z).
  { intros b Hb NL z Hz. destruct (ONE b Hb) as (N1 & N2 & Hbo). pose proof (APT b c Hbo INC N1). pose proof (APT b n Hbo INN N2).
    intros [HP|[HP|[NE HP]]]; [lia | lia |]. pose proof (APT b _ Hbo (INL NE) (NL NE)). unfold last_addr in *. lia. }
  assert (EGN : forall b, In b (D ++ c :: n :: L) -> E <> [] -> qb_addr b <> last_addr E).
  { intros b Hb NE EQ. unfold old in ND. rewrite map_app in ND. apply (NoDup_app_disj _ _ (qb_addr b) ND); [rewrite EQ; unfold last_addr; apply in_map; apply In_last; exact NE | apply in_map; exact Hb]. }
  split; [|split; [|split]].
  - apply Forall_forall. intros b Hb. apply in_app_or in Hb as [Hb|Hb].
    + apply in_app_or in Hb as [Hb|[<-|[]]]; [apply BMO; apply in_or_app; left; exact Hb | exact BMN].
    + apply in_app_or in Hb as [Hb|[<-|Hb]]; [apply BMO; apply in_or_app; right; apply in_or_app; left; exact Hb | exact BMC | apply BMO; apply in_or_app; right; apply in_or_app; right; exact Hb].
  - apply qlinks_to_0. destruct (list_eq_nilq E) as [EE|NE].
    + rewrite EE. cbn. split; [exact Cn0 | exact I].
    + apply (qlinks_to_app v3 E [emptyb n] 0); [discriminate | | cbn; split; [exact Cn0 | exact I]].
      unfold hd_addr. cbn [hd emptyb qb_addr]. apply (qlinks_to_relast v v3 E 0 (qb_addr n) NE); [| exact (CE NE) | apply qlinks_to_0; exact HLE].
      intros b z Hb Hz. apply FR. apply (LNK b); [apply in_or_app; left; apply in_removelast_q; exact Hb | | exact Hz].
      intros _ EQ. assert (NDE : NoDup (map qb_addr E)) by (unfold old in ND; rewrite map_app in ND; exact (NoDup_app_l _ _ ND)).
      assert (b = last E qb_dflt) by (apply (NoDup_map_In_inj qb_addr E b _ NDE); [apply in_removelast_q; exact Hb | apply In_last; exact NE | exact EQ]).
      subst b. exact (removelast_not_last E NE NDE Hb).
  - apply qlinks_to_0. apply qlinks_to_0 in HLG.
    destruct (qlinks_to_split v D (c :: n :: L) 0 ltac:(discriminate) HLG) as [LD LC]. cbn [qlinks_to] in LC. destruct LC as (_ & _ & LL).
    apply (qlinks_to_app v3 D (mergeb c n :: L) 0); [discriminate | |].
    + unfold hd_addr in LD |- *. cbn [hd mergeb qb_addr] in LD |- *. apply (links_frame v v3 W D _ FR); [|exact LD]. intros b z Hb Hz.
      apply (LNK b); [apply in_or_app; right; apply in_or_app; left; exact Hb | | exact Hz]. intros NE. apply (EGN b); [apply in_or_app; left; exact Hb | exact NE].
    + cbn [qlinks_to]. split; [cbn [mergeb qb_addr]; destruct L as [|l0 L']; exact Cc0|].
      apply (links_frame v v3 W L 0 FR); [|exact LL]. intros b z Hb Hz.
      apply (LNK b); [apply in_or_app; right; apply in_or_app; right; exact Hb | | exact Hz]. intros NE. apply (EGN b); [apply in_or_app; right; right; right; exact Hb | exact NE].
  - exact (thd_frame v v3 W HW FR HTD).
Qed.

Definition JRM (E glob : list qbatch) (c n : qbatch) (j : nat) : jpredA := ltac2:(tb__ "0|1|
S2eS3S76Q40A1A1S3Sa5A1Sa4S1dVK;VA1;R4R3R2R1A5S1dS1dS84S7bS75S30R4A1A2M0S17VA1;A1VE;Vglob;A4S85G0Vc;Vn;Vj;A4A2S96VA0;Vrho0;R4A3A2A2Lmd;Ltr;Ltp;Lrho;").
Lemma JRM_stable : ltac2:(tb__ "0|1|
S3S14A1M0G0S14S14S6S92S75SaeS56R5R4R3R2R1A5A3Fj;Fn;Fc;Fglob;FE;").
Proof.
  intros E glob c n j rho rho' tp tr md md' Hag Hme (HK & HR & HF).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply (proj2 (proj2 Hag))).
  split; [eapply (kq_stable segsA K HL A1); eauto|]. split; [rewrite Erm; exact HR|]. exact (FRM_stable A0 rho0 rho rho' Hag HF).
Qed.
Lemma JRM_okf : ltac2:(tb__ "0|1|
Sb0OF_;S3S14A1M0G0S14S14S6S1cS91S75R7VK;R1A1A3FA;S91S75R7S56R6R5R4R3R2A5A3F_;Fj;Fn;Fc;Fglob;FE;Fok;").
Proof. intros ok E glob c n j HOK rho tp tr ms md msv' (HK & _). exact (HOK A1 rho tp tr ms md msv' HK). Qed.

Definition TJ : jpredA := ltac2:(tb__ "0|0|
S2eS3S76Q40A1A1S3Sa5A1Sa4S22L_;L_;L_;L_;").
Definition dspec : Type := ltac2:(tb__ "0|0|
S2S2S2S2S2dS0A2S0A2S3S2S2S0S6A2S2dA2A1A2S0A2").
Definition dobj (d : dspec) : sobj := ltac2:(tb__ "0|4|
S2S2S2S2S2dS0A2M0S0A2M1S3S2S2S0S6A2S2dA2A1M2A2M3S0A2S2cLd;Vd;G3S0G3S2cLp;R2G1G2G1S2cLp0;R2G0S0G0S2cLp1;R2S2dS0Sb5R2R1R3R5A4Llo;Lb;X2x1Lhi;Lp1;X2x1Lcs;Lp0;X2x1La;Lp;X2x1").
Definition dcs (d : dspec) : carve_spec := ltac2:(tb__ "0|4|
S2S2S2S2S2dS0A2M0S0A2M1S3S2S2S0S6A2S2dA2A1M2A2M3S0A2S93Ld;Vd;G3S0G3S93Lp;R2G1G2G1S93Lp0;R2G0S0G0S93Lp1;R2S2dS0S7G1G2S7G0S0S7S2dS0R2R1A4R3A4R5A4Llo;Lb;X2x1Lhi;Lp1;X2x1Lcs;Lp0;X2x1La;Lp;X2x1").
Definition dzone (ds : list dspec) (z : Z) : Prop := ltac2:(tb__ "0|4|
S6dS49S49S2S2S2S2S2dS0A2M0S0A2M1S3S2S2S0S6A2S2dA2A1M2A2M3S0A2OLd;R1G3S0G3OLp;R2G1G2G1OLp0;R2G0S0G0OLp1;R2S2dS0S1dS24S23R7R1A2Vz;A2S25Vz;S23R7R3A2A2A2Llo;Lb;X2x1Lhi;Lp1;X2x1Lcs;Lp0;X2x1La;Lp;X2x1Ld;Vds;A3").
Lemma dzone_dec : ltac2:(tb__ "0|1|
S3S49A1S0S20S4fR2R1A2M0S1fG0A1A2Fz;Fds;").
Proof.
  intros ds z. induction ds as [|d r IH]; [right; intros H; inversion H|]. destruct d as [[[[b lo] hi] cs] a].
  destruct (Z_le_dec (a + lo) z) as [L1|L1]; [destruct (Z_lt_dec z (a + hi)) as [L2|L2]|].
  - left. apply List.Exists_cons_hd. lia.
  - destruct IH as [IH|IH]; [left; apply List.Exists_cons_tl; exact IH | right; intros H; inversion H; subst; [lia | exact (IH H1)]].
  - destruct IH as [IH|IH]; [left; apply List.Exists_cons_tl; exact IH | right; intros H; inversion H; subst; [lia | exact (IH H1)]].
Qed.
Lemma map_dcs : ltac2:(tb__ "0|0|
S3S49A1S1eS3S2cA1S71S93S2cS94S71S49S93S63R1A4A4S71S49S2cS4aR1A4A3Fds;").
Proof. intros ds. rewrite map_map. apply map_ext. intros [[[[b lo] hi] cs] a]. reflexivity. Qed.
Lemma dobj_range : ltac2:(tb__ "0|5|
S2eS2dS0S0S3S2S2S0S6A2S2dA2A1M0S0S1eS76Q40M1A1S32R6R5A2S77G1R1A2A3S1dS24Z0R2A2S25R2S27Z2Z3eA2M2A2A2S24S29G2A1R6A2S24R7R6A2S24R7G2A2S1eS2S0S0A2S34RbS4aS7S2S2S2S2dS0A2M3S0A2M4G0A2S0S7G4G0S7G3S0S7S2dS0RaR9A4R8A4R7A4R6A4A1A2S7S0S0S23R6R9A2S23R6R8A2A4A3F_;F_;F_;F_;F_;Fa;Fcs;Fhi;Flo;Fb;Frho;").
Proof. intros rho b lo hi cs a Eb H1 H2 H3 H4. unfold dobj, carved. rewrite obj_range_mk by lia. rewrite Eb, u64_lit by lia. reflexivity. Qed.
Definition diss_cond (rho : valuation) (d : dspec) : Prop := ltac2:(tb__ "0|7|
S2S2S2S2S2dS0A2M0S0A2M1S3S2S2S0S6A2S2dA2A1M2A2M3S0A2OLd;Vd;G3S0G3OLp;R2G1G2G1OLp0;R2G0S0G0OLp1;R2S2dS0S1dS1eS76Q40M4A1S32Vrho;R2A2S77G4R7A2A3S1dS1dS24Z0M5R7A2S25R7S27Z2Z3eA2M6A2A2S1dS24S29G6A1R1A2S1dS24R1R3A2S1dS24R3G6A2S1dS24G5S23R7R1A2A2S1dSb4R1R3R5A3S0S1dS24S23R8R2A2R1A2S25R1S23R8R4A2A2A2S1dS99VA1;R2A2S1fS1dS24Sa8R2A2S25R2Sa7A2A2A1A2F_;Fz;A2A2A2A2A2A2A2Llo;Lb;X2x1Lhi;Lp1;X2x1Lcs;Lp0;X2x1La;Lp;X2x1").
Definition diss_res (rho : valuation) (v3 : bview) (d : dspec) : Prop := ltac2:(tb__ "0|7|
S2S2S2S2S2dS0A2M0S0A2M1S3S2S2S0S6A2M2S2dA2M3A1M4A2M5S0A2OLd;Vd;G5S0G5OLp;R2G1G4G1OLp0;R2G0S0G0OLp1;R2S2dS0S1dS0S6S2dS0S69G3S7G2S2dS7S0S6R4R3A4R2A4R9A3S1eS76Q40M6A1S32Vrho;R3A2S77G6R2A2A3S79Vv3;S7aS23RdR6A2R5R3A3A2F_;F_;Fval;Fe;Fk;Foff;S7cVv3;S23R7R1A2S23R7R3A2A3A2Llo;Lb;X2x1Lhi;Lp1;X2x1Lcs;Lp0;X2x1La;Lp;X2x1").

Definition with_objs (S : sstate) (os : list sobj) : sstate := ltac2:(tb__ "0|0|
S3fS46VS;A1S47VS;A1S44VS;A1S43VS;A1S48VS;A1S4S2cS31VS;A1Vos;A3S33VS;A1S3bVS;A1S45VS;A1A9").

Lemma m_dissolve : ltac2:(tb__ "0|3|
S80S3S2cA1M0S3S49A1S2eS3S76Q40A1M1A1S3Sa5A1M2SafSa4S1eG0S31S7dR8A1A1S4S2cR7S71S49S2cS4aR6A4A3A3S8fS75S4eR9R6R5S7G2Sa2R4Sa3R3R2A2A4A6S72S49S59R7A1R8A3VK;VA1;R8R7R6R4A5S96VA0;Vrho0;R9A3Sb1RaS71S49S2cS4aRbA4Sb3R6R9R7A3A3S2eS1dS8fS75S4eS7eReSb2S7dReA1RdA2A2R1RaS7G2Sa2R9Sa3R8R7A2A4A6S1dVK;VA1;R1RaR9R7A5S1dS96VA0;Vrho0;R1A3S1dS1S1eG1S36R2R1A2S36RcR1A2A3Fi;S1dS0S1fS4fRdR1A2A1S1eSbS76Q8A1A1S7bS75S30R3A1R2A3S7bS75S30RdA1R2A3A3F_;Fz;S72S49S5aRbS7bS75S30R1A1A2A2RcA3A2A2A2A2A2Trho3;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fds;FBASE;FC;").
Proof.
  intros C BASE ds rho tp tr ms md HOBJ HS HD HK HF rho3.
  pose proof (proj1 (proj1 HS)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  assert (AV : Forall (diss_res rho (view segsA (rm rho3))) ds).
  { apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) HD d Hd) as X. destruct d as [[[[b lo] hi] cs] a]. destruct X as (Eb & A1' & L1 & L2 & L3 & L4 & CI & _).
    destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) BASE (map dobj ds) b lo hi cs Hsm HOBJ (in_map dobj ds _ Hd) ltac:(lia) ltac:(lia) ltac:(lia) CI
                ltac:(rewrite Eb, u64_lit by lia; lia) ltac:(rewrite Eb, u64_lit by lia; lia)) as [AVc PRc].
    fold rho3 in AVc, PRc. rewrite Eb, u64_lit in AVc, PRc by lia. split.
    - intros off k e val Hin Ee. exact (av_cell _ a off k e val rho (fun j Hj => AVc off k e j Hin Hj) Ee).
    - exact PRc. }
  assert (INRG : forall x, in_ranges rho (map dobj ds) x -> dzone ds (bv_unsigned x)).
  { intros x (o & Ho & Hz). apply in_map_iff in Ho as (d & <- & Hd). pose proof (proj1 (Forall_forall _ _) HD d Hd) as X. apply List.Exists_exists. exists d. split; [exact Hd|].
    destruct d as [[[[b lo] hi] cs] a]. destruct X as (Eb & A1' & L1 & L2 & L3 & _). rewrite (dobj_range rho b lo hi cs a Eb A1' L1 L2 L3) in Hz. cbn [fst snd] in Hz. exact Hz. }
  destruct (absorb_out rho (map dobj ds) (vms md tp ms) (dzone ds) INRG) as [FR FRrm]. fold rho3 in FR, FRrm.
  destruct (K_FRM_absorb K HL A0 rho0 A1 HQW rho rho3 tp tr md (dzone ds) (dzone_dec ds) ltac:(intros i; reflexivity) ltac:(intros l; reflexivity)) as [HK3 HF3]; try assumption.
  { intros z Hz. left. apply List.Exists_exists in Hz as (d & Hd & Hz). pose proof (proj1 (Forall_forall _ _) HD d Hd) as X. destruct d as [[[[b lo] hi] cs] a].
    destruct X as (_ & _ & _ & _ & _ & _ & _ & HQ). exact (HQ z Hz). }
  { intros z Hz. apply List.Exists_exists in Hz as (d & Hd & Hz). pose proof (proj1 (Forall_forall _ _) AV d Hd) as X. destruct d as [[[[b lo] hi] cs] a].
    destruct X as [_ PR]. destruct (PR z Hz) as [x Hx]. rewrite Hx. discriminate. }
  pose proof (SPA_unobj segsA TJ rho C BASE (map dobj ds) tp tr ms md HOBJ HS (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU.
  split; [exact HU|]. split; [exact HK3|]. split; [exact HF3|]. split; [intros i; reflexivity|]. split; [exact FR | exact AV].
Qed.

Definition carve_cond (rho4 : valuation) (v : bview) (others : list sobj) (d : dspec) : Prop := ltac2:(tb__ "0|b|
S2S2S2S2S2dS0A2M0S0A2M1S3S2S2S0S6A2M2S2dA2M3A1M4A2M5S0A2OLd;Vd;G5S0G5OLp;R2G1G4G1OLp0;R2G0S0G0OLp1;R2S2dS0S1dS1eS76Q40M6A1M7S32Vrho4;R2A2S77G6R7A2A3S1dS1dS24Z0R7A2S25R7S27Z2Z3eA2M8A2A2S1dS24S29G8A1R1A2S1dS24R1R3A2S1dS25R3G8A2S1dS24Z643000S23R7R1A2M9A2S1dS24S23R7R3A2MaG8A2S1dS24GaS1aS17VA1;A1A1A2S1dSb4R1R3R5A3S1dS7cVv;G9GaA3S1dS72G3G3G3OLc;R1G2S2dG2OLp;R2S0S6S21S0S0S1dS1eG7S32Vrho4;R4A2S77G6R1A2A3S79Vv;S7aS23RdR3A2R2R1A3A2A2Lval;A2Lk;Loff;X2x1Le;Lp;X2x1Lc;R5A3S72S2cS2cS40S34Vrho4;R1A2S7S0S0S23R8R2A2S23R8R4A2A4A2Lo';Vothers;A3A2A2A2A2A2A2A2A2A2A2A2Llo;Lb;X2x1Lhi;Lp1;X2x1Lcs;Lp0;X2x1La;Lp;X2x1").
Definition apart_d (d1 d2 : dspec) : Prop := ltac2:(tb__ "0|8|
S2S2S2S2S2dS0A2M0S0A2M1S3S2S2S0S6A2S2dA2A1M2A2M3S0A2M4OLd1;Vd1;G3S0G3OLp;M5R2G1G2G1OLp0;M6R2G0S0G0OLp1;M7R2S2dS0G4OLd2;Vd2;G3S0G5R2G1G2G6R2G0S0G7R2S2dS0S20S24S23RfRbA2S23R7R1A2A2S24S23R7R3A2S23RfR9A2A2A2Ll2;Ls;X2x1Lh2;Lp1;X2x1Ll;Lp0;X2x1La2;Lp;X2x1Ll1;Ls;X2x1Lh1;Lp1;X2x1Ll;Lp0;X2x1La1;Lp;X2x1").

Lemma m_carve : ltac2:(tb__ "0|1|
S90S80S2eS3S76Q40A1A1Sb0S3S49A1S8fS75R6R5R4R3R2A6S1eS3S2S2dS2dA2M0A1S7fR6A1S9G0A1A3S1eScS3cS4dS7dR7A1S71S49S2cS4aR3A4A2A1SdA3S72S49S58R7S7bS75S30R7A1A2S31S7dR8A1A1A3R4A3S6bS49S57R5A3S8fS75RbS7eRaS4dS7dRaA1S71S49S2cS4aR6A4A2A2R9R8R7A6F_;F_;F_;F_;F_;Fds;Fw;Ftp;Frho;FS;FJ;").
Proof.
  intros J S rho tp w ds H HX Hswf HD HP.
  pose proof (SPA_carve_list segsA J rho S tp w (map dcs ds) (ss_next (ax_S S)) H) as X. cbn zeta in X. rewrite map_dcs in X. apply X; clear X.
  - exact Hswf.
  - apply Pos.le_refl.
  - apply Forall_forall. intros k Hk. apply in_map_iff in Hk as (d & <- & Hd). pose proof (proj1 (Forall_forall _ _) HD d Hd) as Y. destruct d as [[[[b lo] hi] cs] a]. cbn [dcs].
    destruct Y as (Eb & A1' & L1 & L2 & L3 & L4 & L5 & _ & CI & PR & CV & _). rewrite Eb, u64_lit by lia.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact CI|]. split; [|split].
    + intros off Hoff. destruct (PR (a + off) ltac:(lia)) as [x Hx]. rewrite view_in in Hx by lia. exact (wok_rd_off_image _ (a + off) x ltac:(lia) Hx).
    + unfold cells_in_view. apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) CV c Hc) as Z1. pose proof (proj1 (Forall_forall _ _) CI c Hc) as Z2.
      destruct c as [[off k] e]. destruct Z1 as (val & Ee & Cc). destruct Z2 as (B1 & B2 & B3). exact (civ_cell rho (rm rho) a off k val e Cc Ee ltac:(lia) ltac:(lia)).
    + intros rr y j Hin. rewrite HX in Hin. destruct Hin.
  - apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d & <- & Hd). pose proof (proj1 (Forall_forall _ _) HD d Hd) as Y. destruct d as [[[[b lo] hi] cs] a].
    destruct Y as (Eb & A1' & L1 & L2 & L3 & _ & _ & _ & _ & _ & _ & DJ). rewrite (dobj_range rho b lo hi cs a Eb A1' L1 L2 ltac:(lia)). exact DJ.
  - clear Hswf H. induction HP as [|d r HF HR IH]; [exact I|]. cbn [map pairwise_disjoint]. apply Forall_cons_iff in HD as [Hd HDr]. split; [|exact (IH HDr)].
    apply Forall_forall. intros o Ho. apply in_map_iff in Ho as (d2 & <- & Hd2). pose proof (proj1 (Forall_forall _ _) HF d2 Hd2) as AP. pose proof (proj1 (Forall_forall _ _) HDr d2 Hd2) as Y2.
    destruct d as [[[[b lo] hi] cs] a]. destruct d2 as [[[[b2 lo2] hi2] cs2] a2]. destruct Hd as (Eb & A1' & L1 & L2 & L3 & _). destruct Y2 as (Eb2 & B1' & M1 & M2 & M3 & _).
    rewrite (dobj_range rho b lo hi cs a Eb A1' L1 L2 ltac:(lia)), (dobj_range rho b2 lo2 hi2 cs2 a2 Eb2 B1' M1 M2 ltac:(lia)). unfold ranges_disjoint. cbn [fst snd]. unfold apart_d in AP. lia.
Qed.

Definition keepN (C : axst) (k : nat) : list sobj := ltac2:(tb__ "0|1|
S73S2cSa1SaS2cS31S7dVC;A1A1M0A2Vk;A2G0A3").
Definition dropN (C : axst) (k : nat) : axst := ltac2:(tb__ "0|0|
S7eVC;Sb2S7dVC;A1S5cVC;Vk;A2A2A2").
Definition addO (C : axst) (os : list sobj) : axst := ltac2:(tb__ "0|0|
S7eVC;S4dS7dVC;A1Vos;A2A2").
Definition addF (C : axst) (F : list sprop) : axst := ltac2:(tb__ "0|0|
Sc6VC;S4S2fS33S7dVC;A1A1VF;A3A2").

Record trans : Type := mkT { t_C : axst; t_k : nat; t_OC : list sobj; t_bs : list positive; t_F : list sprop; t_T : axst; t_M : vmap }.
Definition t_Cd (t : trans) : axst := ltac2:(tb__ "0|0|
S64S4cVt;A1S60Vt;A1A2").
Definition t_Ca (t : trans) : axst := ltac2:(tb__ "0|0|
S62S51Vt;A1S53Vt;A1A2").
Definition t_Cc (t : trans) : axst := ltac2:(tb__ "0|0|
S61S5dVt;A1S52Vt;A1A2").
Definition same_rng (o o' : sobj) : bool := ltac2:(tb__ "0|0|
S8S8S37S38Vo;A1S38Vo';A1A2S37S3aVo;A1S3aVo';A1A2A2S37S39Vo;A1S39Vo';A1A2A2").
Definition FIX9 : list sobj := ltac2:(tb__ "0|1|
S4S2cS4S2cS8dS9S3eA1S8eS8cS8cS8cS8cA4A2S5S2cSbeS3dZ101A1A1S5S2cSbcS9S2cA1M0A3A3A3S4S2cSb8S5S2cSbdS8cS8cS8cS8cA4G0A3A3A3").
Fixpoint forallb2 {X Y} (f : X -> Y -> bool) (l : list X) (k : list Y) : bool :=
  match l, k with [], [] => true | x :: l', y :: k' => f x y && forallb2 f l' k' | _, _ => false end.
Definition t_ok (t : trans) : bool := ltac2:(tb__ "0|8|
S8S8S8S8S8S8S8S8S3S2S2dS2dA2M0A1M1ScLx;S7fS4cVt;A1A1SdG0G1S12Ll;Lp;X3x2Sc4Sc7S54Vt;A1M2A1M3S7dS51Vt;A1M4A1M5A2A2Sc5G3S81G4A1A2A2S6aS1S1S8S8Sc0SaeR1A2S10SbfR1PaA2A1A2S10SbfR1Sb9A2A1A2Lv;G2A3A2S3cS4dG5S53Vt;A1A2A1A2S6aS2fS41S3bS7dS5dVt;A1A1M6A1A1S4S2fS33G6A1S52Vt;A1A3A3A2Sc9S66Vt;A1S5fVt;A1S5eVt;A1A3A2S5bS2cS2cS50S73S2cU9S31G5A1A3M7S73S2cSaS2cG7A2S55A3A5A2S6aS2fS2fS6fS2fS42R1A1S33G5A1A3Lf;Sb6SbaA1A3A2").

Lemma same_rng_range : ltac2:(tb__ "0|0|
S2eS2cS2cS1eScS50R2R1A2SdA3S1eS2S0S0A2S34R4R3A2S34R4R2A2A3F_;Fo';Fo;Frho;").
Proof.
  intros rho o o' H. unfold same_rng in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply sv_eqb_sound in H1, H2, H3. unfold obj_range, obj_lo_of, obj_hi_of. rewrite H1, H2, H3. reflexivity.
Qed.
Lemma fix9_ok : ltac2:(tb__ "0|0|
S2eS3S2cA1S6Sb7VA1;R3A2S72S2fS35R4A1Sb6SbaA1A3S1eScS5bS2cS2cS50R4S73S2cR3S55A3A5SdA3S72S2cS8bR6S1aS17VA1;A1A1A2R5A3F_;F_;F_;Fn;Fl;Frho;").
Proof.
  intros rho l n HT HF. pose proof (OH_fixed A1 rho [] (sw_cells ZQ ZQ ZQ ZQ) (SLit 257) ZQ ZQ ZQ ZQ HT HF) as FX. fold (SW ZQ ZQ ZQ ZQ) in FX. fold FIX9 in FX.
  apply (Forall_firstn _ n) in FX. revert l. induction FX as [|o' r Ho HR IH]; intros l H; destruct l as [|o l']; cbn [forallb2] in H; try discriminate; [constructor|].
  apply andb_prop in H as [H1 H2]. constructor; [|exact (IH l' H2)]. unfold fixed_ok in *. rewrite (same_rng_range rho o o' H1). exact Ho.
Qed.

Lemma m_step : ltac2:(tb__ "0|9|
S68S90S3S49A1M0G0S3S76Q40A1M1A1M2S2eG2S3Sa5A1M3SafSa4S1eScS67RaA1SdA3S92S75SaeRaA3S1eS3S2cA1M4S31S7dS4cRcA1M5A1A1S4S2cS5cG5S60RcA1A2S71S49S2cS4aRaA4M6A3A3S1eG4G6S53RdA1A3S1eS6SaG1RaA2SaS1S54ReA1A2A3S8fS75S4eS4cRfA1RaR9S7G3Sa2R8Sa3R7R6A2A4A6VK;VA1;RbRaR9R7A5S96VA0;Vrho0;RcA3Sb7VA1;RdA2S72S49S59ReA1R11A3Sb1RfS71S49S2cS4aR12A4Sb3RbReRcA3A3S2eSc8R1S6eS1G1S54R15A1R11A4A2S2eVK;VA1;R2R10RfRdA5S96VA0;Vrho0;R3A3S0S1fS4fR17R1A2A1S1eSbS76Q8A1A1S7bS75S30R6A1M7R2A3S7bS75S30R15A1R2A3A3F_;Fz;S72S49S5aR14S7bS75S30R5A1A2A2R17A3S1dR19R6R14R13R11A4S1dS72S49S58R5S7bS75G7A2S74S2cU9S31S7dS51R1aA1A1M8A1A3A3R17A3S1dS6bS49S57R17A3S72S2fS35R5A1S33G8A1A3S72S2fS35R6A1S52R1bA1A3F_;A2A2A2F_;F_;F_;F_;S21S2eS2eS1dS8fS75R17S5fR18A1R1R12S7G3Sa2R11Sa3R10RfA2A4A6S1S2dS69S2S1S2dA2S7S1S2dR2R1A4S5eR1aA1A3S1eG1S36R4R3A2S32R6R2A2A3F_;Fe;Fv;A2Lrho5;A2F_;Trho4;Trho3;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fvals;FdsC;FdsD;FJ';Ft;").
Proof.
  intros t J' dsD dsC vals rho tp tr ms md HOK HST HOBJ HOC HLEN HS HK HF HTOP HDC rho3 rho4 HCONT.
  unfold t_ok in HOK. repeat (apply andb_prop in HOK as [HOK ?]).
  match goal with H : forallb _ (pre_facts DEPTH_R) = true |- _ => rename H into OKPF end.
  match goal with H : forallb2 _ _ _ = true |- _ => rename H into OKFX end.
  match goal with H : entsM _ _ _ = true |- _ => rename H into OKENT end.
  match goal with H : forallb (sprop_below _) _ = true |- _ => rename H into OKBEL end.
  match goal with H : swf _ = true |- _ => rename H into OKSWF end.
  match goal with H : forallb _ (t_bs t) = true |- _ => rename H into OKBS end.
  match goal with H : sv_vars_all _ _ = true |- _ => rename H into OKV2 end.
  match goal with H : state_vars_all _ _ = true |- _ => rename H into OKV1 end.
  assert (HX : ax_X (t_C t) = []) by (destruct (ax_X (t_C t)); [reflexivity | discriminate HOK]).
  destruct (m_dissolve (t_C t) (keepN (t_C t) (t_k t)) dsD rho tp tr ms md HOBJ HS HDC HK HF) as (HU & HK3 & HF3 & RW3 & FR & AV). fold rho3 in HU, HK3, HF3, RW3, FR, AV.
  destruct (HCONT HK3 HF3 FR AV) as (HJ' & CC & AP & HFN).
  assert (H1 : SPA segsA J' (t_Cd t) rho3 tp (tr, mkCfg ms md)) by (split; [exact (proj1 HU) | exact HJ']).
  assert (MF : map fst (combine (t_bs t) vals) = t_bs t).
  { clear - HLEN. revert vals HLEN. induction (t_bs t) as [|b r IH]; intros vals HLEN; destruct vals as [|x vs]; cbn in *; try reflexivity; try discriminate. f_equal. apply IH. lia. }
  assert (H2 : SPA segsA J' (t_Cd t) rho4 tp (tr, mkCfg ms md)).
  { apply (SPA_bindV segsA _ NPRE (t_Cd t) rho3 tp _ _ HX HST); [| rewrite MF; exact OKV1 | rewrite MF; exact OKV2 | exact H1].
    intros v Hv. rewrite MF in Hv. pose proof (proj1 (forallb_forall _ _) OKBS v Hv) as X. apply andb_prop in X as [X _]. apply andb_prop in X as [X _]. apply Pos.leb_le. exact X. }
  pose proof (SPA_facts_hold segsA _ rho4 (t_Cd t) tp _ H2) as HFa.
  assert (HPF : Forall (holds rho4) (pre_facts DEPTH_R)).
  { apply Forall_forall. intros f Hf. pose proof (proj1 (forallb_forall _ _) OKPF f Hf) as X. apply existsb_exists in X as (g & Hg & E). apply sprop_eqb_sound in E. subst g.
    exact (proj1 (Forall_forall _ _) HFa f Hg). }
  assert (OTH : forall i, ~ In i (t_bs t) -> rw rho4 i = rw rho i).
  { intros i Hi. unfold rho4. rewrite rho_sets_other by (rewrite MF; exact Hi). apply RW3. }
  assert (HTOP4 : top_high A1 rho4).
  { unfold top_high in *. rewrite !OTH; [exact HTOP | |]; intros Hi; pose proof (proj1 (forallb_forall _ _) OKBS _ Hi) as X; apply andb_prop in X as [X X2]; apply andb_prop in X as [_ X1];
      [apply negb_true_iff in X2; apply Pos.eqb_neq in X2; congruence | apply negb_true_iff in X1; apply Pos.eqb_neq in X1; congruence]. }
  pose proof (fix9_ok rho4 _ _ HTOP4 HPF OKFX) as FX.
  assert (H3 : SPA segsA J' (t_Ca t) rho4 tp (tr, mkCfg ms md)).
  { unfold t_Ca, addO. rewrite <- HOC. apply (m_carve J' (t_Cd t) rho4 tp _ dsC H2 HX); [rewrite HOC; exact OKSWF | | exact AP].
    apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) CC d Hd) as X. destruct d as [[[[b lo] hi] cs] a]. destruct X as (Eb & A1' & L1 & L2 & L3 & L4 & L5 & ATOP & CI & PR & CV & DJ).
    assert (ERM : rm rho4 = rm rho3) by (unfold rho4; apply rm_rho_sets). unfold carve_cond. rewrite ERM.
    repeat (split; [assumption|]).
    rewrite <- (firstn_skipn 9 (ss_objs (ax_S (t_Cd t)))). apply Forall_app. split; [|exact DJ].
    eapply Forall_impl; [|exact FX]. intros o Ho. apply (fixed_clear rho4 (topG (aa_geom A1)) o _ _ Ho); lia. }
  assert (H4 : SPA segsA J' (t_Cc t) rho4 tp (tr, mkCfg ms md)).
  { unfold t_Cc, addF. apply SPA_refacts; [exact H3 | exact OKBEL |]. intros HF4. apply Forall_app. split; [exact HF4 | apply HFN; exact HFa]. }
  destruct (entM_SPA J' _ (t_T t) (t_M t) rho4 tp _ OKENT HST H4) as (H5 & AG5 & V5 & RM5).
  eexists. split; [exact H5 | exact V5].
Qed.
End MGlue.
