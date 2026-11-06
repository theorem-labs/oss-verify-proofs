(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "leafA"; "entailsA"; "la_state"; "sym_runA"; "ax_setS"; "cell_eqb"; "mkLeafA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "ss_next"; "sprop"; "eval"; "rw"; "sv"; "reg_sv"; "agree_below"; "SVar"; "SLit"; "holds"; "sobj"; "sprop_below"; "ss_objs"; "sv_below"; "rl"; "ss_facts"; "cell"; "ss_lenient"; "SPUle"; "mkCell"; "mkObj"; "ob_cells"; "obj_holds"; "odefault"; "@"; "segs"; "wl_fd"; "D"; "Pre_wl1"; "Pre_wl2"; "CB1"; "CB2"; "@Corelib.Init.Datatypes"; "nat"; "list"; "length"; "bool"; "true"; "Some"; "option"; "pair"; "nil"; "app"; "cons"; "false"; "prod"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "LQA"; "stableA"; "ok_frameA"; "@Stdlib.ZArith.BinInt.Z"; "of_nat"; "add"; "le"; "lt"; "pow"; "to_nat"; "@Corelib.Init.Peano"; "le"; "lt"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.MuslWLA.WLProofA.WL"; "Kw"; "G"; "MSG"; "chw"; "P_of"; "Posts_wl"; "QD"; "TRk"; "eQD"; "Q_wr"; "eQ_wr"; "J'"; "@Corelib.Init.Nat"; "add"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "FdEntry"; "WriteEv"; "FdChannel"; "fd_lookup"; "m_fds"; "MAX_RW_COUNT"; "read_bytes_map"; "read_u64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "triple"; "etriple"; "assn"; "@Stdlib.PArith.BinPos.Pos"; "le"; "lt"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "rho_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.MuslWL"; "sub_idb"; "dlist_of"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "@Corelib.Lists.ListDef"; "firstn"; "map"; "skipn"; "Forall"; "nth"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_read_byte"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "smatch_pendingA"; "ok_pframeA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "vms"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.MuslWLA"; "obA"; "site1A"; "site2A"; "ax_add_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.SysA"; "A_after_write"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "obj_rng"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "dummy_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "RsCut"; "add_fact"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "ax_add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.MuslWLA.Generic"; "ax_add_fact"; "obA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec.SpecConsts"; "max_write_total"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj SymCall SymBytes SymExit Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict Virt StepA SoundA EntailA CompleteA CFGA SysCallA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CfgGlue SysExtra MuslWL.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import SysStepA SysA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Spec Require Import SpecConsts.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Generic.
Variable segs : list Segment.
Variable ok : world -> Prop.

Lemma LQA_elim : ltac2:(tb__ "0|0|
S3dS4aSfS30S3Q40A1A1S30S8A1S66S8SfS6eS8R2R4A3S16R8R7R2A3S64Vsegs;Vok;S3cVsegs;RaSaR4A1R3R7A5R5A4F_;F_;Frho';FL;S64Vsegs;Vok;S3eVsegs;R7R6R5R4R3A6R2A4F_;FQ;Fleaves;Ftp;Frho;Fn;FJ;").
Proof using .
  intros J n rho tp leaves Q H. unfold LQA.
  apply triple_ex; intros L. apply triple_ex; intros rho'.
  apply triple_pure; intros Hin. apply triple_pure; intros Hag.
  eapply triple_conseq; [| intros w Hw; exact Hw | exact (H L rho' Hin Hag)].
  intros w [Hsm Hk]. split; assumption.
Qed.

Lemma runA_tr : ltac2:(tb__ "0|1|
S2fS30S49A1S7S30S8A1M0S3dSfS30S3Q40A1A1S66S0S35G0A1SbVsegs;R8R7R6S33A5S34G0R5A2A3S0S32S21S6R7A1A1S3aA3S40Vsegs;Vok;R6A3S3fVsegs;S10S6R9A1A1R7A3S8SfS6eS8R2RbA3S16S10S6RdA1A1RaR2A3S64Vsegs;Vok;S3cVsegs;RcSaR4A1R3RaA5R9A4F_;F_;Frho';FL;S64Vsegs;Vok;S3cVsegs;R9RbR8R7A5R6A4F_;F_;F_;F_;F_;FQ;Ftp;Frho;FJ;Fleaves;FA;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts A leaves J rho tp Q Hrun Hstrict Hok Hst H.
  eapply triple_seq; [apply triple1_triple; eapply sym_run_soundA; [exact Hrun | exact Hok | exact Hstrict | exact Hst]|].
  apply LQA_elim. exact H.
Qed.

Lemma erunA_tr : ltac2:(tb__ "0|1|
S2fS30S49A1S7S30S8A1M0S3dSfS30S3Q40A1A1S63OF_;S0S35G0A1SbVsegs;R8R7R6S33A5S34G0R5A2A3S0S32S21S6R7A1A1S3aA3S3fVsegs;S10S6R8A1A1R6A3S8SfS6eS8R2RaA3S16S10S6RcA1A1R9R2A3S65Vsegs;S3cVsegs;RbSaR4A1R3R9A5R8A3F_;F_;Frho';FL;S65Vsegs;S3cVsegs;R8RaR7R6A5R5A3F_;F_;F_;F_;FQ;Ftp;Frho;FJ;Fleaves;FA;Fcuts;Ffuel;").
Proof using .
  intros fuel cuts A leaves J rho tp Q Hrun Hstrict Hst H w Hsp.
  destruct (sym_run_completeA segs fuel cuts A leaves J rho tp w Hstrict Hst Hrun Hsp) as (L & rho' & w' & Hin & Hst' & Hag & Hsp').
  destruct (H L rho' Hin Hag w' Hsp') as (w'' & Hst'' & HQ).
  exists w''. split; [eapply wsteps_trans; eauto | exact HQ].
Qed.

Lemma sub_idb_agree : ltac2:(tb__ "0|0|
S6aSfS0S32S6cR2A1S33A3S16P5cR2S6bR2R3A2A3F_;Frho;Fs;").
Proof using .
  intros s rho Hs. split; [|split; [intros l; reflexivity | reflexivity]].
  intros i Hi. cbn [rho_sub rw].
  pose proof (proj1 (forallb_forall _ _) Hs i) as X. cbn beta in X.
  assert (In i (map Pos.of_nat (seq 1 91))) as Hin.
  { apply in_map_iff. exists (Pos.to_nat i). split; [apply Pos2Nat.id|]. apply in_seq. lia. }
  rewrite (sv_eqb_sound _ _ (X Hin)). reflexivity.
Qed.

Lemma SPA_entails_idb : ltac2:(tb__ "0|0|
S3dS7S7S6aSfS30S3Q40A1A1S63S0S32S9R6R5R4A3S33A3S0S32S6cR5A1S33A3S3fVsegs;P5cR9A3S3cVsegs;RaR9R6R5R4A6S3cVsegs;RbR9S6bR7R8A2R6R5A6F_;F_;F_;F_;Fw;Ftp;Frho;Fs;FT;FL;FJ;").
Proof using .
  intros J L T s rho tp w He Hid Hst [Hsm Hk]. split.
  - eapply smatchA_entails; eauto.
  - eapply Hst; [apply sub_idb_agree; exact Hid | apply mat_equiv_refl | exact Hk].
Qed.

Lemma SPA_fact : ltac2:(tb__ "0|0|
S3dS7SfS30S3Q40A1A1S63S11S3cVsegs;R6R5R4R3R2A6S6eS11R2S1fS6R6A1A1A3S19R6R3A2F_;F_;Fp;Fw;Ftp;Frho;FA;FJ;").
Proof using . intros J A rho tp w p [Hsm _] Hin. exact (proj1 (Forall_forall _ _) (smatchA_facts segs rho tp A w Hsm) p Hin). Qed.

Lemma SPpA_fact : ltac2:(tb__ "0|1|
SfS30S3Q40A1A1S7S30S59A1M0S76S5aS11S7aVsegs;R7R6R5S36G0S78R4S79R3R2A2A4A5S6eS11R2S1fS6R6A1A1A3S19R9R3A2F_;F_;Fp;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md p Hsp Hin. exact (MuslWL.SPp_fact segs rho (ax_S A) tr (vms md tp ms) (vmd md) p (smatch_pendingA_sp segs _ _ _ _ _ _ Hsp) Hin).
Qed.

Lemma hdA_fact : ltac2:(tb__ "0|1|
SfS7S11S30S11A1M0S63S3dS30S3Q40A1A1S0G0S1fS6R6A1A1S39S11R5R4A3A3S3cVsegs;R3R7R8R2R4A6S19R9R7A2F_;F_;Ftp;FJ;Fw;FF;Ff;FA;Frho;").
Proof using . intros rho A f F w J tp E Hsp. eapply SPA_fact; [exact Hsp|]. rewrite E. left. reflexivity. Qed.

Definition ax_add_fact (A : axst) (p : sprop) : axst := ltac2:(tb__ "0|0|
ScVA;S85S6VA;A1Vp;A2A2").

Lemma SPA_add1 : ltac2:(tb__ "0|0|
S3dS7SfS30S3Q40A1A1S63S11S3cVsegs;R6R5R4R3R2A6S19R5R2A2S0S32S1bS10S6R7A1A1R3A2S33A3S3cVsegs;R9S87R8R4A2R7R6R5A6F_;F_;F_;Ff;Fw;Ftp;Frho;FA;FJ;").
Proof using .
  intros J A rho tp w f [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] Hf Hb. split; [|exact Hk].
  split; [|split; [exact HMI | split; [exact Hwf | split; [exact Hsh | exact Hhz]]]].
  apply smatch_add_fact; [exact Hsm | exact Hb | exact Hf].
Qed.

Lemma SPA_addn : ltac2:(tb__ "0|0|
S3dS7SfS30S3Q40A1A1S63S30S11A1S3cVsegs;R6R5R4R3R2A6S74S11S19R5A1R2A3S0S32S6fS11S1bS10S6R7A1A1A1R3A3S33A3S3cVsegs;R9S86R4R8A2R7R6R5A6F_;F_;F_;FF;Fw;Ftp;Frho;FA;FJ;").
Proof using .
  intros J A rho tp w F [Hsm Hk] Hf Hb. split; [|exact Hk]. apply smatchA_add_facts; [exact Hsm | exact Hf | exact Hb].
Qed.

Definition obA (A : axst) (i : nat) : sobj := ltac2:(tb__ "0|0|
S75S1aVi;S1cS6VA;A1A1S83A4").

Lemma objsA_hold : ltac2:(tb__ "0|1|
SfS30S3Q40A1A1S7S30S59A1M0S76S5aS2fS7aVsegs;R7R6R5S36G0S78R4S79R3R2A2A4A5S48R2S31S1aS1cS6R6A1A1A2A2S26Vsegs;R9S7cR4R8R5A3S88R7R3A2A4F_;F_;Fi;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof using .
  intros rho tp A tr ms md i Hsp Hi. unfold obA. exact (MuslWL.objs_hold segs rho (ax_S A) tr (vms md tp ms) (vmd md) i (smatch_pendingA_sp segs _ _ _ _ _ _ Hsp) Hi).
Qed.
End Generic.

Record site2A (segs : list Segment) (wl_fd : Z) (A : axst) (e0 l0 : sv) : Prop := mkSite2A {
  s2_len : (4 <= length (ss_objs (ax_S A)))%nat;
  s2_stk : obj_rng (obA A 0) = (SVar 10, SLit 8, SLit 40);
  s2_b1 : obA A 1 = mkObj (SVar 12) (SLit 0) (SVar 13) [] (DList 5);
  s2_b2 : obA A 2 = mkObj (SVar 14) (SLit 0) (SVar 15) [] (DRom 6);
  s2_c8 : existsb (cell_eqb (mkCell (SLit 8) 8 e0)) (ob_cells (obA A 0)) = true;
  s2_c16 : existsb (cell_eqb (mkCell (SLit 16) 8 l0)) (ob_cells (obA A 0)) = true;
  s2_c24 : existsb (cell_eqb (mkCell (SLit 24) 8 (SVar 14))) (ob_cells (obA A 0)) = true;
  s2_c32 : existsb (cell_eqb (mkCell (SLit 32) 8 (SVar 15))) (ob_cells (obA A 0)) = true;
  s2_a1 : reg_sv (ax_S A) 11 = SAlu ALU_ADD (SVar 10) (SLit 8);
  s2_pc : instr_at segs (ss_pc (ax_S A)) = Some Ecall;
  s2_a7 : reg_sv (ax_S A) 17 = SLit 66;
  s2_a0 : reg_sv (ax_S A) 10 = SLit wl_fd;
  s2_a2 : reg_sv (ax_S A) 12 = SLit 2;
  s2_f10a : In (SPUle (SLit 0x7fff7ff00000) (SVar 10)) (ss_facts (ax_S A));
  s2_f10b : In (SPUle (SVar 10) (SLit (2 ^ 47))) (ss_facts (ax_S A));
  s2_f12 : In (SPUle (SVar 12) (SLit (2 ^ 62))) (ss_facts (ax_S A));
  s2_f14 : In (SPUle (SVar 14) (SLit (2 ^ 62))) (ss_facts (ax_S A));

  s2_urng : forall rho, Forall (holds rho) (ss_facts (ax_S A)) ->
      bv_unsigned (rw rho 10) + 40 <= 2 ^ 47
      /\ bv_unsigned (rw rho 12) + bv_unsigned (rw rho 13) <= 2 ^ 47
      /\ bv_unsigned (rw rho 14) + bv_unsigned (rw rho 15) <= 2 ^ 47
}.

Record site1A (segs : list Segment) (wl_fd : Z) (A : axst) (e1 l1 : sv) : Prop := mkSite1A {
  s1_len : (4 <= length (ss_objs (ax_S A)))%nat;
  s1_stk : obj_rng (obA A 0) = (SVar 10, SLit 8, SLit 40);
  s1_b2 : obA A 2 = mkObj (SVar 14) (SLit 0) (SVar 15) [] (DRom 6);
  s1_c24 : existsb (cell_eqb (mkCell (SLit 24) 8 e1)) (ob_cells (obA A 0)) = true;
  s1_c32 : existsb (cell_eqb (mkCell (SLit 32) 8 l1)) (ob_cells (obA A 0)) = true;
  s1_a1 : reg_sv (ax_S A) 11 = SAlu ALU_ADD (SVar 10) (SLit 24);
  s1_pc : instr_at segs (ss_pc (ax_S A)) = Some Ecall;
  s1_a7 : reg_sv (ax_S A) 17 = SLit 66;
  s1_a0 : reg_sv (ax_S A) 10 = SLit wl_fd;
  s1_a2 : reg_sv (ax_S A) 12 = SLit 1;
  s1_f10a : In (SPUle (SLit 0x7fff7ff00000) (SVar 10)) (ss_facts (ax_S A));
  s1_f10b : In (SPUle (SVar 10) (SLit (2 ^ 47))) (ss_facts (ax_S A));
  s1_f14 : In (SPUle (SVar 14) (SLit (2 ^ 62))) (ss_facts (ax_S A));

  s1_urng : forall rho, Forall (holds rho) (ss_facts (ax_S A)) ->
      bv_unsigned (rw rho 10) + 40 <= 2 ^ 47
      /\ bv_unsigned (rw rho 14) + bv_unsigned (rw rho 15) <= 2 ^ 47
}.

Module WLProofA.

Section WL.
  Variable segs : list Segment.
  Variable wl_fd : Z.
  Hypothesis wl_fd_rng : 0 < wl_fd < 2 ^ 32.

  Variables Pre_wl2 PA2 PA2a PA2b CB2 PB2 PB2a PB2b CB1 PB1 D Pre_wl1 PA1 : axst.
  Variables L_PA2a_e L_PA2a_d L_PA2b_e L_PA2b_d L_PB2a_d L_PB2a_e
             L_PB2b_d L_PB2b_e L_PB1_d L_PB1_e L_PA1_e L_PA1_d : axst.
  Variable FUEL : nat.
  Variable cuts_run : list Z.

  Hypothesis PA2_eq : ax_add_facts [SPUle (SVar 92) (SLit (2^28))] (A_after_write Pre_wl2 (reg_sv (ax_S Pre_wl2) 22)) = PA2.
  Hypothesis PA2a_eq : ax_add_fact PA2 (SPNot (SPBranch BC_LTU (SVar 13) (SVar 92))) = PA2a.
  Hypothesis PA2b_eq : ax_add_fact PA2 (SPBranch BC_LTU (SVar 13) (SVar 92)) = PA2b.
  Hypothesis PB2_eq : ax_add_facts [SPUle (SVar 98) (SLit (2^28))] (A_after_write CB2 (reg_sv (ax_S CB2) 22)) = PB2.
  Hypothesis PB2a_eq : ax_add_fact PB2 (SPNot (SPBranch BC_LTU (SVar 93) (SVar 98))) = PB2a.
  Hypothesis PB2b_eq : ax_add_fact PB2 (SPBranch BC_LTU (SVar 93) (SVar 98)) = PB2b.
  Hypothesis PB1_eq : ax_add_facts [SPUle (SVar 100) (SLit (2^28))] (A_after_write CB1 (reg_sv (ax_S CB1) 22)) = PB1.
  Hypothesis PA1_eq : ax_add_facts [SPUle (SVar 92) (SLit (2^28))] (A_after_write Pre_wl1 (reg_sv (ax_S Pre_wl1) 22)) = PA1.

  Hypothesis run_PA2a : sym_runA segs FUEL cuts_run PA2a true = Some [mkLeafA L_PA2a_e RsCut; mkLeafA L_PA2a_d RsCut].
  Hypothesis run_PA2b : sym_runA segs FUEL cuts_run PA2b true = Some [mkLeafA L_PA2b_e RsCut; mkLeafA L_PA2b_d RsCut].
  Hypothesis run_PB2a : sym_runA segs FUEL cuts_run PB2a true = Some [mkLeafA L_PB2a_d RsCut; mkLeafA L_PB2a_e RsCut].
  Hypothesis run_PB2b : sym_runA segs FUEL cuts_run PB2b true = Some [mkLeafA L_PB2b_d RsCut; mkLeafA L_PB2b_e RsCut].
  Hypothesis run_PB1 : sym_runA segs FUEL cuts_run PB1 true = Some [mkLeafA L_PB1_d RsCut; mkLeafA L_PB1_e RsCut].
  Hypothesis run_PA1 : sym_runA segs FUEL cuts_run PA1 true = Some [mkLeafA L_PA1_e RsCut; mkLeafA L_PA1_d RsCut].

  Variables s_PA2a_CB2 s_PB2a_CB2 s_PA2b_CB1 s_PB2b_CB1 s_PB1_CB1 s_PA1_CB1
             s_PA2a_D s_PA2b_D s_PB2a_D s_PB2b_D s_PB1_D s_PA1_D : wsub.
  Hypothesis ent_PA2a_CB2 : entailsA L_PA2a_e CB2 s_PA2a_CB2 = true.
  Hypothesis ent_PB2a_CB2 : entailsA L_PB2a_e CB2 s_PB2a_CB2 = true.
  Hypothesis ent_PA2b_CB1 : entailsA L_PA2b_e CB1 s_PA2b_CB1 = true.
  Hypothesis ent_PB2b_CB1 : entailsA L_PB2b_e CB1 s_PB2b_CB1 = true.
  Hypothesis ent_PB1_CB1 : entailsA L_PB1_e CB1 s_PB1_CB1 = true.
  Hypothesis ent_PA1_CB1 : entailsA L_PA1_e CB1 s_PA1_CB1 = true.
  Hypothesis ent_PA2a_D : entailsA L_PA2a_d D s_PA2a_D = true.
  Hypothesis ent_PA2b_D : entailsA L_PA2b_d D s_PA2b_D = true.
  Hypothesis ent_PB2a_D : entailsA L_PB2a_d D s_PB2a_D = true.
  Hypothesis ent_PB2b_D : entailsA L_PB2b_d D s_PB2b_D = true.
  Hypothesis ent_PB1_D : entailsA L_PB1_d D s_PB1_D = true.
  Hypothesis ent_PA1_D : entailsA L_PA1_d D s_PA1_D = true.
  Hypothesis sv93 :
    wsub_get s_PA2a_CB2 93 = SAlu ALU_SUB (SVar 13) (SVar 92)
    /\ wsub_get s_PB2a_CB2 93 = SAlu ALU_SUB (SVar 93) (SVar 98)
    /\ wsub_get s_PA2b_CB1 93 = SAlu ALU_SUB (SVar 15) (SAlu ALU_SUB (SVar 92) (SVar 13))
    /\ wsub_get s_PB2b_CB1 93 = SAlu ALU_SUB (SVar 15) (SAlu ALU_SUB (SVar 98) (SVar 93))
    /\ wsub_get s_PB1_CB1 93 = SAlu ALU_SUB (SVar 93) (SVar 100)
    /\ wsub_get s_PA1_CB1 93 = SAlu ALU_SUB (SVar 15) (SVar 92).
  Hypothesis subs_id :
    forallb sub_idb
      [s_PA2a_CB2; s_PB2a_CB2; s_PA2b_CB1; s_PB2b_CB1; s_PB1_CB1; s_PA1_CB1;
       s_PA2a_D; s_PA2b_D; s_PB2a_D; s_PB2b_D; s_PB1_D; s_PA1_D] = true.
  Hypothesis cert_misc :
    ss_next (ax_S CB2) = 98%positive /\ reg_sv (ax_S CB2) 22 = SAlu ALU_ADD (SVar 93) (SVar 15)
    /\ ss_next (ax_S CB1) = 100%positive /\ reg_sv (ax_S CB1) 22 = SVar 93
    /\ ss_next (ax_S Pre_wl2) = 92%positive /\ reg_sv (ax_S Pre_wl2) 22 = SAlu ALU_ADD (SVar 13) (SVar 15)
    /\ ss_next (ax_S Pre_wl1) = 92%positive /\ reg_sv (ax_S Pre_wl1) 22 = SVar 15
    /\ ss_facts (ax_S L_PB2a_d) = SPBranch BC_EQ (SVar 98) (SAlu ALU_ADD (SVar 93) (SVar 15)) :: ss_facts (ax_S PB2a)
    /\ ss_facts (ax_S L_PB2a_e) = SPNot (SPBranch BC_EQ (SVar 98) (SAlu ALU_ADD (SVar 93) (SVar 15))) :: ss_facts (ax_S PB2a)
    /\ ss_facts (ax_S L_PB2b_d) = SPBranch BC_EQ (SVar 98) (SAlu ALU_ADD (SVar 93) (SVar 15)) :: ss_facts (ax_S PB2b)
    /\ ss_facts (ax_S L_PB2b_e) = SPNot (SPBranch BC_EQ (SVar 98) (SAlu ALU_ADD (SVar 93) (SVar 15))) :: ss_facts (ax_S PB2b)
    /\ ss_facts (ax_S L_PB1_d) = SPBranch BC_EQ (SVar 100) (SVar 93) :: ss_facts (ax_S PB1)
    /\ ss_facts (ax_S L_PB1_e) = SPNot (SPBranch BC_EQ (SVar 100) (SVar 93)) :: ss_facts (ax_S PB1)
    /\ ss_facts (ax_S L_PA2a_d) = SPNot (SPBranch BC_NE (SVar 92) (SAlu ALU_ADD (SVar 13) (SVar 15))) :: ss_facts (ax_S PA2a)
    /\ ss_facts (ax_S L_PA2a_e) = SPBranch BC_NE (SVar 92) (SAlu ALU_ADD (SVar 13) (SVar 15)) :: ss_facts (ax_S PA2a)
    /\ ss_facts (ax_S L_PA2b_d) = SPNot (SPBranch BC_NE (SVar 92) (SAlu ALU_ADD (SVar 13) (SVar 15))) :: ss_facts (ax_S PA2b)
    /\ ss_facts (ax_S L_PA2b_e) = SPBranch BC_NE (SVar 92) (SAlu ALU_ADD (SVar 13) (SVar 15)) :: ss_facts (ax_S PA2b)
    /\ ss_facts (ax_S L_PA1_d) = SPNot (SPBranch BC_NE (SVar 92) (SVar 15)) :: ss_facts (ax_S PA1)
    /\ ss_facts (ax_S L_PA1_e) = SPBranch BC_NE (SVar 92) (SVar 15) :: ss_facts (ax_S PA1).
  Hypothesis cert_runs :
    ss_next (ax_S PA2a) = 93%positive /\ ss_next (ax_S PA2b) = 93%positive /\ ss_next (ax_S PB2a) = 99%positive
    /\ ss_next (ax_S PB2b) = 99%positive /\ ss_next (ax_S PB1) = 101%positive /\ ss_next (ax_S PA1) = 93%positive
    /\ ss_lenient (ax_S PA2a) = false /\ ss_lenient (ax_S PA2b) = false /\ ss_lenient (ax_S PB2a) = false
    /\ ss_lenient (ax_S PB2b) = false /\ ss_lenient (ax_S PB1) = false /\ ss_lenient (ax_S PA1) = false.
  Hypothesis cert_pre :
    sv_below 92 (reg_sv (ax_S Pre_wl2) 22) = true /\ sv_below 92 (reg_sv (ax_S Pre_wl1) 22) = true
    /\ sv_below 98 (reg_sv (ax_S CB2) 22) = true /\ sv_below 100 (reg_sv (ax_S CB1) 22) = true
    /\ In (SPUle (SVar 12) (SLit (2 ^ 62))) (ss_facts (ax_S Pre_wl2)) /\ In (SPUle (SVar 14) (SLit (2 ^ 62))) (ss_facts (ax_S Pre_wl1)).
  Hypothesis site_Pre_wl2 : site2A segs wl_fd Pre_wl2 (SVar 12) (SVar 13).
  Hypothesis site_CB2 : site2A segs wl_fd CB2 (SAlu ALU_SUB (SAlu ALU_ADD (SVar 12) (SVar 13)) (SVar 93)) (SVar 93).
  Hypothesis site_Pre_wl1 : site1A segs wl_fd Pre_wl1 (SVar 14) (SVar 15).
  Hypothesis site_CB1 : site1A segs wl_fd CB1 (SAlu ALU_SUB (SAlu ALU_ADD (SVar 14) (SVar 15)) (SVar 93)) (SVar 93).

Variable ok : world -> Prop.
Variable J : jpredA.
Variable rho0 : valuation.
Variable tp0 : list word.
Variables bs1 bs2 : list byte.

Definition MSG : list byte := bs1 ++ bs2.
Definition chw : word := Z_to_bv 64 wl_fd.
Definition TRk (k : nat) : list event := ltac2:(tb__ "0|1|
S72S3Q8A1M0S59S5cS4eA1S71G0Vk;S4dA3A4").

Definition Kw (k : nat) : jpredA := ltac2:(tb__ "0|1|
SfS30S3Q40A1A1S30S59A1M0S5aS2G0G0S1VJ;R5R4R1R2A4S0G0R3S38S59R1S52Vk;A1A3A3A2Ltr0;A2Lmd;Ltr;Ltp;Lrho;").
Definition Posts_wl : list leafA := ltac2:(tb__ "0|0|
S39S8SeS2aS84A2S37S8A1A3").

Hypothesis Hrl5 : rl rho0 5 = bs1.
Hypothesis Hrl6 : rl rho0 6 = bs2.
Hypothesis HU13 : ltac2:(tb__ "0|0|
S0S49S4Q40S13Vrho0;PdA2A2S41S31S3Q8A1Vbs1;A2A1A3").
Hypothesis HU15 : ltac2:(tb__ "0|0|
S0S49S4Q40S13Vrho0;PfA2A2S41S31S3Q8A1Vbs2;A2A1A3").
Hypothesis Hmax : ltac2:(tb__ "0|0|
S43S41S31S3Q8A1S4dA2A1S89A2").
Hypothesis HstJ : stableA segs 92 J.
Hypothesis HokK : ltac2:(tb__ "0|0|
S2fS40S28Vok;S4bR1A1A3Fk;").
Hypothesis HokP : ltac2:(tb__ "0|0|
S2fS7bS28Vok;S4bR1A1A3Fk;").
Hypothesis Hfd : ltac2:(tb__ "0|0|
SfS30S3Q40A1A1S30S59A1S5aVJ;R4R3R2R1A4S0S35S5bA1S5eS5fR2A1S4eA2S34S5bS5dS4eA1A2A3F_;Fmd;Ftr;Ftp;Frho;").

Lemma MSG_len : ltac2:(tb__ "0|1|
S0S2fS31S3Q8A1M0S4dA2S57S31G0Vbs1;A2S31G0Vbs2;A2A2A3").
Proof using . unfold MSG. rewrite length_app. reflexivity. Qed.

Lemma rwmax : ltac2:(tb__ "0|1|
S1S43S41S31S3Q8A1S4dA2A1M0S60A2S43G0S45Z2Z12A2A2A2").
Proof using Hmax cert_misc cert_runs. pose proof max_write_total_le_rw_count_clamp. pose proof max_write_total_eq_2_18. lia. Qed.

Lemma Kw_stable : ltac2:(tb__ "0|0|
S2fS4aS67P5cR1A2S3fS28R2S4bR3A1A3F_;Fn;Fk;").
Proof using HstJ.
  intros k n Hn rho rho' tp tr md md' Hag Hme (tr0 & HJ & ->). exists tr0. split; [|reflexivity].
  eapply (stableA_mono segs 92 n J Hn HstJ); eauto.
Qed.

Definition G (rho : valuation) : Prop := agree_below 92 rho0 rho.
Lemma G_agree : ltac2:(tb__ "0|1|
S4aSfSfS16R3R2R1A3S67P5cR4A2S4cR4A1M0G0F_;F_;F_;Frho';Frho;Fn;").
Proof using .
  intros n rho rho' Hag Hn HG. eapply agree_below_trans; [exact HG|].
  eapply agree_below_le; [exact Hn|exact Hag].
Qed.
Lemma G_sub : ltac2:(tb__ "0|0|
S6aSfS0S32S6cR2A1S33A3S4cR2A1S4cS6bR3R4A2A1F_;F_;Frho;Fs;").
Proof using bs1 bs2.
  intros s rho Hs HG. eapply agree_below_trans; [exact HG | apply sub_idb_agree; exact Hs].
Qed.
Lemma G_rw : ltac2:(tb__ "0|0|
SfS4aS4cR2A1S68R2P5cA2S0S3Q40A1S13R4R3A2S13Vrho0;R3A2A3F_;F_;Fi;Frho;").
Proof using . intros rho i (Hw & _ & _) Hi. symmetry. apply Hw. exact Hi. Qed.
Lemma G_rl : ltac2:(tb__ "0|0|
SfS4aS4cR2A1S0S30S3Q8A1A1S1eR3R2A2S1eVrho0;R2A2A3F_;Fl;Frho;").
Proof using . intros rho l (_ & Hl & _). symmetry. apply Hl. Qed.
Lemma G13 : ltac2:(tb__ "0|0|
SfS4cR1A1S0S49S4Q40S12R2S17PdA1A2A2S41S31S3Q8A1Vbs1;A2A1A3F_;Frho;").
Proof using HU13 bs2 cert_misc cert_runs. intros rho HG. cbn [eval]. rewrite (G_rw rho 13 HG) by lia. exact HU13. Qed.
Lemma G15 : ltac2:(tb__ "0|0|
SfS4cR1A1S0S49S4Q40S12R2S17PfA1A2A2S41S31S3Q8A1Vbs2;A2A1A3F_;Frho;").
Proof using HU15 bs1 cert_misc cert_runs. intros rho HG. cbn [eval]. rewrite (G_rw rho 15 HG) by lia. exact HU15. Qed.

Lemma Kw_fd : ltac2:(tb__ "0|0|
S2fSfS30S3Q40A1A1S30S59A1S5aS4bR5R4R3R2R1A5S0S35S5bA1S5eS5fR2A1S4eA2S34S5bS5dS4eA1A2A3F_;Fmd;Ftr;Ftp;Frho;Fk;").
Proof using Hfd. intros k rho tp tr md (tr0 & Hk & _). exact (Hfd rho tp tr0 md Hk). Qed.

Lemma firstn_add_skipn : forall {T} (l : list T) n k, firstn n l ++ firstn k (skipn n l) = firstn (n + k) l.
Proof using .
  intros T l n k. revert l. induction n as [|n IH]; intros l; [reflexivity|].
  destruct l as [|x l]; cbn; [rewrite firstn_nil; reflexivity|]. rewrite IH. reflexivity.
Qed.
Lemma TRk_app : ltac2:(tb__ "0|1|
S2fS2fS0S30S59A1S38S59S52R2A1S72S3Q8A1M0S59S5cS4eA1S71G0R1S73G0R2S4dA3A3A4A3S52S57R2R1A2A1A3Fk;Fn;").
Proof using . intros n k. unfold TRk. rewrite <- map_app, firstn_add_skipn. reflexivity. Qed.
Lemma Kw_step : ltac2:(tb__ "0|1|
S2fS2fSfS30S3Q40A1A1S30S59A1S5aS4bR6R4R3R2R1A5S4bS57R7R6A2R5R4S38S59R3S72S3Q8A1M0S59S5cS4eA1S71G0R6S73G0R7S4dA3A3A4A3R2A5F_;Fmd;Ftr;Ftp;Frho;Fk;Fn;").
Proof using . intros n k rho tp tr md (tr0 & Hk & ->). exists tr0. split; [exact Hk|]. rewrite <- app_assoc, TRk_app. reflexivity. Qed.

Lemma wl_fd_u : 0 <= wl_fd < 2 ^ 64.
Proof using bs1 bs2 cert_misc cert_runs wl_fd_rng. pose proof wl_fd_rng. lia. Qed.

Lemma iov_field : ltac2:(tb__ "0|7|
SfS7S30S59A1M0S76S5aS49S14S3Q40M1A1M2S7aS28R8Vtp0;R7S36G0S78R6S79R5R4A2A4A5S47U4S31S1aS1cS6R8A1A1A2A2S0S3bS3bS14S14A2M3S14A2S82S7dR9U0M4A2A1S36G3S14S36S14S14S17PaM5A1S18Z8M6A1A4S18Z28A1A4A3S0S32S70S20SdS23S18R6A1G6R5A3A1S25S7dRaG4A2A1A3S33A3S1S43Z0R7A2S44R7Z40A2A2S0S49S4G1R6A2S42S4G1S13RdG5A2A2R8A2A3S0S35G2A1S62S77S7cRaVtp0;RbA3A1R7A2S34G2S12ReR8A2A2A3F_;F_;F_;F_;F_;F_;Fa;Fv;Foff;Fmd;Fms;Ftr;FA;Frho;").
Proof using bs1 bs2 cert_misc cert_runs.
  intros rho A tr ms md off v a Hsp Hlen Hrng Hc Hoff Ha.
  pose proof (objsA_hold segs rho tp0 A tr ms md 0 Hsp ltac:(lia)) as H0.
  unfold obj_rng in Hrng. injection Hrng as Hb Hlo Hhi.
  apply (cell_read_u64 segs rho (vms md tp0 ms) (obA A 0) (SLit off) v a H0 (In_cellb _ _ Hc)).
  rewrite Hb. change (eval rho (SVar 10)) with (rw rho 10). rewrite soff_lit_small by lia. lia.
Qed.

Lemma list_read : ltac2:(tb__ "0|7|
S27SfS7S30S59A1M0S76S5aS2fS4aS4aS4aS49S2fS3Q40M1A1M2G2S7aS28RdVtp0;RcS36G0S78RbS79RaR9A2A4A5S48R9S31S1aS1cS6RdA1A1A2A2S0S1aS7dReRaA2S24S17R9A1S18Z0M3A1S17R8A1S37S20A1R10A5A3S0S35S4aA1S6dR11A1S34S4aR8A2A3S43G3R8A2S43S42R9S41R8A1A2S4G1S13R12RbA2A2A2S44S4G1S13R13RcA2A2S45Z2Z3eA2A2S0S49S4G1R9A2M4S42S4G1S13R14ReA2A2RbA2A3S0S49G4S41RbA1A3S0S35S30S3Q8A1M5A1M6A1S61S77S7cR12Vtp0;R13A3A1RbRaA3S34G6S71G5RcS73G5S46RdA1S1eR16ReA2A3A3A2A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Flen;Fa;Fn;Foff;Fl;Fhi;Fb;Fi;Fmd;Fms;Ftr;FA;Frho;Fd;").
Proof using bs1 bs2 cert_misc cert_runs.
  intros d rho A tr ms md i b hi l off n a len Hsp Hi Hob Hd Hoff Hn Hhi Ha Hl.
  pose proof (objsA_hold segs rho tp0 A tr ms md i Hsp Hi) as H. rewrite Hob in H.
  rewrite (listish_obj_read_bytes_map segs rho (vms md tp0 ms) _ l n off a len H Hd eq_refl).
  - unfold obj_lo_of. cbn [ob_lo]. rewrite soff_lit_small by lia. rewrite Z.sub_0_r. reflexivity.
  - unfold obj_lo_of. cbn [ob_lo]. rewrite soff_lit_small by lia. lia.
  - unfold obj_hi_of. cbn [ob_hi]. rewrite soff_snorm. unfold U. change (eval rho (SVar hi)) with (rw rho hi).
    rewrite snorm_id; [lia|]. unfold smin, smax. pose proof (urange (rw rho hi)). lia.
  - cbn [ob_base]. change (eval rho (SVar b)) with (rw rho b). lia.
  - exact Hl.
Qed.

Definition Q_wr (A : axst) (e : sv) (n len : nat) (rho : valuation) : assn := ltac2:(tb__ "0|2|
S63S2SfSfS2S2fS2fS1S4cR2A1S1S16S10S6VA;A1A1M0Vrho;R2A3S1S0S3Q40M1A1S13R2G0A2S5G1S41R1A1A2A3S1S1S47U1R1A2S47R1Vlen;A2A2S3cS28S4bS57Vn;R1A2A1S81VA;Ve;A2R2Vtp0;R3A6A2A2A2A2Lk;A2Lrho';A2Lw;").

Definition J' (A : axst) (n len : nat) : jpredA := ltac2:(tb__ "0|2|
SfS30S3Q40M0A1M1A1S30S59A1S5aS2S2fS2fS1S0G1S13R5S10S6VA;A1A1A2S5G0S41R1A1A2A3S1S1S47U1R1A2S47R1Vlen;A2A2S4bS57Vn;R1A2R5R4R3R2A5A2A2Lk;A2Lmd;Ltr;Ltp;Lr;").

Lemma J'_stable : ltac2:(tb__ "0|0|
S7S2fS2fS67P5cS10S6R3A1A1A2S3fS28S69S10S6R4A1A1A1S56R4R3R2A3A3F_;Flen;Fn;FA;").
Proof using HstJ cert_misc cert_runs.
  intros A n len Hn rho rho' tp tr md md' Hag Hme (k & Hk & Hkb & HK). exists k.
  split; [rewrite <- (proj1 Hag (ss_next (ax_S A)) ltac:(lia)); exact Hk|]. split; [exact Hkb|].
  eapply (Kw_stable (n + k) (Pos.succ (ss_next (ax_S A)))); [lia | exact Hag | exact Hme | exact HK].
Qed.

Lemma writev2 : ltac2:(tb__ "0|7|
S7S14S14SfS2fS7fS28S29R5R4R3A5S4cR3A1S67P5cS10S6R7A1A1A2S0S32S1dS10S6R8A1M0A1S15G0Z16M1A2A2S33A3S47R5S31S3Q8A1M2Vbs1;A2M3A2S47U1S57R6S31G2Vbs2;A2M4A2A2S0S49S4Q40M5S12R8R9A2A2S41R7A1A3S0S49S4G5S12R9RbA2A2S42S4G5S13R9PcA2A2S41S58G3R8A2A1A2A3S0S49S4G5S12RaS15S6RdA1G1A2A2A2S41S57R9G4A2A1A3S64S28Vok;S3cS28S4bS58G3RaA2M6A1ReRbVtp0;A5S54ReS15S6ReA1G1A2G6S57RaG4A2RbA5A4F_;F_;F_;F_;F_;F_;F_;F_;F_;FL0;Frho;Fl0;Fe0;FA;").
Proof using HU13 HU15 Hfd Hmax HokK HokP Hrl5 Hrl6 HstJ cert_misc cert_runs wl_fd_rng.
  intros A e0 l0 rho L0 HS HG Hn He HL0 H1 Hl0 He0 H22.
  destruct HS as [Hlen Hrng Hb1 Hb2 C8 C16 C24 C32 R11 Hi H17 H10 H12 F10a F10b F12 F14 UR].
  pose proof wl_fd_u as FD.
  set (n := (length bs1 - L0)%nat).
  assert (Hbs : length (skipn n bs1 ++ bs2) = (L0 + length bs2)%nat) by (rewrite length_app, length_skipn; lia).
  apply triple1_triple.
  eapply triple1_conseq; [intros w Hw; exact Hw | |
    eapply (triple1_writev2A segs ok (Kw n) (J' A n (L0 + length bs2)) A rho tp0 wl_fd (skipn n bs1) bs2 (reg_sv (ax_S A) 22));
      [ apply HokK
      | apply HokP
      | apply Kw_stable; exact Hn
      | apply J'_stable; exact Hn
      | exact Hi | exact H17 | exact H10 | exact H12 | exact wl_fd_rng | rewrite Hbs; pose proof rwmax as RWM; rewrite MSG_len in RWM; lia | exact He | | ]].
  - intros w (rho' & Hag & Hsm & (k & Hk & Hkb & HK)). exists rho', k.
    split; [exact (G_agree _ _ _ Hag Hn HG)|]. split; [exact Hag|]. split; [exact Hk|]. split; [exact Hkb|].
    split; [exact Hsm | exact HK].
  - intros rho' tr md k Hag Hk HK Hkb. split; [exact (Kw_fd _ _ _ _ _ HK)|]. exists k. split; [exact Hk|].
    split; [rewrite Hbs in Hkb; exact Hkb|].
    replace (skipn n bs1 ++ bs2) with (skipn n MSG) by (unfold MSG; rewrite skipn_app; replace (n - length bs1)%nat with 0%nat by lia; reflexivity).
    apply Kw_step. eapply (Kw_stable n (ss_next (ax_S A)) Hn); [exact Hag | apply mat_equiv_refl | exact HK].
  - intros tr ms md Hsp HK.
    pose proof (SPpA_fact segs _ _ _ _ _ _ _ Hsp F10a) as A1. pose proof (SPpA_fact segs _ _ _ _ _ _ _ Hsp F10b) as A2.
    pose proof (SPpA_fact segs _ _ _ _ _ _ _ Hsp F12) as A3. pose proof (SPpA_fact segs _ _ _ _ _ _ _ Hsp F14) as A4.
    cbn [holds eval] in A1, A2, A3, A4. rewrite !u64_lit in A1, A2, A3, A4 by lia.
    change (eval rho (SVar 10)) with (rw rho 10) in *. change (eval rho (SVar 12)) with (rw rho 12) in *. change (eval rho (SVar 14)) with (rw rho 14) in *.
    pose proof (G13 rho HG) as V13. pose proof (G15 rho HG) as V15. cbn [eval] in V13, V15.
    assert (A0 : bv_unsigned (eval rho (reg_sv (ax_S A) 11)) = bv_unsigned (rw rho 10) + 8).
    { rewrite R11. apply (U_addc rho (SVar 10) 8 (bv_unsigned (rw rho 10))); [reflexivity | lia | lia]. }
    assert (A16 : bv_unsigned (eval rho (reg_sv (ax_S A) 11) + 16)%bv = bv_unsigned (rw rho 10) + 24) by (rewrite (U_bvadd _ _ _ _ A0 u16) by lia; lia).
    exists (eval rho e0), (eval rho l0), (eval rho (SVar 14)), (eval rho (SVar 15)).
    split; [eapply (iov_field rho A tr ms md 8); [exact Hsp | exact Hlen | exact Hrng | exact C8 | lia | lia]|].
    split; [eapply (iov_field rho A tr ms md 16); [exact Hsp | exact Hlen | exact Hrng | exact C16 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
    split; [eapply (iov_field rho A tr ms md 24); [exact Hsp | exact Hlen | exact Hrng | exact C24 | lia | lia]|].
    split; [eapply (iov_field rho A tr ms md 32); [exact Hsp | exact Hlen | exact Hrng | exact C32 | lia | rewrite (U_bvadd _ _ _ _ A16 u8) by lia; lia]|].
    split.
    { pose proof rwmax as HM. rewrite MSG_len in HM.
      rewrite (list_read (DList 5) rho A tr ms md 1 12 13 5 (Z.of_nat n) L0 (eval rho e0) (eval rho l0) Hsp ltac:(lia) Hb1 eq_refl ltac:(lia) ltac:(rewrite V13; lia) ltac:(rewrite V13; lia) He0 Hl0).
      f_equal. rewrite Nat2Z.id, (G_rl rho 5 HG), Hrl5. apply firstn_all2. rewrite length_skipn. lia. }
    split.
    { pose proof rwmax as HM. rewrite MSG_len in HM.
      rewrite (list_read (DRom 6) rho A tr ms md 2 14 15 6 0 (length bs2) (eval rho (SVar 14)) (eval rho (SVar 15)) Hsp ltac:(lia) Hb2 eq_refl ltac:(lia) ltac:(rewrite V15; lia) ltac:(rewrite V15; lia) ltac:(cbn [eval]; lia) V15).
      f_equal. cbn [Z.to_nat skipn]. rewrite (G_rl rho 6 HG), Hrl6. apply firstn_all. }
    destruct (UR rho (smatch_pendingA_facts segs _ _ _ _ Hsp)) as (U10 & U12 & U14).
    change (eval rho (SVar 14)) with (rw rho 14). change (eval rho (SVar 15)) with (rw rho 15).
    rewrite task_size_val. split; [rewrite H22, Hbs; reflexivity|]. split; [lia|]. split; [|exact U14].
    rewrite He0, Hl0. rewrite V13 in U12. lia.
Qed.

Lemma writev1 : ltac2:(tb__ "0|5|
S7S14S14SfS2fS2fS7eS28S29R6R5R4A5S4cR4A1S67P5cS10S6R8A1A1A2S0S32S1dS10S6R9A1M0A1S15G0Z16M1A2A2S33A3S1S47U1R6A2S47R6S31S3Q8A1M2Vbs2;A2M3A2A2S0S2fR6S57S31G2Vbs1;A2S58G3R7A2A2A3S0S49S4Q40M4S12R9RaA2A2S41R8A1A3S0S49S4G4S12RaRcA2A2S42S4G4S13RaPeA2A2S41S58G3R9A2A1A2A3S0S49S4G4S12RbS15S6ReA1G1A2A2A2S41RaA1A3S64S28Vok;S3cS28S4bRaA1RfRcVtp0;A5S54RfS15S6RfA1G1A2RaRbRcA5A4F_;F_;F_;F_;F_;F_;F_;F_;F_;Fn0;FR;Frho;Fl1;Fe1;FA;").
Proof using HU15 Hfd Hmax HokK HokP Hrl6 HstJ cert_misc cert_runs wl_fd_rng.
  intros A e1 l1 rho R n0 HS HG Hn He HR Hn0 Hl1 He1 H22.
  destruct HS as [Hlen Hrng Hb2 C24 C32 R11 Hi H17 H10 H12 F10a F10b F14 UR].
  pose proof wl_fd_u as FD.
  assert (Hbs : length (skipn (length bs2 - R) bs2) = R) by (rewrite length_skipn; lia).
  apply triple1_triple.
  eapply triple1_conseq; [intros w Hw; exact Hw | |
    eapply (triple1_writev1A segs ok (Kw n0) (J' A n0 R) A rho tp0 wl_fd (skipn (length bs2 - R) bs2) (reg_sv (ax_S A) 22));
      [ apply HokK
      | apply HokP
      | apply Kw_stable; exact Hn
      | apply J'_stable; exact Hn
      | exact Hi | exact H17 | exact H10 | exact H12 | exact wl_fd_rng | rewrite Hbs; pose proof rwmax as RWM; rewrite MSG_len in RWM; lia | exact He | | ]].
  - intros w (rho' & Hag & Hsm & (k & Hk & Hkb & HK)). exists rho', k.
    split; [exact (G_agree _ _ _ Hag Hn HG)|]. split; [exact Hag|]. split; [exact Hk|]. split; [exact Hkb|].
    split; [exact Hsm | exact HK].
  - intros rho' tr md k Hag Hk HK Hkb. split; [exact (Kw_fd _ _ _ _ _ HK)|]. exists k. split; [exact Hk|].
    split; [rewrite Hbs in Hkb; exact Hkb|].
    replace (skipn (length bs2 - R) bs2) with (skipn n0 MSG) by (unfold MSG; rewrite skipn_app, skipn_all2 by lia; cbn [app]; f_equal; lia).
    apply Kw_step. eapply (Kw_stable n0 (ss_next (ax_S A)) Hn); [exact Hag | apply mat_equiv_refl | exact HK].
  - intros tr ms md Hsp HK.
    pose proof (SPpA_fact segs _ _ _ _ _ _ _ Hsp F10a) as A1. pose proof (SPpA_fact segs _ _ _ _ _ _ _ Hsp F10b) as A2.
    pose proof (SPpA_fact segs _ _ _ _ _ _ _ Hsp F14) as A4.
    cbn [holds eval] in A1, A2, A4. rewrite !u64_lit in A1, A2, A4 by lia.
    change (eval rho (SVar 10)) with (rw rho 10) in *. change (eval rho (SVar 14)) with (rw rho 14) in *.
    pose proof (G15 rho HG) as V15. cbn [eval] in V15.
    assert (A0 : bv_unsigned (eval rho (reg_sv (ax_S A) 11)) = bv_unsigned (rw rho 10) + 24).
    { rewrite R11. apply (U_addc rho (SVar 10) 24 (bv_unsigned (rw rho 10))); [reflexivity | lia | lia]. }
    exists (eval rho e1), (eval rho l1).
    split; [eapply (iov_field rho A tr ms md 24); [exact Hsp | exact Hlen | exact Hrng | exact C24 | lia | lia]|].
    split; [eapply (iov_field rho A tr ms md 32); [exact Hsp | exact Hlen | exact Hrng | exact C32 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
    split.
    { pose proof rwmax as HM. rewrite MSG_len in HM.
      rewrite (list_read (DRom 6) rho A tr ms md 2 14 15 6 (Z.of_nat (length bs2 - R)) R (eval rho e1) (eval rho l1) Hsp ltac:(lia) Hb2 eq_refl ltac:(lia) ltac:(rewrite V15; lia) ltac:(rewrite V15; lia) He1 Hl1).
      f_equal. rewrite Nat2Z.id, (G_rl rho 6 HG), Hrl6. apply firstn_all2. rewrite length_skipn. lia. }
    destruct (UR rho (smatch_pendingA_facts segs _ _ _ _ Hsp)) as (U10 & U14).
    rewrite task_size_val. split; [rewrite H22, Hbs; reflexivity|]. split; [lia|].
    rewrite He1, Hl1. rewrite V15 in U14. lia.
Qed.

Definition P_of (rho : valuation) : nat := Z.to_nat (bv_unsigned (rw rho 93)).
Definition QD : assn := ltac2:(tb__ "0|0|
S3eS28S4bS31S3Q8A1S4dA2A1P5cVrho0;Vtp0;S50A6").

Lemma to_D : ltac2:(tb__ "0|0|
S7S6aSfS2fS63S0S32S9R5S2aR4A3S33A3S0S32S6cR5A1S33A3S4cR5A1S0S2fR5S31S3Q8A1S4dA2A3S3cS28S4bR6A1R9R7Vtp0;R5A6S51R6A1F_;F_;F_;F_;F_;Fw;Fn;Frho;FsD;FL;").
Proof using HstJ cert_misc cert_runs.
  intros L sD rho n w He Hs HG -> Hsp. exists (mkLeafA D RsCut), (rho_sub rho sD).
  split; [left; reflexivity|]. split; [apply G_sub; [exact Hs | exact HG]|].
  eapply SPA_entails_idb; [exact He | exact Hs | apply Kw_stable; lia | exact Hsp].
Qed.

Lemma after_write_below : ltac2:(tb__ "0|0|
S7S4aS49S0S4aS10S6R3A1A1R2A3S0S32S6fS11S1bS10S6S81R4S15S6R4A1Z16A2A2A1A1A1S39S11S22S17R3A1S18R2A1A2S37S11A1A3A3S33A3F_;Fz;Fv;FS;").
Proof using bs1 bs2 cert_misc cert_runs.
  intros S v z Hv. unfold A_after_write, ax_setS. cbn [ax_S]. unfold S_after_write. rewrite !ss_next_add_fact, ss_next_S_after, Hv.
  cbn. rewrite !andb_true_r. apply Pos.ltb_lt. lia.
Qed.

Lemma below_of_eq : ltac2:(tb__ "0|0|
S7S7S11S4aS11S0S7S80R5R3A2R4A3S0S4aS10S6R5A1A1R3A3S0S32S1bR4R3A2S33A3S0S32S1bS10S6R8A1A1R4A2S33A3F_;F_;F_;Ff;Fv;Fp;FS';FS;").
Proof using . intros S S' p v f <- Hv Hf. exact (eq_trans (f_equal (fun n => sprop_below n f) Hv) Hf). Qed.

Lemma loop : ltac2:(tb__ "0|8|
S2fS1SfS4cR1A1M0S47S4fR2A1M1S31S3Q8A1M2Vbs1;A2M3A2S47U1M4S57S4fR3A1M5S31G2Vbs2;A2M6A2A2S47S57S4fR4A1M7G6A2R5A2S64S28Vok;S3cS28S4bS58G3S4fR5A1A2A1S2eR5Vtp0;A5S51A4F_;F_;F_;F_;Frho;SfG0S1S47G4G1A2S47G1G6A2A2S47G5R4A2S64S28Vok;S3cS28S4bS57G3S58G6G7A2A2A1S2dR4Vtp0;A5S51A4F_;F_;F_;Frho;A2Fm;").
Proof using HU13 HU15 Hfd Hmax HokK HokP Hrl5 Hrl6 HstJ PB1_eq PB2_eq PB2a_eq PB2b_eq cert_misc cert_runs ent_PB1_CB1 ent_PB1_D ent_PB2a_CB2 ent_PB2a_D ent_PB2b_CB1 ent_PB2b_D run_PB1 run_PB2a run_PB2b site_CB1 site_CB2 subs_id sv93 wl_fd_rng.
  pose proof rwmax as RWM. rewrite MSG_len in RWM.
  pose proof subs_id as SI. cbn [forallb] in SI.
  apply andb_prop in SI as [S1 SI]. apply andb_prop in SI as [S2 SI]. apply andb_prop in SI as [S3 SI].
  apply andb_prop in SI as [S4 SI]. apply andb_prop in SI as [S5 SI]. apply andb_prop in SI as [S6 SI].
  apply andb_prop in SI as [S7 SI]. apply andb_prop in SI as [S8 SI]. apply andb_prop in SI as [S9 SI].
  apply andb_prop in SI as [S10 SI]. apply andb_prop in SI as [S11 SI]. apply andb_prop in SI as [S12 _].
  destruct cert_misc as (Nx2 & R22b & Nx1 & R22c & _ & _ & _ & _ & FPB2ad & FPB2ae & FPB2bd & FPB2be & FPB1d & FPB1e & _).
  destruct cert_runs as (_ & _ & NxPB2a & NxPB2b & NxPB1 & _ & _ & _ & StPB2a & StPB2b & StPB1 & _).
  destruct sv93 as (_ & CV2a & _ & CV2b & CV1 & _).
  pose proof (s2_f12 _ _ _ _ _ site_CB2) as F12. pose proof (s1_f14 _ _ _ _ _ site_CB1) as F14.
  induction m as [|m IH].
  { split; intros; exfalso; lia. }
  destruct IH as [IH2 IH1].
  split.
  -
    intros rho HG HL0 H1 Hm. set (L0 := P_of rho) in *.
    assert (U93 : bv_unsigned (rw rho 93) = Z.of_nat L0) by (subst L0; unfold P_of; pose proof (urange (rw rho 93)); lia).
    clearbody L0.
    apply triple_factsA. intros HF.
    eapply triple_seq.
    { apply (writev2 CB2 _ _ rho L0 site_CB2 HG); [rewrite Nx2; lia | rewrite R22b, Nx2; reflexivity | lia | lia | cbn [eval]; exact U93 | |].
      + pose proof (G13 rho HG) as V13. cbn [eval] in V13.
        assert (B12 : bv_unsigned (rw rho 12) <= 2 ^ 62).
        { pose proof (proj1 (Forall_forall _ _) HF (SPUle (SVar 12) (SLit (2 ^ 62))) F12) as X.
          cbn [holds eval] in X. rewrite u64_lit in X by lia. exact X. }
        pose proof (urange (rw rho 12)) as UR12.
        rewrite (U_sub2 rho _ _ (bv_unsigned (rw rho 12) + Z.of_nat (length bs1)) (Z.of_nat L0)); [lia | | cbn [eval]; exact U93 | lia].
        apply (U_add2 rho (SVar 12) (SVar 13) (bv_unsigned (rw rho 12)) (Z.of_nat (length bs1))); [reflexivity | exact V13 | lia].
      + rewrite R22b. pose proof (G15 rho HG) as V15. cbn [eval] in V15.
        rewrite (U_add2 rho (SVar 93) (SVar 15) (Z.of_nat L0) (Z.of_nat (length bs2))); [lia | cbn [eval]; exact U93 | exact V15 | lia]. }
    apply triple_ex; intros rho1. apply triple_ex; intros k.
    apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
    rewrite Nx2 in Hk, Hag1.
    assert (E93 : rw rho1 93 = rw rho 93) by (symmetry; apply (proj1 Hag1); lia).
    assert (U98 : bv_unsigned (rw rho1 98) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite two64; lia).
    pose proof (G15 rho1 HG1) as V15. cbn [eval] in V15.

    eapply triple_conseq with (P := SPA segs (Kw (length bs1 - L0 + k)) PB2 rho1 tp0); [| intros w Hw; exact Hw |].
    { intros w Hw. rewrite <- PB2_eq. apply SPA_addn; [exact Hw | | apply after_write_below; exact Nx2]. constructor; [|constructor].
      cbn [holds eval]. rewrite U98, u64_lit by lia. lia. }
    destruct (Nat.le_gt_cases k L0) as [Hle|Hgt].
    +
      eapply triple_conseq with (P := SPA segs (Kw (length bs1 - L0 + k)) PB2a rho1 tp0); [| intros w Hw; exact Hw |].
      { intros w Hw. rewrite <- PB2a_eq. apply SPA_add1; [exact Hw | | apply (below_of_eq _ _ _ _ _ PB2a_eq NxPB2a); reflexivity]. cbn [holds eval branch_taken]. unfold bv_ltu.
        rewrite E93, U93, U98. destruct (Z.ltb_spec (Z.of_nat L0) (Z.of_nat k)); [lia | discriminate]. }
      eapply runA_tr; [exact run_PB2a | exact StPB2a | apply HokK | apply Kw_stable; rewrite NxPB2a; cbn; lia |].
      intros L rho2 [<-|[<-|[]]] Hag2; cbn [la_state]; rewrite NxPB2a in Hag2.
      *
        eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
        intros w Hw. pose proof (hdA_fact segs rho2 L_PB2a_d _ _ w _ tp0 FPB2ad Hw) as Hf.
        cbn [holds branch_taken eval] in Hf. unfold bv_eqb in Hf. apply Z.eqb_eq in Hf.
        rewrite <- (proj1 Hag2 98%positive ltac:(cbn; lia)), U98 in Hf.
        rewrite (alu_add2 (rw rho2 93) (rw rho2 15) (Z.of_nat L0) (Z.of_nat (length bs2))) in Hf;
          [| rewrite <- (proj1 Hag2 93%positive ltac:(cbn; lia)), E93; exact U93
           | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia].
        apply (to_D _ _ rho2 (length bs1 - L0 + k)%nat w ent_PB2a_D S9 ltac:(eapply G_agree; [exact Hag2 | cbn; lia | exact HG1]) ltac:(clear -HL0 Hle Hf; rewrite MSG_len; lia) Hw).
      *
        apply triple_factsA. intros HF2. rewrite FPB2ae in HF2.
        apply Forall_inv in HF2. cbn [holds branch_taken eval] in HF2. unfold bv_eqb in HF2. rewrite Z.eqb_eq in HF2.
        rewrite <- (proj1 Hag2 98%positive ltac:(cbn; lia)), U98 in HF2.
        rewrite (alu_add2 (rw rho2 93) (rw rho2 15) (Z.of_nat L0) (Z.of_nat (length bs2))) in HF2;
          [| rewrite <- (proj1 Hag2 93%positive ltac:(cbn; lia)), E93; exact U93
           | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia].
        assert (EL : P_of (rho_sub rho2 s_PB2a_CB2) = (L0 - k)%nat).
        { unfold P_of. cbn [rho_sub rw]. rewrite CV2a.
          rewrite (U_sub2 rho2 (SVar 93) (SVar 98) (Z.of_nat L0) (Z.of_nat k)); [lia | | | lia];
            cbn [eval]; rewrite <- ?(proj1 Hag2 93%positive ltac:(cbn; lia)), <- ?(proj1 Hag2 98%positive ltac:(cbn; lia)), ?E93; [exact U93 | exact U98]. }
        eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH2 (rho_sub rho2 s_PB2a_CB2))].
        -- intros w Hw. eapply SPA_entails_idb in Hw; [| exact ent_PB2a_CB2 | exact S2 | apply Kw_stable; lia]. rewrite EL.
           replace (length bs1 - (L0 - k))%nat with (length bs1 - L0 + k)%nat by lia. exact Hw.
        -- apply G_sub; [exact S2|]. eapply G_agree; [exact Hag2 | cbn; lia | exact HG1].
        -- rewrite EL. lia.
        -- rewrite EL. lia.
        -- rewrite EL. lia.
    +
      eapply triple_conseq with (P := SPA segs (Kw (length bs1 - L0 + k)) PB2b rho1 tp0); [| intros w Hw; exact Hw |].
      { intros w Hw. rewrite <- PB2b_eq. apply SPA_add1; [exact Hw | | apply (below_of_eq _ _ _ _ _ PB2b_eq NxPB2b); reflexivity]. cbn [holds eval branch_taken]. unfold bv_ltu.
        rewrite E93, U93, U98. destruct (Z.ltb_spec (Z.of_nat L0) (Z.of_nat k)); [reflexivity | lia]. }
      eapply runA_tr; [exact run_PB2b | exact StPB2b | apply HokK | apply Kw_stable; rewrite NxPB2b; cbn; lia |].
      intros L rho2 [<-|[<-|[]]] Hag2; cbn [la_state]; rewrite NxPB2b in Hag2.
      *
        eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
        intros w Hw. pose proof (hdA_fact segs rho2 L_PB2b_d _ _ w _ tp0 FPB2bd Hw) as Hf.
        cbn [holds branch_taken eval] in Hf. unfold bv_eqb in Hf. apply Z.eqb_eq in Hf.
        rewrite <- (proj1 Hag2 98%positive ltac:(cbn; lia)), U98 in Hf.
        rewrite (alu_add2 (rw rho2 93) (rw rho2 15) (Z.of_nat L0) (Z.of_nat (length bs2))) in Hf;
          [| rewrite <- (proj1 Hag2 93%positive ltac:(cbn; lia)), E93; exact U93
           | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia].
        apply (to_D _ _ rho2 (length bs1 - L0 + k)%nat w ent_PB2b_D S10 ltac:(eapply G_agree; [exact Hag2 | cbn; lia | exact HG1]) ltac:(clear -HL0 Hgt Hf Hkb; rewrite MSG_len; lia) Hw).
      *
        apply triple_factsA. intros HF2. rewrite FPB2be in HF2.
        apply Forall_inv in HF2. cbn [holds branch_taken eval] in HF2. unfold bv_eqb in HF2. rewrite Z.eqb_eq in HF2.
        rewrite <- (proj1 Hag2 98%positive ltac:(cbn; lia)), U98 in HF2.
        rewrite (alu_add2 (rw rho2 93) (rw rho2 15) (Z.of_nat L0) (Z.of_nat (length bs2))) in HF2;
          [| rewrite <- (proj1 Hag2 93%positive ltac:(cbn; lia)), E93; exact U93
           | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia].
        assert (ER : P_of (rho_sub rho2 s_PB2b_CB1) = (L0 + length bs2 - k)%nat).
        { unfold P_of. cbn [rho_sub rw]. rewrite CV2b.
          rewrite (U_sub2 rho2 (SVar 15) _ (Z.of_nat (length bs2)) (Z.of_nat k - Z.of_nat L0)); [lia | | | lia].
          - cbn [eval]. rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)). exact V15.
          - apply (U_sub2 rho2 (SVar 98) (SVar 93)); [| | lia]; cbn [eval];
              rewrite <- ?(proj1 Hag2 93%positive ltac:(cbn; lia)), <- ?(proj1 Hag2 98%positive ltac:(cbn; lia)), ?E93; [exact U98 | exact U93]. }
        eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH1 (rho_sub rho2 s_PB2b_CB1))].
        -- intros w Hw. eapply SPA_entails_idb in Hw; [| exact ent_PB2b_CB1 | exact S4 | apply Kw_stable; lia]. rewrite ER.
           replace (length bs1 + (length bs2 - (L0 + length bs2 - k)))%nat with (length bs1 - L0 + k)%nat by lia. exact Hw.
        -- apply G_sub; [exact S4|]. eapply G_agree; [exact Hag2 | cbn; lia | exact HG1].
        -- rewrite ER. lia.
        -- rewrite ER. lia.
  -
    intros rho HG HR Hm. set (R := P_of rho) in *.
    assert (U93 : bv_unsigned (rw rho 93) = Z.of_nat R) by (subst R; unfold P_of; pose proof (urange (rw rho 93)); lia).
    clearbody R.
    apply triple_factsA. intros HF.
    eapply triple_seq.
    { apply (writev1 CB1 _ _ rho R (length bs1 + (length bs2 - R)) site_CB1 HG); [rewrite Nx1; lia | rewrite R22c, Nx1; reflexivity | lia | lia | cbn [eval]; exact U93 | | rewrite R22c; cbn [eval]; exact U93].
      pose proof (G15 rho HG) as V15. cbn [eval] in V15.
      assert (B14 : bv_unsigned (rw rho 14) <= 2 ^ 62).
      { pose proof (proj1 (Forall_forall _ _) HF (SPUle (SVar 14) (SLit (2 ^ 62))) F14) as X.
        cbn [holds eval] in X. rewrite u64_lit in X by lia. exact X. }
      pose proof (urange (rw rho 14)) as UR14.
      rewrite (U_sub2 rho _ _ (bv_unsigned (rw rho 14) + Z.of_nat (length bs2)) (Z.of_nat R)); [lia | | cbn [eval]; exact U93 | lia].
      apply (U_add2 rho (SVar 14) (SVar 15) (bv_unsigned (rw rho 14)) (Z.of_nat (length bs2))); [reflexivity | exact V15 | lia]. }
    apply triple_ex; intros rho1. apply triple_ex; intros k.
    apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
    rewrite Nx1 in Hk, Hag1.
    assert (E93 : rw rho1 93 = rw rho 93) by (symmetry; apply (proj1 Hag1); lia).
    assert (U100 : bv_unsigned (rw rho1 100) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite two64; lia).
    eapply triple_conseq with (P := SPA segs (Kw (length bs1 + (length bs2 - R) + k)) PB1 rho1 tp0); [| intros w Hw; exact Hw |].
    { intros w Hw. rewrite <- PB1_eq. apply SPA_addn; [exact Hw | | apply after_write_below; exact Nx1]. constructor; [|constructor].
      cbn [holds eval]. rewrite U100, u64_lit by lia. lia. }
    eapply runA_tr; [exact run_PB1 | exact StPB1 | apply HokK | apply Kw_stable; rewrite NxPB1; cbn; lia |].
    intros L rho2 [<-|[<-|[]]] Hag2; cbn [la_state]; rewrite NxPB1 in Hag2.
    +
      eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
      intros w Hw. pose proof (hdA_fact segs rho2 L_PB1_d _ _ w _ tp0 FPB1d Hw) as Hf.
      cbn [holds branch_taken eval] in Hf. unfold bv_eqb in Hf. apply Z.eqb_eq in Hf.
      rewrite <- (proj1 Hag2 100%positive ltac:(cbn; lia)), <- (proj1 Hag2 93%positive ltac:(cbn; lia)), U100, E93, U93 in Hf.
      apply (to_D _ _ rho2 (length bs1 + (length bs2 - R) + k)%nat w ent_PB1_D S11 ltac:(eapply G_agree; [exact Hag2 | cbn; lia | exact HG1]) ltac:(clear -HR Hf Hkb; rewrite MSG_len; lia) Hw).
    +
      apply triple_factsA. intros HF2. rewrite FPB1e in HF2.
      apply Forall_inv in HF2. cbn [holds branch_taken eval] in HF2. unfold bv_eqb in HF2. rewrite Z.eqb_eq in HF2.
      rewrite <- (proj1 Hag2 100%positive ltac:(cbn; lia)), <- (proj1 Hag2 93%positive ltac:(cbn; lia)), U100, E93, U93 in HF2.
      assert (ER : P_of (rho_sub rho2 s_PB1_CB1) = (R - k)%nat).
      { unfold P_of. cbn [rho_sub rw]. rewrite CV1.
        rewrite (U_sub2 rho2 (SVar 93) (SVar 100) (Z.of_nat R) (Z.of_nat k)); [lia | | | lia]; cbn [eval];
          rewrite <- ?(proj1 Hag2 93%positive ltac:(cbn; lia)), <- ?(proj1 Hag2 100%positive ltac:(cbn; lia)), ?E93; [exact U93 | exact U100]. }
      eapply triple_conseq; [| intros w Hw; exact Hw | apply (IH1 (rho_sub rho2 s_PB1_CB1))].
      * intros w Hw. eapply SPA_entails_idb in Hw; [| exact ent_PB1_CB1 | exact S5 | apply Kw_stable; lia]. rewrite ER.
        replace (length bs1 + (length bs2 - (R - k)))%nat with (length bs1 + (length bs2 - R) + k)%nat by lia. exact Hw.
      * apply G_sub; [exact S5|]. eapply G_agree; [exact Hag2 | cbn; lia | exact HG1].
      * rewrite ER. lia.
      * rewrite ER. lia.
Qed.

Definition eQ_wr (A : axst) (e : sv) (n len : nat) (rho : valuation) : world -> Prop := ltac2:(tb__ "0|4|
S63S2SfSfS2S2fS2fS1S4cR2A1S1S16S10S6VA;A1A1M0Vrho;R2A3S1S0S3Q40M1A1M2S13R2G0A2M3S5G1S41R1A1A2A3S1S1S47U1R1A2S47R1Vlen;A2A2S1S0G2G3S5G1S41Vlen;A1A2A3S3cS28S4bS57Vn;R1A2A1S81VA;Ve;A2R2Vtp0;R3A6A2A2A2A2A2Lk;A2Lrho';A2Lw;").

Lemma ewritev2 : ltac2:(tb__ "0|7|
S7S14S14SfS2fS7fS28S29R5R4R3A5S4cR3A1S67P5cS10S6R7A1A1A2S0S32S1dS10S6R8A1M0A1S15G0Z16M1A2A2S33A3S47R5S31S3Q8A1M2Vbs1;A2M3A2S47U1S57R6S31G2Vbs2;A2M4A2A2S0S49S4Q40M5S12R8R9A2A2S41R7A1A3S0S49S4G5S12R9RbA2A2S42S4G5S13R9PcA2A2S41S58G3R8A2A1A2A3S0S49S4G5S12RaS15S6RdA1G1A2A2A2S41S57R9G4A2A1A3S65S28S3cS28S4bS58G3RaA2M6A1ReRbVtp0;A5S55ReS15S6ReA1G1A2G6S57RaG4A2RbA5A3F_;F_;F_;F_;F_;F_;F_;F_;F_;FL0;Frho;Fl0;Fe0;FA;").
Proof using HU13 HU15 Hfd Hmax Hrl5 Hrl6 HstJ cert_misc cert_runs wl_fd_rng.
  intros A e0 l0 rho L0 HS HG Hn He HL0 H1 Hl0 He0 H22.
  destruct HS as [Hlen Hrng Hb1 Hb2 C8 C16 C24 C32 R11 Hi H17 H10 H12 F10a F10b F12 F14 UR].
  pose proof wl_fd_u as FD.
  set (n := (length bs1 - L0)%nat).
  assert (Hbs : length (skipn n bs1 ++ bs2) = (L0 + length bs2)%nat) by (rewrite length_app, length_skipn; lia).
  eapply etriple_conseq; [intros w Hw; exact Hw | |
    eapply (etriple_writev2A segs (Kw n) (J' A n (L0 + length bs2)) A rho tp0 wl_fd (skipn n bs1) bs2 (reg_sv (ax_S A) 22));
      [ apply Kw_stable; exact Hn
      | apply J'_stable; exact Hn
      | exact Hi | exact H17 | exact H10 | exact H12 | exact wl_fd_rng | rewrite Hbs; pose proof rwmax as RWM; rewrite MSG_len in RWM; lia | exact He | | ]].
  - intros w (rho' & Hag & Hfull & Hsm & (k & Hk & Hkb & HK)). exists rho', k.
    split; [exact (G_agree _ _ _ Hag Hn HG)|]. split; [exact Hag|]. split; [exact Hk|]. split; [exact Hkb|].
    split; [rewrite Hbs in Hfull; exact Hfull|]. split; [exact Hsm | exact HK].
  - intros rho' tr md k Hag Hk HK Hkb. split; [exact (Kw_fd _ _ _ _ _ HK)|]. exists k. split; [exact Hk|].
    split; [rewrite Hbs in Hkb; exact Hkb|].
    replace (skipn n bs1 ++ bs2) with (skipn n MSG) by (unfold MSG; rewrite skipn_app; replace (n - length bs1)%nat with 0%nat by lia; reflexivity).
    apply Kw_step. eapply (Kw_stable n (ss_next (ax_S A)) Hn); [exact Hag | apply mat_equiv_refl | exact HK].
  - intros tr ms md Hsp HK.
    pose proof (SPpA_fact segs _ _ _ _ _ _ _ Hsp F10a) as A1. pose proof (SPpA_fact segs _ _ _ _ _ _ _ Hsp F10b) as A2.
    pose proof (SPpA_fact segs _ _ _ _ _ _ _ Hsp F12) as A3. pose proof (SPpA_fact segs _ _ _ _ _ _ _ Hsp F14) as A4.
    cbn [holds eval] in A1, A2, A3, A4. rewrite !u64_lit in A1, A2, A3, A4 by lia.
    change (eval rho (SVar 10)) with (rw rho 10) in *. change (eval rho (SVar 12)) with (rw rho 12) in *. change (eval rho (SVar 14)) with (rw rho 14) in *.
    pose proof (G13 rho HG) as V13. pose proof (G15 rho HG) as V15. cbn [eval] in V13, V15.
    assert (A0 : bv_unsigned (eval rho (reg_sv (ax_S A) 11)) = bv_unsigned (rw rho 10) + 8).
    { rewrite R11. apply (U_addc rho (SVar 10) 8 (bv_unsigned (rw rho 10))); [reflexivity | lia | lia]. }
    assert (A16 : bv_unsigned (eval rho (reg_sv (ax_S A) 11) + 16)%bv = bv_unsigned (rw rho 10) + 24) by (rewrite (U_bvadd _ _ _ _ A0 u16) by lia; lia).
    exists (eval rho e0), (eval rho l0), (eval rho (SVar 14)), (eval rho (SVar 15)).
    split; [eapply (iov_field rho A tr ms md 8); [exact Hsp | exact Hlen | exact Hrng | exact C8 | lia | lia]|].
    split; [eapply (iov_field rho A tr ms md 16); [exact Hsp | exact Hlen | exact Hrng | exact C16 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
    split; [eapply (iov_field rho A tr ms md 24); [exact Hsp | exact Hlen | exact Hrng | exact C24 | lia | lia]|].
    split; [eapply (iov_field rho A tr ms md 32); [exact Hsp | exact Hlen | exact Hrng | exact C32 | lia | rewrite (U_bvadd _ _ _ _ A16 u8) by lia; lia]|].
    split.
    { pose proof rwmax as HM. rewrite MSG_len in HM.
      rewrite (list_read (DList 5) rho A tr ms md 1 12 13 5 (Z.of_nat n) L0 (eval rho e0) (eval rho l0) Hsp ltac:(lia) Hb1 eq_refl ltac:(lia) ltac:(rewrite V13; lia) ltac:(rewrite V13; lia) He0 Hl0).
      f_equal. rewrite Nat2Z.id, (G_rl rho 5 HG), Hrl5. apply firstn_all2. rewrite length_skipn. lia. }
    split.
    { pose proof rwmax as HM. rewrite MSG_len in HM.
      rewrite (list_read (DRom 6) rho A tr ms md 2 14 15 6 0 (length bs2) (eval rho (SVar 14)) (eval rho (SVar 15)) Hsp ltac:(lia) Hb2 eq_refl ltac:(lia) ltac:(rewrite V15; lia) ltac:(rewrite V15; lia) ltac:(cbn [eval]; lia) V15).
      f_equal. cbn [Z.to_nat skipn]. rewrite (G_rl rho 6 HG), Hrl6. apply firstn_all. }
    destruct (UR rho (smatch_pendingA_facts segs _ _ _ _ Hsp)) as (U10 & U12 & U14).
    change (eval rho (SVar 14)) with (rw rho 14). change (eval rho (SVar 15)) with (rw rho 15).
    rewrite task_size_val. split; [rewrite H22, Hbs; reflexivity|]. split; [lia|]. split; [|exact U14].
    rewrite He0, Hl0. rewrite V13 in U12. lia.
Qed.

Lemma ewritev1 : ltac2:(tb__ "0|5|
S7S14S14SfS2fS2fS7eS28S29R6R5R4A5S4cR4A1S67P5cS10S6R8A1A1A2S0S32S1dS10S6R9A1M0A1S15G0Z16M1A2A2S33A3S1S47U1R6A2S47R6S31S3Q8A1M2Vbs2;A2M3A2A2S0S2fR6S57S31G2Vbs1;A2S58G3R7A2A2A3S0S49S4Q40M4S12R9RaA2A2S41R8A1A3S0S49S4G4S12RaRcA2A2S42S4G4S13RaPeA2A2S41S58G3R9A2A1A2A3S0S49S4G4S12RbS15S6ReA1G1A2A2A2S41RaA1A3S65S28S3cS28S4bRaA1RfRcVtp0;A5S55RfS15S6RfA1G1A2RaRbRcA5A3F_;F_;F_;F_;F_;F_;F_;F_;F_;Fn0;FR;Frho;Fl1;Fe1;FA;").
Proof using HU15 Hfd Hmax Hrl6 HstJ cert_misc cert_runs wl_fd_rng.
  intros A e1 l1 rho R n0 HS HG Hn He HR Hn0 Hl1 He1 H22.
  destruct HS as [Hlen Hrng Hb2 C24 C32 R11 Hi H17 H10 H12 F10a F10b F14 UR].
  pose proof wl_fd_u as FD.
  assert (Hbs : length (skipn (length bs2 - R) bs2) = R) by (rewrite length_skipn; lia).
  eapply etriple_conseq; [intros w Hw; exact Hw | |
    eapply (etriple_writev1A segs (Kw n0) (J' A n0 R) A rho tp0 wl_fd (skipn (length bs2 - R) bs2) (reg_sv (ax_S A) 22));
      [ apply Kw_stable; exact Hn
      | apply J'_stable; exact Hn
      | exact Hi | exact H17 | exact H10 | exact H12 | exact wl_fd_rng | rewrite Hbs; pose proof rwmax as RWM; rewrite MSG_len in RWM; lia | exact He | | ]].
  - intros w (rho' & Hag & Hfull & Hsm & (k & Hk & Hkb & HK)). exists rho', k.
    split; [exact (G_agree _ _ _ Hag Hn HG)|]. split; [exact Hag|]. split; [exact Hk|]. split; [exact Hkb|].
    split; [rewrite Hbs in Hfull; exact Hfull|]. split; [exact Hsm | exact HK].
  - intros rho' tr md k Hag Hk HK Hkb. split; [exact (Kw_fd _ _ _ _ _ HK)|]. exists k. split; [exact Hk|].
    split; [rewrite Hbs in Hkb; exact Hkb|].
    replace (skipn (length bs2 - R) bs2) with (skipn n0 MSG) by (unfold MSG; rewrite skipn_app, skipn_all2 by lia; cbn [app]; f_equal; lia).
    apply Kw_step. eapply (Kw_stable n0 (ss_next (ax_S A)) Hn); [exact Hag | apply mat_equiv_refl | exact HK].
  - intros tr ms md Hsp HK.
    pose proof (SPpA_fact segs _ _ _ _ _ _ _ Hsp F10a) as A1. pose proof (SPpA_fact segs _ _ _ _ _ _ _ Hsp F10b) as A2.
    pose proof (SPpA_fact segs _ _ _ _ _ _ _ Hsp F14) as A4.
    cbn [holds eval] in A1, A2, A4. rewrite !u64_lit in A1, A2, A4 by lia.
    change (eval rho (SVar 10)) with (rw rho 10) in *. change (eval rho (SVar 14)) with (rw rho 14) in *.
    pose proof (G15 rho HG) as V15. cbn [eval] in V15.
    assert (A0 : bv_unsigned (eval rho (reg_sv (ax_S A) 11)) = bv_unsigned (rw rho 10) + 24).
    { rewrite R11. apply (U_addc rho (SVar 10) 24 (bv_unsigned (rw rho 10))); [reflexivity | lia | lia]. }
    exists (eval rho e1), (eval rho l1).
    split; [eapply (iov_field rho A tr ms md 24); [exact Hsp | exact Hlen | exact Hrng | exact C24 | lia | lia]|].
    split; [eapply (iov_field rho A tr ms md 32); [exact Hsp | exact Hlen | exact Hrng | exact C32 | lia | rewrite (U_bvadd _ _ _ _ A0 u8) by lia; lia]|].
    split.
    { pose proof rwmax as HM. rewrite MSG_len in HM.
      rewrite (list_read (DRom 6) rho A tr ms md 2 14 15 6 (Z.of_nat (length bs2 - R)) R (eval rho e1) (eval rho l1) Hsp ltac:(lia) Hb2 eq_refl ltac:(lia) ltac:(rewrite V15; lia) ltac:(rewrite V15; lia) He1 Hl1).
      f_equal. rewrite Nat2Z.id, (G_rl rho 6 HG), Hrl6. apply firstn_all2. rewrite length_skipn. lia. }
    destruct (UR rho (smatch_pendingA_facts segs _ _ _ _ Hsp)) as (U10 & U14).
    rewrite task_size_val. split; [rewrite H22, Hbs; reflexivity|]. split; [lia|].
    rewrite He1, Hl1. rewrite V15 in U14. lia.
Qed.

Lemma G0 : G rho0. Proof using . apply agree_below_refl. Qed.

Lemma SP_Kw0 : ltac2:(tb__ "0|0|
S7SfS63S3cS28VJ;R3R2Vtp0;R1A6S3cS28S4bU0A1R4R3Vtp0;R2A6F_;Fw;Frho;FS;").
Proof using . intros S rho w [Hsm Hk]. split; [exact Hsm|]. exists (w_tr w). split; [exact Hk|]. unfold TRk. cbn. rewrite app_nil_r. reflexivity. Qed.

Theorem wl2_sum : ltac2:(tb__ "0|1|
S47U1S31S3Q8A1M0Vbs1;A2A2S64S28Vok;S3cS28VJ;S2cVrho0;Vtp0;A5S3eS28S4bS31G0S4dA2A1P5cVrho0;Vtp0;S50A6A4F_;").
Proof using HU13 HU15 Hfd Hmax HokK HokP Hrl5 Hrl6 HstJ PA2_eq PA2a_eq PA2b_eq PB1_eq PB2_eq PB2a_eq PB2b_eq cert_misc cert_pre cert_runs ent_PA2a_CB2 ent_PA2a_D ent_PA2b_CB1 ent_PA2b_D ent_PB1_CB1 ent_PB1_D ent_PB2a_CB2 ent_PB2a_D ent_PB2b_CB1 ent_PB2b_D run_PA2a run_PA2b run_PB1 run_PB2a run_PB2b site_CB1 site_CB2 site_Pre_wl2 subs_id sv93 wl_fd_rng.
  intros Hbs1. pose proof rwmax as RWM. rewrite MSG_len in RWM.
  pose proof subs_id as SI. cbn [forallb] in SI.
  apply andb_prop in SI as [S1 SI]. apply andb_prop in SI as [S2 SI]. apply andb_prop in SI as [S3 SI].
  apply andb_prop in SI as [S4 SI]. apply andb_prop in SI as [S5 SI]. apply andb_prop in SI as [S6 SI].
  apply andb_prop in SI as [S7 SI]. apply andb_prop in SI as [S8 SI]. apply andb_prop in SI as [S9 SI].
  apply andb_prop in SI as [S10 SI]. apply andb_prop in SI as [S11 SI]. apply andb_prop in SI as [S12 _].
  destruct cert_misc as (Nx2 & R22b & Nx1 & R22c & Nx0 & R22a & _ & _ & _ & _ & _ & _ & _ & _ & FPA2ad & FPA2ae & FPA2bd & FPA2be & _ & _).
  destruct cert_runs as (NxPA2a & NxPA2b & _ & _ & _ & _ & StPA2a & StPA2b & _ & _ & _ & _).
  destruct sv93 as (CVa & _ & CVb & _ & _ & _).
  destruct cert_pre as (B22 & _ & _ & _ & F12 & _).
  eapply triple_conseq; [intros w Hw; exact (SP_Kw0 _ _ _ Hw) | intros w Hw; exact Hw |].
  apply triple_factsA. intros HF.
  assert (B12 : bv_unsigned (rw rho0 12) <= 2 ^ 62).
  { pose proof (proj1 (Forall_forall _ _) HF _ F12) as X. cbn [holds eval] in X. rewrite u64_lit in X by lia. exact X. }
  pose proof (urange (rw rho0 12)) as UR12.
  eapply triple_seq.
  { replace 0%nat with (length bs1 - length bs1)%nat by lia.
    apply (writev2 Pre_wl2 (SVar 12) (SVar 13) rho0 (length bs1) site_Pre_wl2 G0); [rewrite Nx0; lia | rewrite Nx0; exact B22 | lia | lia | cbn [eval]; exact HU13 | cbn [eval]; lia |].
    rewrite R22a, Nat2Z.inj_add. apply (U_add2 rho0 (SVar 13) (SVar 15)); [cbn [eval]; exact HU13 | cbn [eval]; exact HU15 | lia]. }
  apply triple_ex; intros rho1. apply triple_ex; intros k.
  apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
  rewrite Nx0 in Hk, Hag1. replace (length bs1 - length bs1 + k)%nat with k by lia.
  assert (U92 : bv_unsigned (rw rho1 92) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite two64; lia).
  pose proof (G13 rho1 HG1) as V13. pose proof (G15 rho1 HG1) as V15. cbn [eval] in V13, V15.
  eapply triple_conseq with (P := SPA segs (Kw k) PA2 rho1 tp0); [| intros w Hw; exact Hw |].
  { intros w Hw. rewrite <- PA2_eq. apply SPA_addn; [exact Hw | | apply after_write_below; exact Nx0]. constructor; [|constructor].
    cbn [holds eval]. rewrite U92, u64_lit by lia. lia. }
  destruct (Nat.le_gt_cases k (length bs1)) as [Hle|Hgt].
  - eapply triple_conseq with (P := SPA segs (Kw k) PA2a rho1 tp0); [| intros w Hw; exact Hw |].
    { intros w Hw. rewrite <- PA2a_eq. apply SPA_add1; [exact Hw | | apply (below_of_eq _ _ _ _ _ PA2a_eq NxPA2a); reflexivity]. cbn [holds eval branch_taken]. unfold bv_ltu.
      rewrite V13, U92. destruct (Z.ltb_spec (Z.of_nat (length bs1)) (Z.of_nat k)); [lia | discriminate]. }
    eapply runA_tr; [exact run_PA2a | exact StPA2a | apply HokK | apply Kw_stable; rewrite NxPA2a; cbn; lia |].
    intros L rho2 [<-|[<-|[]]] Hag2; cbn [la_state]; rewrite NxPA2a in Hag2.
    +
      apply triple_factsA. intros HF2. rewrite FPA2ae in HF2.
      apply Forall_inv in HF2. cbn [holds branch_taken eval] in HF2. unfold bv_eqb in HF2. apply negb_true_iff in HF2. rewrite Z.eqb_neq in HF2.
      rewrite <- (proj1 Hag2 92%positive ltac:(cbn; lia)), U92 in HF2.
      rewrite (alu_add2 (rw rho2 13) (rw rho2 15) (Z.of_nat (length bs1)) (Z.of_nat (length bs2))) in HF2;
        [| rewrite <- (proj1 Hag2 13%positive ltac:(cbn; lia)); exact V13
         | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia].
      assert (EL : P_of (rho_sub rho2 s_PA2a_CB2) = (length bs1 - k)%nat).
      { unfold P_of. cbn [rho_sub rw]. rewrite CVa.
        rewrite (U_sub2 rho2 (SVar 13) (SVar 92) (Z.of_nat (length bs1)) (Z.of_nat k)); [lia | | | lia]; cbn [eval];
          rewrite <- ?(proj1 Hag2 13%positive ltac:(cbn; lia)), <- ?(proj1 Hag2 92%positive ltac:(cbn; lia)); [exact V13 | exact U92]. }
      eapply triple_conseq; [| intros w Hw; exact Hw | apply (proj1 (loop (length bs1 - k + length bs2)) (rho_sub rho2 s_PA2a_CB2))].
      * intros w Hw. eapply SPA_entails_idb in Hw; [| exact ent_PA2a_CB2 | exact S1 | apply Kw_stable; lia]. rewrite EL.
        replace (length bs1 - (length bs1 - k))%nat with k by lia. exact Hw.
      * apply G_sub; [exact S1|]. eapply G_agree; [exact Hag2 | cbn; lia | exact HG1].
      * rewrite EL. lia.
      * rewrite EL. clear -Hle Hkb HF2 Hbs1. lia.
      * rewrite EL. lia.
    +
      eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
      intros w Hw. pose proof (hdA_fact segs rho2 L_PA2a_d _ _ w _ tp0 FPA2ad Hw) as Hf.
      cbn [holds branch_taken eval] in Hf. unfold bv_eqb in Hf. apply negb_neq_true in Hf. apply Z.eqb_eq in Hf.
      rewrite <- (proj1 Hag2 92%positive ltac:(cbn; lia)), U92 in Hf.
      rewrite (alu_add2 (rw rho2 13) (rw rho2 15) (Z.of_nat (length bs1)) (Z.of_nat (length bs2))) in Hf;
        [| rewrite <- (proj1 Hag2 13%positive ltac:(cbn; lia)); exact V13
         | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia].
      apply (to_D _ _ rho2 k w ent_PA2a_D S7 ltac:(eapply G_agree; [exact Hag2 | cbn; lia | exact HG1]) ltac:(clear -Hf; rewrite MSG_len; lia) Hw).
  - eapply triple_conseq with (P := SPA segs (Kw k) PA2b rho1 tp0); [| intros w Hw; exact Hw |].
    { intros w Hw. rewrite <- PA2b_eq. apply SPA_add1; [exact Hw | | apply (below_of_eq _ _ _ _ _ PA2b_eq NxPA2b); reflexivity]. cbn [holds eval branch_taken]. unfold bv_ltu.
      rewrite V13, U92. destruct (Z.ltb_spec (Z.of_nat (length bs1)) (Z.of_nat k)); [reflexivity | lia]. }
    eapply runA_tr; [exact run_PA2b | exact StPA2b | apply HokK | apply Kw_stable; rewrite NxPA2b; cbn; lia |].
    intros L rho2 [<-|[<-|[]]] Hag2; cbn [la_state]; rewrite NxPA2b in Hag2.
    +
      apply triple_factsA. intros HF2. rewrite FPA2be in HF2.
      apply Forall_inv in HF2. cbn [holds branch_taken eval] in HF2. unfold bv_eqb in HF2. apply negb_true_iff in HF2. rewrite Z.eqb_neq in HF2.
      rewrite <- (proj1 Hag2 92%positive ltac:(cbn; lia)), U92 in HF2.
      rewrite (alu_add2 (rw rho2 13) (rw rho2 15) (Z.of_nat (length bs1)) (Z.of_nat (length bs2))) in HF2;
        [| rewrite <- (proj1 Hag2 13%positive ltac:(cbn; lia)); exact V13
         | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia].
      assert (ER : P_of (rho_sub rho2 s_PA2b_CB1) = (length bs1 + length bs2 - k)%nat).
      { unfold P_of. cbn [rho_sub rw]. rewrite CVb.
        rewrite (U_sub2 rho2 (SVar 15) _ (Z.of_nat (length bs2)) (Z.of_nat k - Z.of_nat (length bs1))); [lia | | | lia].
        - cbn [eval]. rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)). exact V15.
        - apply (U_sub2 rho2 (SVar 92) (SVar 13)); [| | lia]; cbn [eval];
            rewrite <- ?(proj1 Hag2 13%positive ltac:(cbn; lia)), <- ?(proj1 Hag2 92%positive ltac:(cbn; lia)); [exact U92 | exact V13]. }
      eapply triple_conseq; [| intros w Hw; exact Hw | apply (proj2 (loop (length bs1 + length bs2 - k)) (rho_sub rho2 s_PA2b_CB1))].
      * intros w Hw. eapply SPA_entails_idb in Hw; [| exact ent_PA2b_CB1 | exact S3 | apply Kw_stable; lia]. rewrite ER.
        replace (length bs1 + (length bs2 - (length bs1 + length bs2 - k)))%nat with k by lia. exact Hw.
      * apply G_sub; [exact S3|]. eapply G_agree; [exact Hag2 | cbn; lia | exact HG1].
      * rewrite ER. clear -Hgt Hkb HF2. lia.
      * rewrite ER. lia.
    +
      eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
      intros w Hw. pose proof (hdA_fact segs rho2 L_PA2b_d _ _ w _ tp0 FPA2bd Hw) as Hf.
      cbn [holds branch_taken eval] in Hf. unfold bv_eqb in Hf. apply negb_neq_true in Hf. apply Z.eqb_eq in Hf.
      rewrite <- (proj1 Hag2 92%positive ltac:(cbn; lia)), U92 in Hf.
      rewrite (alu_add2 (rw rho2 13) (rw rho2 15) (Z.of_nat (length bs1)) (Z.of_nat (length bs2))) in Hf;
        [| rewrite <- (proj1 Hag2 13%positive ltac:(cbn; lia)); exact V13
         | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia].
      apply (to_D _ _ rho2 k w ent_PA2b_D S8 ltac:(eapply G_agree; [exact Hag2 | cbn; lia | exact HG1]) ltac:(clear -Hf; rewrite MSG_len; lia) Hw).
Qed.

Theorem wl1_sum : ltac2:(tb__ "0|1|
S0S30S3Q8A1M0A1Vbs1;S37G0A1A3S47U1S31G0Vbs2;A2A2S64S28Vok;S3cS28VJ;S2bVrho0;Vtp0;A5S3eS28S4bS31G0S4dA2A1P5cVrho0;Vtp0;S50A6A4F_;F_;").
Proof using HU13 HU15 Hfd Hmax HokK HokP Hrl5 Hrl6 HstJ PA1_eq PB1_eq PB2_eq PB2a_eq PB2b_eq cert_misc cert_pre cert_runs ent_PA1_CB1 ent_PA1_D ent_PB1_CB1 ent_PB1_D ent_PB2a_CB2 ent_PB2a_D ent_PB2b_CB1 ent_PB2b_D run_PA1 run_PB1 run_PB2a run_PB2b site_CB1 site_CB2 site_Pre_wl1 subs_id sv93 wl_fd_rng.
  intros Hnil Hbs2. pose proof rwmax as RWM. rewrite MSG_len in RWM.
  assert (L1z : length bs1 = 0%nat) by (rewrite Hnil; reflexivity).
  pose proof subs_id as SI. cbn [forallb] in SI.
  apply andb_prop in SI as [S1 SI]. apply andb_prop in SI as [S2 SI]. apply andb_prop in SI as [S3 SI].
  apply andb_prop in SI as [S4 SI]. apply andb_prop in SI as [S5 SI]. apply andb_prop in SI as [S6 SI].
  apply andb_prop in SI as [S7 SI]. apply andb_prop in SI as [S8 SI]. apply andb_prop in SI as [S9 SI].
  apply andb_prop in SI as [S10 SI]. apply andb_prop in SI as [S11 SI]. apply andb_prop in SI as [S12 _].
  destruct cert_misc as (Nx2 & R22b & Nx1 & R22c & Nx0 & R22a & Nx0' & R22a' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FPA1d & FPA1e).
  destruct cert_runs as (_ & _ & _ & _ & _ & NxPA1 & _ & _ & _ & _ & _ & StPA1).
  destruct sv93 as (_ & _ & _ & _ & _ & CVc).
  destruct cert_pre as (_ & B22 & _ & _ & _ & F14).
  eapply triple_conseq; [intros w Hw; exact (SP_Kw0 _ _ _ Hw) | intros w Hw; exact Hw |].
  apply triple_factsA. intros HF.
  assert (B14 : bv_unsigned (rw rho0 14) <= 2 ^ 62).
  { pose proof (proj1 (Forall_forall _ _) HF _ F14) as X. cbn [holds eval] in X. rewrite u64_lit in X by lia. exact X. }
  pose proof (urange (rw rho0 14)) as UR14.
  eapply triple_seq.
  { apply (writev1 Pre_wl1 (SVar 14) (SVar 15) rho0 (length bs2) 0%nat site_Pre_wl1 G0); [rewrite Nx0'; lia | rewrite Nx0'; exact B22 | lia | lia | cbn [eval]; exact HU15 | cbn [eval]; lia |].
    rewrite R22a'. cbn [eval]. exact HU15. }
  apply triple_ex; intros rho1. apply triple_ex; intros k.
  apply triple_pure; intros HG1. apply triple_pure; intros Hag1. apply triple_pure; intros Hk. apply triple_pure; intros Hkb.
  rewrite Nx0' in Hk, Hag1. cbn [Nat.add].
  assert (U92 : bv_unsigned (rw rho1 92) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite two64; lia).
  pose proof (G15 rho1 HG1) as V15. cbn [eval] in V15.
  eapply triple_conseq with (P := SPA segs (Kw k) PA1 rho1 tp0); [| intros w Hw; exact Hw |].
  { intros w Hw. rewrite <- PA1_eq. apply SPA_addn; [exact Hw | | apply after_write_below; exact Nx0']. constructor; [|constructor].
    cbn [holds eval]. rewrite U92, u64_lit by lia. lia. }
  eapply runA_tr; [exact run_PA1 | exact StPA1 | apply HokK | apply Kw_stable; rewrite NxPA1; cbn; lia |].
  intros L rho2 [<-|[<-|[]]] Hag2; cbn [la_state]; rewrite NxPA1 in Hag2.
  -
    apply triple_factsA. intros HF2. rewrite FPA1e in HF2.
    apply Forall_inv in HF2. cbn [holds branch_taken eval] in HF2. unfold bv_eqb in HF2. apply negb_true_iff in HF2. rewrite Z.eqb_neq in HF2.
    rewrite <- (proj1 Hag2 92%positive ltac:(cbn; lia)), <- (proj1 Hag2 15%positive ltac:(cbn; lia)), U92, V15 in HF2.
    assert (ER : P_of (rho_sub rho2 s_PA1_CB1) = (length bs2 - k)%nat).
    { unfold P_of. cbn [rho_sub rw]. rewrite CVc.
      rewrite (U_sub2 rho2 (SVar 15) (SVar 92) (Z.of_nat (length bs2)) (Z.of_nat k)); [lia | | | lia]; cbn [eval];
        rewrite <- ?(proj1 Hag2 15%positive ltac:(cbn; lia)), <- ?(proj1 Hag2 92%positive ltac:(cbn; lia)); [exact V15 | exact U92]. }
    eapply triple_conseq; [| intros w Hw; exact Hw | apply (proj2 (loop (length bs2 - k)) (rho_sub rho2 s_PA1_CB1))].
    + intros w Hw. eapply SPA_entails_idb in Hw; [| exact ent_PA1_CB1 | exact S6 | apply Kw_stable; lia]. rewrite ER, L1z.
      replace (0 + (length bs2 - (length bs2 - k)))%nat with k by lia. exact Hw.
    + apply G_sub; [exact S6|]. eapply G_agree; [exact Hag2 | cbn; lia | exact HG1].
    + rewrite ER. clear -Hkb HF2. lia.
    + rewrite ER. lia.
  -
    eapply triple_conseq; [| intros w Hw; exact Hw | apply triple_refl].
    intros w Hw. pose proof (hdA_fact segs rho2 L_PA1_d _ _ w _ tp0 FPA1d Hw) as Hf.
    cbn [holds branch_taken eval] in Hf. unfold bv_eqb in Hf. apply negb_neq_true in Hf. apply Z.eqb_eq in Hf.
    rewrite <- (proj1 Hag2 92%positive ltac:(cbn; lia)), <- (proj1 Hag2 15%positive ltac:(cbn; lia)), U92, V15 in Hf.
    apply (to_D _ _ rho2 k w ent_PA1_D S12 ltac:(eapply G_agree; [exact Hag2 | cbn; lia | exact HG1]) ltac:(clear -Hf L1z; rewrite MSG_len; lia) Hw).
Qed.

Definition eQD : world -> Prop := ltac2:(tb__ "0|0|
S3eS28S4bS31S3Q8A1S4dA2A1P5cVrho0;Vtp0;S50A6").

Lemma eto_D : ltac2:(tb__ "0|0|
S7S6aSfS2fS63S0S32S9R5S2aR4A3S33A3S0S32S6cR5A1S33A3S4cR5A1S0S2fR5S31S3Q8A1S4dA2A3S3cS28S4bR6A1R9R7Vtp0;R5A6S53R6A1F_;F_;F_;F_;F_;Fw;Fn;Frho;FsD;FL;").
Proof using HstJ cert_misc cert_runs. intros. eapply to_D; eauto. Qed.

Lemma k_full : ltac2:(tb__ "0|4|
S3Q40M0A1M1S2fS2fS0G1R3S5G0S41R2A1A2M2A3S0G1R4G2A3S44S41R4A1S45Z2Z40A2A2M3G3S0S2fR6R5A3F_;F_;F_;F_;Flen;Fk;Fr;").
Proof using bs1 bs2 cert_misc cert_runs.
  intros r k len H1 H2 Hk Hl. rewrite H1 in H2. apply (f_equal bv_unsigned) in H2.
  rewrite !Z_to_bv_small in H2 by (rewrite two64; lia). lia.
Qed.

Theorem wl2_sum_ex : ltac2:(tb__ "0|0|
S47U1S31S3Q8A1Vbs1;A2A2S65S28S3cS28VJ;S2cVrho0;Vtp0;A5S53A3F_;").
Proof using HU13 HU15 Hfd Hmax Hrl5 Hrl6 HstJ PA2_eq PA2a_eq PA2b_eq cert_misc cert_pre cert_runs ent_PA2a_D ent_PA2b_D run_PA2a run_PA2b site_Pre_wl2 subs_id wl_fd_rng.
  intros Hbs1. pose proof rwmax as RWM. rewrite MSG_len in RWM.
  pose proof subs_id as SI. cbn [forallb] in SI.
  apply andb_prop in SI as [S1 SI]. apply andb_prop in SI as [S2 SI]. apply andb_prop in SI as [S3 SI].
  apply andb_prop in SI as [S4 SI]. apply andb_prop in SI as [S5 SI]. apply andb_prop in SI as [S6 SI].
  apply andb_prop in SI as [S7 SI]. apply andb_prop in SI as [S8 SI]. apply andb_prop in SI as [S9 SI].
  apply andb_prop in SI as [S10 SI]. apply andb_prop in SI as [S11 SI]. apply andb_prop in SI as [S12 _].
  destruct cert_misc as (Nx2 & R22b & Nx1 & R22c & Nx0 & R22a & _ & _ & _ & _ & _ & _ & _ & _ & FPA2ad & FPA2ae & FPA2bd & FPA2be & _ & _).
  destruct cert_runs as (NxPA2a & NxPA2b & _ & _ & _ & _ & StPA2a & StPA2b & _ & _ & _ & _).
  destruct cert_pre as (B22 & _ & _ & _ & F12 & _).
  intros w0 Hw0. apply SP_Kw0 in Hw0.
  pose proof (SPA_facts_hold segs _ _ _ _ _ Hw0) as HF.
  assert (B12 : bv_unsigned (rw rho0 12) <= 2 ^ 62).
  { pose proof (proj1 (Forall_forall _ _) HF _ F12) as X. cbn [holds eval] in X. rewrite u64_lit in X by lia. exact X. }
  pose proof (urange (rw rho0 12)) as UR12.
  revert w0 Hw0. eapply etriple_seq.
  { replace 0%nat with (length bs1 - length bs1)%nat by lia.
    apply (ewritev2 Pre_wl2 (SVar 12) (SVar 13) rho0 (length bs1) site_Pre_wl2 G0); [rewrite Nx0; lia | rewrite Nx0; exact B22 | lia | lia | cbn [eval]; exact HU13 | cbn [eval]; lia |].
    rewrite R22a, Nat2Z.inj_add. apply (U_add2 rho0 (SVar 13) (SVar 15)); [cbn [eval]; exact HU13 | cbn [eval]; exact HU15 | lia]. }
  apply etriple_ex; intros rho1. apply etriple_ex; intros k.
  apply etriple_pure; intros HG1. apply etriple_pure; intros Hag1. apply etriple_pure; intros Hk. apply etriple_pure; intros Hkb. apply etriple_pure; intros Hfull.
  rewrite Nx0 in Hk, Hag1, Hfull. replace (length bs1 - length bs1 + k)%nat with k by lia.
  pose proof (k_full _ _ _ Hk Hfull ltac:(lia) ltac:(lia)) as Ek.
  assert (U92 : bv_unsigned (rw rho1 92) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite two64; lia).
  pose proof (G13 rho1 HG1) as V13. pose proof (G15 rho1 HG1) as V15. cbn [eval] in V13, V15.
  eapply etriple_conseq with (P := SPA segs (Kw k) PA2 rho1 tp0); [| intros w Hw; exact Hw |].
  { intros w Hw. rewrite <- PA2_eq. apply SPA_addn; [exact Hw | | apply after_write_below; exact Nx0]. constructor; [|constructor].
    cbn [holds eval]. rewrite U92, u64_lit by lia. lia. }
  destruct (Nat.le_gt_cases k (length bs1)) as [Hle|Hgt].
  - eapply etriple_conseq with (P := SPA segs (Kw k) PA2a rho1 tp0); [| intros w Hw; exact Hw |].
    { intros w Hw. rewrite <- PA2a_eq. apply SPA_add1; [exact Hw | | apply (below_of_eq _ _ _ _ _ PA2a_eq NxPA2a); reflexivity]. cbn [holds eval branch_taken]. unfold bv_ltu.
      rewrite V13, U92. destruct (Z.ltb_spec (Z.of_nat (length bs1)) (Z.of_nat k)); [lia | discriminate]. }
    eapply erunA_tr; [exact run_PA2a | exact StPA2a | apply Kw_stable; rewrite NxPA2a; cbn; lia |].
    intros L rho2 [<-|[<-|[]]] Hag2; cbn [la_state]; rewrite NxPA2a in Hag2; intros w Hw.
    + exfalso. pose proof (hdA_fact segs rho2 L_PA2a_e _ _ w _ tp0 FPA2ae Hw) as Hf.
      cbn [holds branch_taken eval] in Hf. unfold bv_eqb in Hf. apply negb_true_iff in Hf. rewrite Z.eqb_neq in Hf.
      rewrite <- (proj1 Hag2 92%positive ltac:(cbn; lia)), U92 in Hf.
      rewrite (alu_add2 (rw rho2 13) (rw rho2 15) (Z.of_nat (length bs1)) (Z.of_nat (length bs2))) in Hf;
        [| rewrite <- (proj1 Hag2 13%positive ltac:(cbn; lia)); exact V13
         | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia]. clear -Hf Ek. lia.
    + exists w. split; [apply wsteps_refl|].
      apply (eto_D _ _ rho2 k w ent_PA2a_D S7 ltac:(eapply G_agree; [exact Hag2 | cbn; lia | exact HG1]) ltac:(clear -Ek; rewrite MSG_len; lia) Hw).
  - eapply etriple_conseq with (P := SPA segs (Kw k) PA2b rho1 tp0); [| intros w Hw; exact Hw |].
    { intros w Hw. rewrite <- PA2b_eq. apply SPA_add1; [exact Hw | | apply (below_of_eq _ _ _ _ _ PA2b_eq NxPA2b); reflexivity]. cbn [holds eval branch_taken]. unfold bv_ltu.
      rewrite V13, U92. destruct (Z.ltb_spec (Z.of_nat (length bs1)) (Z.of_nat k)); [reflexivity | lia]. }
    eapply erunA_tr; [exact run_PA2b | exact StPA2b | apply Kw_stable; rewrite NxPA2b; cbn; lia |].
    intros L rho2 [<-|[<-|[]]] Hag2; cbn [la_state]; rewrite NxPA2b in Hag2; intros w Hw.
    + exfalso. pose proof (hdA_fact segs rho2 L_PA2b_e _ _ w _ tp0 FPA2be Hw) as Hf.
      cbn [holds branch_taken eval] in Hf. unfold bv_eqb in Hf. apply negb_true_iff in Hf. rewrite Z.eqb_neq in Hf.
      rewrite <- (proj1 Hag2 92%positive ltac:(cbn; lia)), U92 in Hf.
      rewrite (alu_add2 (rw rho2 13) (rw rho2 15) (Z.of_nat (length bs1)) (Z.of_nat (length bs2))) in Hf;
        [| rewrite <- (proj1 Hag2 13%positive ltac:(cbn; lia)); exact V13
         | rewrite <- (proj1 Hag2 15%positive ltac:(cbn; lia)); exact V15 | lia]. clear -Hf Ek. lia.
    + exists w. split; [apply wsteps_refl|].
      apply (eto_D _ _ rho2 k w ent_PA2b_D S8 ltac:(eapply G_agree; [exact Hag2 | cbn; lia | exact HG1]) ltac:(clear -Ek; rewrite MSG_len; lia) Hw).
Qed.

Theorem wl1_sum_ex : ltac2:(tb__ "0|1|
S0S30S3Q8A1M0A1Vbs1;S37G0A1A3S47U1S31G0Vbs2;A2A2S65S28S3cS28VJ;S2bVrho0;Vtp0;A5S53A3F_;F_;").
Proof using HU15 Hfd Hmax Hrl6 HstJ PA1_eq cert_misc cert_pre cert_runs ent_PA1_D run_PA1 site_Pre_wl1 subs_id wl_fd_rng.
  intros Hnil Hbs2. pose proof rwmax as RWM. rewrite MSG_len in RWM.
  assert (L1z : length bs1 = 0%nat) by (rewrite Hnil; reflexivity).
  pose proof subs_id as SI. cbn [forallb] in SI.
  apply andb_prop in SI as [S1 SI]. apply andb_prop in SI as [S2 SI]. apply andb_prop in SI as [S3 SI].
  apply andb_prop in SI as [S4 SI]. apply andb_prop in SI as [S5 SI]. apply andb_prop in SI as [S6 SI].
  apply andb_prop in SI as [S7 SI]. apply andb_prop in SI as [S8 SI]. apply andb_prop in SI as [S9 SI].
  apply andb_prop in SI as [S10 SI]. apply andb_prop in SI as [S11 SI]. apply andb_prop in SI as [S12 _].
  destruct cert_misc as (Nx2 & R22b & Nx1 & R22c & Nx0 & R22a & Nx0' & R22a' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & FPA1d & FPA1e).
  destruct cert_runs as (_ & _ & _ & _ & _ & NxPA1 & _ & _ & _ & _ & _ & StPA1).
  destruct cert_pre as (_ & B22 & _ & _ & _ & F14).
  intros w0 Hw0. apply SP_Kw0 in Hw0.
  pose proof (SPA_facts_hold segs _ _ _ _ _ Hw0) as HF.
  assert (B14 : bv_unsigned (rw rho0 14) <= 2 ^ 62).
  { pose proof (proj1 (Forall_forall _ _) HF _ F14) as X. cbn [holds eval] in X. rewrite u64_lit in X by lia. exact X. }
  pose proof (urange (rw rho0 14)) as UR14.
  revert w0 Hw0. eapply etriple_seq.
  { apply (ewritev1 Pre_wl1 (SVar 14) (SVar 15) rho0 (length bs2) 0%nat site_Pre_wl1 G0); [rewrite Nx0'; lia | rewrite Nx0'; exact B22 | lia | lia | cbn [eval]; exact HU15 | cbn [eval]; lia |].
    rewrite R22a'. cbn [eval]. exact HU15. }
  apply etriple_ex; intros rho1. apply etriple_ex; intros k.
  apply etriple_pure; intros HG1. apply etriple_pure; intros Hag1. apply etriple_pure; intros Hk. apply etriple_pure; intros Hkb. apply etriple_pure; intros Hfull.
  rewrite Nx0' in Hk, Hag1, Hfull. cbn [Nat.add].
  pose proof (k_full _ _ _ Hk Hfull ltac:(lia) ltac:(lia)) as Ek.
  assert (U92 : bv_unsigned (rw rho1 92) = Z.of_nat k) by (rewrite Hk; apply Z_to_bv_small; rewrite two64; lia).
  pose proof (G15 rho1 HG1) as V15. cbn [eval] in V15.
  eapply etriple_conseq with (P := SPA segs (Kw k) PA1 rho1 tp0); [| intros w Hw; exact Hw |].
  { intros w Hw. rewrite <- PA1_eq. apply SPA_addn; [exact Hw | | apply after_write_below; exact Nx0']. constructor; [|constructor].
    cbn [holds eval]. rewrite U92, u64_lit by lia. lia. }
  eapply erunA_tr; [exact run_PA1 | exact StPA1 | apply Kw_stable; rewrite NxPA1; cbn; lia |].
  intros L rho2 [<-|[<-|[]]] Hag2; cbn [la_state]; rewrite NxPA1 in Hag2; intros w Hw.
  - exfalso. pose proof (hdA_fact segs rho2 L_PA1_e _ _ w _ tp0 FPA1e Hw) as Hf.
    cbn [holds branch_taken eval] in Hf. unfold bv_eqb in Hf. apply negb_true_iff in Hf. rewrite Z.eqb_neq in Hf.
    rewrite <- (proj1 Hag2 92%positive ltac:(cbn; lia)), <- (proj1 Hag2 15%positive ltac:(cbn; lia)), U92, V15 in Hf. clear -Hf Ek. lia.
  - exists w. split; [apply wsteps_refl|].
    apply (eto_D _ _ rho2 k w ent_PA1_D S12 ltac:(eapply G_agree; [exact Hag2 | cbn; lia | exact HG1]) ltac:(clear -Ek L1z; rewrite MSG_len; lia) Hw).
Qed.

End WL.
End WLProofA.
