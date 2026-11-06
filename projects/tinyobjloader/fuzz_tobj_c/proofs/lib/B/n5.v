(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool PArith Lia.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require FastChkA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n2.
From Stdlib Require Sorting.Permutation.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require GlueA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From Stdlib Require Logic.FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout Fs Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MmapFixedA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require SysStartA2.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mprotect.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require MmapBrkA.

(* [comment removed for export] *)
Module Lib_tess_run2d_chk.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "app"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code"; "segs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.Lib_tess_run2d_states"; "FUEL_r2"; "cutpcs_r2"; "cuts_r2"; "exits_r2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.SumConv"; "NF"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "check_cfgA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.FastChkA"; "check_cutA'"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA SoundA EntailA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import FastChkA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Code.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n2.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n2.Lib_tess_run2d_states.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition CC : ltac2:(tb__ "0|0|
S8S0FT;") := ltac2:(tb__ "0|0|
ScS3S4S5S9S1S8S6S7A3A5").

Lemma chk_Pre : CC Pre_r2 = true.  Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Ks : CC Ks = true.       Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Ka : CC Ka = true.       Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Kr : CC Kr = true.       Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Kf : CC Kf = true.       Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Kfan : CC Kfan = true.   Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Km : CC Km = true.       Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Ki : CC Ki = true.       Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Kc : CC Kc = true.       Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Kcm : CC Kcm = true.     Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Kg : CC Kg = true.       Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Kgb : CC Kgb = true.     Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Kgbm : CC Kgbm = true.   Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma chk_Kx : CC Kx = true.       Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma check_r2 : ltac2:(tb__ "0|0|
SaS0SbS3S4S5S9S6S7A6S2A3").
Proof.
  rewrite <- check_cfgA'_eq. unfold check_cfgA'.
  change (forallb_lazy CC [Pre_r2; Ks; Ka; Kr; Kf; Kfan; Km; Ki; Kc; Kcm; Kg; Kgb; Kgbm; Kx] = true).
  apply forallb_lazy_cons_true; [exact chk_Pre|].
  apply forallb_lazy_cons_true; [exact chk_Ks|].
  apply forallb_lazy_cons_true; [exact chk_Ka|].
  apply forallb_lazy_cons_true; [exact chk_Kr|].
  apply forallb_lazy_cons_true; [exact chk_Kf|].
  apply forallb_lazy_cons_true; [exact chk_Kfan|].
  apply forallb_lazy_cons_true; [exact chk_Km|].
  apply forallb_lazy_cons_true; [exact chk_Ki|].
  apply forallb_lazy_cons_true; [exact chk_Kc|].
  apply forallb_lazy_cons_true; [exact chk_Kcm|].
  apply forallb_lazy_cons_true; [exact chk_Kg|].
  apply forallb_lazy_cons_true; [exact chk_Kgb|].
  apply forallb_lazy_cons_true; [exact chk_Kgbm|].
  apply forallb_lazy_cons_true; [exact chk_Kx|].
  reflexivity.
Qed.
End Lib_tess_run2d_chk.

(* [comment removed for export] *)
Module StartGlueA.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "False"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sobj"; "valuation"; "sv"; "SLit"; "eval"; "obj_range"; "ss_objs"; "sstate"; "rm"; "ob_dflt"; "obj_holds"; "ss_next"; "cell"; "odefault"; "DZero"; "mem_match"; "ranges_disjoint"; "rl"; "rw"; "ob_cells"; "ss_facts"; "agree_below"; "smatch"; "enc_bytes"; "mkCell"; "mkObj"; "mkSS"; "ob_base"; "ob_hi"; "ob_lo"; "outside_all"; "rom_ok"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "DImage"; "DUnknown"; "SAlu"; "holds"; "pairwise_disjoint"; "sprop"; "swf"; "SMd"; "c_val"; "dflt_writable"; "image_byte"; "@Corelib.Init.Datatypes"; "list"; "bool"; "option"; "nat"; "cons"; "true"; "app"; "nil"; "pair"; "Some"; "prod"; "fst"; "false"; "snd"; "None"; "length"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "mul"; "modulo"; "of_nat"; "opp"; "div"; "sub"; "ge"; "to_nat"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "leafA"; "ax_X"; "la_state"; "ax_base"; "xr_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "LQA"; "ok_frameA"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "page_size"; "m_vm_lazy"; "m_vmmaps"; "page_in_ranges"; "vm_noaccess"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@Stdlib.Lists.List"; "In"; "nth_error"; "filter"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartDefsA"; "replace_obj_at"; "add_cell_front"; "cells_clear_lit"; "pageZ"; "pages_rev"; "move_obj_last"; "obj_to_unknown"; "unknown_obj_at"; "noX"; "split_chain"; "withX0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "in_ranges"; "wsub"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "same_but_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "image_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "paid"; "vms"; "headroom"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartGlueA.WithSegs"; "drop_zero_cells"; "bump_next"; "KxAt"; "M4096"; "is_zero_cell"; "@Stdlib.PArith.BinPos.Pos"; "le"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "xshadow_outside"; "zero_page_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SummaryA"; "call_checkA"; "entails_frA"; "import_postA"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "Z_to_le_bytes"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_AND"; "M_REMU";
"aluop"; "mulop"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM"; "uncovered"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA GlueA GlueA2 SummaryA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts KxA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import StartDefsA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma ranges_disjoint_sym : ltac2:(tb__ "0|1|
S43S0S0A2M0G0S18R2R1A2S18R2R3A2F_;Fr2;Fr1;").
Proof. intros [a b] [c d]. unfold ranges_disjoint. cbn. lia. Qed.

Lemma pairwise_disjoint_move_last : ltac2:(tb__ "0|1|
S9S39S8A1M0S8G0S32R4S3fS8R3S3dS8R2R1A3A3A2S32R5S3fS8R4S3fS8R2S3dS8R3S40S8A1A3A3A3A2F_;FB;Fx;FA;Frho;").
Proof.
  intros rho A x B H.
  apply pairwise_disjoint_app_inv in H as (HA & HxB & Hcross). cbn in HxB. destruct HxB as [Hx HB].
  apply pairwise_disjoint_app; [exact HA | |].
  - apply pairwise_disjoint_app; [exact HB | cbn; split; constructor |].
    intros o1 o2 H1 [<-|[]]. apply ranges_disjoint_sym. exact (proj1 (Forall_forall _ _) Hx o1 H1).
  - intros o1 o2 H1 H2. apply in_app_iff in H2 as [H2|[<-|[]]].
    + apply Hcross; [exact H1 | right; exact H2].
    + apply Hcross; [exact H1 | left; reflexivity].
Qed.

Lemma mem_match_move_last : ltac2:(tb__ "0|1|
S39S9fA1S9S39S8A1M0S8G0S67S17R6R5S3fS8R4S3dS8R3R2A3A3R1A4S17R7R6S3fS8R5S3fS8R3S3dS8R4S40S8A1A3A3A3R2A4F_;Fms;FB;Fx;FA;Frho;Fsegs;").
Proof.
  intros segs rho A x B ms (Hh & Hpd & Hfr).
  assert (P : Permutation (A ++ x :: B) (A ++ B ++ [x])).
  { apply Permutation_app_head. apply Permutation_cons_append. }
  split; [|split].
  - apply Forall_forall. intros o Ho. apply (proj1 (Forall_forall _ _) Hh o).
    eapply Permutation_in; [apply Permutation_sym; exact P | exact Ho].
  - apply pairwise_disjoint_move_last. exact Hpd.
  - intros a Hout. apply Hfr. unfold outside_all in Hout |- *. apply Forall_forall. intros o Ho.
    apply (proj1 (Forall_forall _ _) Hout o). eapply Permutation_in; [exact P | exact Ho].
Qed.

Lemma firstn_skipn_split : forall {T} (l : list T) i,
  (i < length l)%nat -> exists x, firstn 1 (skipn i l) = [x] /\ l = firstn i l ++ x :: skipn (S i) l.
Proof.
  intros T l. induction l as [|y t IH]; intros i Hi; cbn in Hi; [lia|].
  destruct i as [|i]; cbn.
  - exists y. split; reflexivity.
  - destruct (IH i ltac:(lia)) as (x & H1 & H2). exists x. split; [exact H1|]. rewrite H2 at 1. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma SPA_move_last : ltac2:(tb__ "0|2|
S63S9S5bS3cS39S57Q40A1A1S70S8aR3S48S8SeS5aR4A1A1A2A2S3S39S43SaSaA2M0A1S5eR5A1S40G0A1A3S3S3aS8cS5aR6A1M1S81G1R5A2A2S3eA3S62Vsegs;R9R7R8R5R4A6S62Vsegs;RaS5cR8S81S5aR8A1R7A2A2R9R6R5A6F_;F_;F_;F_;Fw;Ftp;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i tp w Hi HX Hsame Hsp.
  destruct (firstn_skipn_split (ss_objs (ax_S A)) i Hi) as (x & H1 & H2).
  apply (SPA_reobj segs J rho A (move_obj_last (ax_S A) i) tp w Hsame).
  - reflexivity.
  - exact Hsp.
  - destruct Hsp as [Hsm _]. pose proof (smatchA_smatch segs _ _ _ _ Hsm) as S0.
    destruct w as [tr [ms md]]. unfold virt in S0. cbn [w_tr w_cfg fst snd cfg_ms cfg_model] in S0 |- *.
    pose proof (smatch_mm segs _ _ _ _ _ S0) as MM.
    unfold move_obj_last. cbn [ss_objs set_objs]. rewrite H1. rewrite H2 in MM.
    apply mem_match_move_last. exact MM.
  - unfold xshadow_outside. rewrite HX. constructor.
Qed.

Lemma image_byte_none_A : ltac2:(tb__ "0|2|
S57Q40M0A1S4bZ643000S58G0R1A2A2S3S3bS57Q8A1M1A1S38S4aR2A2S47G1A1A3F_;Fa;").
Proof.
  intros a Ha. unfold image_byte, memory_read. change (Z.of_N 1) with 1.
  rewrite (find_segment_none_A (bv_unsigned a) ltac:(lia)). reflexivity.
Qed.

Lemma dzero_obj_bytes_A : ltac2:(tb__ "0|3|
S9S67S8S27S4aR2A2S12S4aR4R3R2A4S3S15S11R3A1S16A3S3S39S14A1S1bR4A1S40S14A1A3S4bZ643000S44S0S0SdR7R5A2A3A2S0S4S4bS44S0S0SdR9R7A2M0A3R1A2S4dR1S46S0S0G0A3A2A2S3S3bS57Q8M1A1M2A1S68R9S59Q40R2A2A2S42G2S59G1Z0A2A2A3F_;Fa;F_;F_;F_;F_;F_;Fo;Fms;Frho;").
Proof.
  intros rho ms o Hrom (Hb & Hw & Hc & Hd & Hi) Hz Hcells Hlo a Ha.
  unfold obj_range in Hlo, Ha. cbn [fst snd] in Hlo, Ha.
  set (b := bv_unsigned (eval rho (ob_base o))) in *.
  specialize (Hd (a - b) ltac:(lia)). rewrite Hcells in Hd.
  assert (Hnc : ~ SymState.covered rho [] (a - b)) by (intros X; inversion X).
  specialize (Hd Hnc). rewrite Hz in Hd. cbn in Hd. replace (b + (a - b)) with a in Hd by lia.
  unfold rd, ms_read_byte in Hd.
  destruct (ms_mem ms (Z_to_bv 64 a)) as [v|] eqn:E; [congruence|].
  exfalso. unfold rom_ok in Hrom. rewrite Hrom in Hd. rewrite image_byte_none_A in Hd; [discriminate|].
  rewrite Z_to_bv_unsigned. pose proof (bv_wrap_small 64 a). change (bv_modulus 64) with (2 ^ 64) in H. lia.
Qed.

Lemma SPA_dzero_bytes_A : ltac2:(tb__ "0|5|
S63S5bS9S39S57Q40M0A1A1S39S6aA1M1S67S69S8S62S4aR8R7R6R5S41G1S74R4S75R3R2A2A4A6S76S8R2SeS5aR8A1A1A3S3S15S11R3A1S16A3S3S39S14A1S1bR4A1S40S14A1A3S4bZ643000S44S0S0SdRaR5A2A3A2S0S4S4bS44S0S0SdRcR7A2M2A3R1A2S4dR1S46S0S0G2A3A2A2S3S3bS57Q8M3A1M4A1S68S90R9RcRaA3S59G0R2A2A2S42G4S59G3Z0A2A2A3F_;Fa;F_;F_;F_;F_;F_;Fo;Fmd;Fms;Ftr;Ftp;Frho;FA;FJ;").
Proof.
  intros J A rho tp tr ms md o [Hsm _] Hin Hz Hcells Hlo.
  pose proof (smatchA_smatch segsA _ _ _ _ Hsm) as S0. unfold virt in S0. cbn [w_tr w_cfg fst snd cfg_ms cfg_model] in S0.
  pose proof (smatch_mm segsA _ _ _ _ _ S0) as (Hh & _ & _).
  pose proof S0 as (_ & _ & _ & _ & Hrom & _). cbn [cfg_ms w_cfg snd] in Hrom.
  apply (dzero_obj_bytes_A rho (vms md tp ms) o Hrom (proj1 (Forall_forall _ _) Hh o Hin) Hz Hcells Hlo).
Qed.

Lemma rm_absorb_inside : ltac2:(tb__ "0|0|
S9S39S8A1S67S57Q40A1S88R4R3R1A3S3S3bS57Q8A1A1S10S87R5R4R3A3R2A2S68R3R2A2A3F_;Fa;Fms;FR;Frho;").
Proof.
  intros rho R ms a H. unfold rho_absorb. cbn [rm].
  destruct (in_ranges_dec rho R a) as [|Hn]; [reflexivity | exfalso; exact (Hn H)].
Qed.

Lemma rm_absorb_outside : ltac2:(tb__ "0|0|
S9S39S8A1S67S57Q40A1S5S88R4R3R1A3A1S3S3bS57Q8A1A1S10S87R5R4R3A3R2A2S10R5R2A2A3F_;Fa;Fms;FR;Frho;").
Proof.
  intros rho R ms a H. unfold rho_absorb. cbn [rm].
  destruct (in_ranges_dec rho R a) as [Hi|]; [exfalso; exact (H Hi) | reflexivity].
Qed.

Lemma rw_absorb : ltac2:(tb__ "0|0|
S9S39S8A1S67S1S3S57Q40A1S1aS87R4R3R2A3R1A2S1aR4R1A2A3Fv;Fms;FR;Frho;").
Proof. intros; reflexivity. Qed.
Lemma rl_absorb : ltac2:(tb__ "0|0|
S9S39S8A1S67S1S3S39S57Q8A1A1S19S87R4R3R2A3R1A2S19R4R1A2A3Fl;Fms;FR;Frho;").
Proof. intros; reflexivity. Qed.

Lemma set_objs_set_objs : ltac2:(tb__ "0|1|
SfS39S8A1M0G0S3SfS8dS8dR3R2A2R1A2S8dR3R1A2A3Fl2;Fl1;FS;").
Proof. intros S l1 l2. reflexivity. Qed.
Lemma set_objs_self : ltac2:(tb__ "0|0|
SfS3SfS8dR1SeR1A1A2R1A3FS;").
Proof. intros S. destruct S; reflexivity. Qed.
Lemma ax_setS_ax_setS : ltac2:(tb__ "0|0|
S5bSfSfS3S5bS5cS5cR3R2A2R1A2S5cR3R1A2A3FS2;FS1;FA;").
Proof. intros A S1 S2. reflexivity. Qed.
Lemma ax_setS_self : ltac2:(tb__ "0|0|
S5bS3S5bS5cR1S5aR1A1A2R1A3FA;").
Proof. intros A. destruct A; reflexivity. Qed.
Lemma ax_S_ax_setS : ltac2:(tb__ "0|0|
S5bSfS3SfS5aS5cR2R1A2A1R1A3FS;FA;").
Proof. intros A S. reflexivity. Qed.

Lemma SPA_prepay_page_rm : ltac2:(tb__ "0|c|
S63S9S5bS57Q40M0A1M1S39G1A1M2S39S6aA1M3S67S69S62S4aR8R6R7R4S41G3S74R3S75R2R1A2A4A6S3S0S50S58G0R6A2S6bA2Z0M4A3S3S3aS6eR7S6cR3A1A2S3eA3S5S76G1R8R7A3A1S0S4S4bG4R1A2S4dR1S6bA2A2S3S3aS98S6fS6dR7A1A1S4cS58G0RbA2R2A2A2S45A3F_;Fj;S55S91R6R9A2S6bA2S79S8S8S18SdReR1A2S41S0S0S58G0RcA2M5S4cG5S6bA2A4A2Lo;SeS5aRcA1A1A3S9S9G2G2R13R4R2ReRcA4R14R4R2RfRdA4F_;Ft';Ft;Fr';Fr;S4bZ643000S58G0RdA2A2S87R10S3dS8S9aReA1S40S8A1A3S90RaS3dG1ReRdA3RbA3A3S9S4S62S4aR12R10R1S3dG1RfReA3S41G3S74RdS75RcRbA2A4A6S4S0S4S4bS58G0R10A2M6R1A2S4dR1S4cG6S6bA2M7A2A2S3S3bS57Q8M8A1M9A1MaS10R3S59G0R2A2A2S42G9S59G8G4A2A2A3F_;Fa;G1S5S4S4bG6S58G0R1A2MbA2S4dGbG7A2A2A1S3GaS10R3R2A2S10R13R2A2A3F_;Fa;A2A2Trho';F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Fp;FA;Frho;FJ;").
Proof.
  intros J rho A p tp tr ms md Hsp Hal Hlz Hnin Hacc Hroom Hdisj HJ Hhigh rho'.
  pose proof (SPA_prepay_zero segsA J rho A p tp tr ms md Hsp Hal Hlz Hnin Hacc Hroom Hdisj ltac:(apply HJ)) as H1.
  pose proof (urange p) as Up. pose proof (page_aligned_end p Hal) as Pend.
  assert (R : obj_range rho (zero_page_obj p) = (bv_unsigned p, bv_unsigned p + page_size)).
  { unfold obj_range, obj_lo_of, obj_hi_of, soff, zero_page_obj. cbn [ob_base ob_lo ob_hi eval].
    rewrite Z_to_bv_bv_unsigned.
    replace (bv_signed (Z_to_bv 64 0)) with 0 by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc).
    change page_size with 4096. replace (bv_signed (Z_to_bv 64 4096)) with 4096 by (OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc). rewrite Z.add_0_r. reflexivity. }
  split; [|split].
  - pose proof (SPA_unobj segsA J rho (ax_setS A (set_objs (ax_S A) (ss_objs (ax_S A) ++ [zero_page_obj p])))
                  (ss_objs (ax_S A)) [zero_page_obj p] (p :: tp) tr ms md eq_refl H1 ltac:(apply HJ)) as H2.
    cbv zeta in H2. rewrite ax_S_ax_setS, ax_setS_ax_setS, set_objs_set_objs, set_objs_self, ax_setS_self in H2. exact H2.
  - intros a Ha. subst rho'. rewrite rm_absorb_inside.
    + apply (SPA_dzero_bytes_A J _ rho (p :: tp) tr ms md (zero_page_obj p) H1);
        [cbn [ax_S ax_setS set_objs ss_objs]; apply in_app_iff; right; left; reflexivity | reflexivity | reflexivity | rewrite R; cbn [fst]; lia | rewrite R; cbn [fst snd]; exact Ha].
    + exists (zero_page_obj p). split; [left; reflexivity|]. rewrite R. cbn [fst snd]. rewrite u64_of_lit; [exact Ha | unfold page_size in Ha, Pend; lia].
  - intros a Ha. subst rho'. apply rm_absorb_outside. intros (o & [<-|[]] & Hr). rewrite R in Hr. cbn [fst snd] in Hr. exact (Ha Hr).
Qed.

Lemma paid_cons_ge : ltac2:(tb__ "0|1|
S69S57Q40A1M0S39G0A1S4bS8fR3R1A2S8fR3S3dG0R2R1A3A2A2Ftp;Fp;Fmd;").
Proof.
  intros md p tp. unfold paid, unpaid. cbn [List.filter].
  destruct (page_in_ranges p (m_vm_lazy md) && negb (page_mem p (m_vm_materialized md))); cbn [length]; unfold page_size; lia.
Qed.
Lemma paid_app_le : ltac2:(tb__ "0|2|
S69S39S57Q40A1M0A1M1G1S4bS8fR3S3fG0R2R1A3A2S4cS8fR3R1A2S4fS6bS51S48G0R2A2A1A2A2A2Ftp;Fl;Fmd;").
Proof.
  intros md l tp. induction l as [|p l IH]; cbn [app length]; [lia|].
  pose proof (paid_cons_le md p (l ++ tp)). rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma eval_ext_rwrl : ltac2:(tb__ "0|1|
S9S9SaS1S3S57Q40A1M0S1aR3R1A2S1aR4R1A2A3Fi;S1S3S39S57Q8A1A1S19R4R1A2S19R5R1A2A3Fl;S3G0ScR4R3A2ScR5R3A2A3F_;F_;Fe;Frho';Frho;").
Proof.
  intros rho rho' e Hrw Hrl. induction e; cbn; rewrite ?IHe1, ?IHe2, ?IHe, ?Hrw, ?Hrl; try reflexivity.
  all: try (rewrite IHe3; reflexivity).
Qed.

Lemma In_pages_rev : ltac2:(tb__ "0|1|
S0S3cS57Q40A1M0S76G0R1S80R3R2A2A3S7S3cS3cS4S8aR1R4A2S3G0R3S7fR5R1A2A3A2Lk;A2F_;Fp;Fn;Fq;").
Proof.
  intros q n p. induction n as [|n IH]; cbn; intros H; [destruct H|].
  destruct H as [<-|H]; [exists n; split; [lia|reflexivity]|].
  destruct (IH H) as (k & Hk & ->). exists k. split; [lia|reflexivity].
Qed.
Lemma length_pages_rev : ltac2:(tb__ "0|0|
S0S3cS3S3cS48S57Q40A1S80R2R1A2A2R1A3Fn;Fq;").
Proof. intros q n. induction n; cbn; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma SPA_prepay_pages_rm : ltac2:(tb__ "0|c|
S63S5bS0S3cS9S39S57Q40M0A1M1A1M2S39S6aA1M3S67S69S62S4aR9R8R5R4S41G3S74R3S75R2R1A2A4A6S9S9G2G2ReR4R2R8R6A4RfR4R2R9R7A4F_;Ft';Ft;Fr';Fr;S3S0S50R9Z1000M4A2Z0M5A3S4bZ643000RaA2S4bS4cRbS4fG4S51RaA1A2A2S4eZ2Z40A2A2S3cS8aR1RcA2S3S3aS6eS7fReR2A2S6cR8A1A2S3eA3F_;Fk;S3cS8aR1RdA2S5S76G1S7fRfR2A2RcA3A1F_;Fk;S0S4S4bRfR1A2S4dR1S4cRfS4fG4S51ReA1M6A2A2A2A2S3S3aS98S6fS6dRaA1A1R2A2S45A3F_;Fz;S55S91R9RcA2S4fS6bG6A2A2S79S8S8S18SdRfR1A2S41S0S0R11S4cR11S4fG4S51R10A1A2A2A4A2Lo;SeS5aR11A1A1A3S7S9S9S4S62S4aR14R13R1S3fG1S80R12R11A2RfA3S41G3S74ReS75RdRcA2A4A6S4S1S3G1S1aR2R1A2S1aR11R1A2A3Fi;S4S1S3S39S57Q8M7A1M8A1S19R2R1A2S19R11R1A2A3Fl;S4S0S4S4bR13R1A2S4dR1S4cR13S4fG4S51R12A1A2A2M9A2A2S3S3bG8A1MaS10R3S59G0R2A2A2S42G8S59G7G5A2A2A3F_;Fa;G1S5S4S4bR13S58G0R1A2MbA2S4dGbG9A2A2A1S3GaS10R3R2A2S10R12R2A2A3F_;Fa;A2A2A2A2Lrho';A2F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Ftp;Frho;Fn;Fq;FA;FJ;").
Proof.
  intros J A q n. induction n as [|n IH]; intros rho tp tr ms md Hsp HJ Hqal Hqlo Hqhi Hlz Hnin Hacc Hroom Hdisj.
  - exists rho. cbn [pages_rev app]. split; [exact Hsp|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
    split; [intros a Ha; cbn in Ha; lia | intros; reflexivity].
  - rewrite Nat2Z.inj_succ in *. unfold page_size in Hroom.
    destruct (IH rho tp tr ms md Hsp HJ Hqal Hqlo ltac:(lia) ltac:(intros k Hk; apply Hlz; lia) ltac:(intros k Hk; apply Hnin; lia)
                 ltac:(intros z Hz; apply Hacc; lia) ltac:(unfold page_size; lia)) as (rho1 & Hsp1 & Hrw1 & Hrl1 & Hz1 & Ho1).
    { apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) Hdisj o Ho) as D. unfold ranges_disjoint in D |- *. cbn [fst snd] in D |- *. lia. }
    set (p := pageZ q n).
    assert (Up : bv_unsigned p = q + 4096 * Z.of_nat n) by (unfold p, pageZ; apply u64_of_lit; lia).
    assert (Hobj : forall o, In o (ss_objs (ax_S A)) -> obj_range rho1 o = obj_range rho o).
    { intros o Ho. unfold obj_range, obj_lo_of, obj_hi_of, soff.
      rewrite !(eval_ext_rwrl rho rho1) by assumption. reflexivity. }
    destruct (SPA_prepay_page_rm J rho1 A p (pages_rev q n ++ tp) tr ms md Hsp1) as (Hsp2 & Hz2 & Ho2).
    + rewrite Up. change page_size with 4096. replace (q + 4096 * Z.of_nat n) with (q + Z.of_nat n * 4096) by lia. rewrite Z_mod_plus_full. exact Hqal.
    + apply Hlz. lia.
    + intros Hin. apply in_app_iff in Hin as [Hin|Hin].
      * apply In_pages_rev in Hin as (k & Hk & E). apply (f_equal bv_unsigned) in E. rewrite Up in E. unfold pageZ in E. rewrite u64_of_lit in E by lia. lia.
      * exact (Hnin n ltac:(lia) Hin).
    + intros j Hj. rewrite Up. apply Hacc. unfold page_size in Hj. lia.
    + unfold headroom in Hroom |- *. pose proof (paid_app_le md (pages_rev q n) tp) as PL. rewrite length_pages_rev in PL. unfold page_size in PL |- *. lia.
    + apply Forall_forall. intros o Ho. rewrite (Hobj o Ho). pose proof (proj1 (Forall_forall _ _) Hdisj o Ho) as D.
      rewrite Up. unfold ranges_disjoint in D |- *. cbn [fst snd] in D |- *. unfold page_size. lia.
    + apply HJ.
    + rewrite Up. lia.
    + cbv zeta in Hsp2, Hz2, Ho2.
      exists (rho_absorb rho1 [zero_page_obj p] (vms md (p :: pages_rev q n ++ tp) ms)).
      split; [exact Hsp2|]. split; [intros i; rewrite rw_absorb; apply Hrw1|]. split; [intros l; rewrite rl_absorb; apply Hrl1|]. split.
      * intros a Ha. destruct (Z_lt_dec a (q + 4096 * Z.of_nat n)) as [Hlt|Hge].
        -- rewrite Ho2; [apply Hz1; lia|]. rewrite u64_of_lit by lia. rewrite Up. unfold page_size. lia.
        -- apply Hz2. rewrite Up. unfold page_size. lia.
      * intros a Ha. rewrite Ho2; [apply Ho1; lia|]. rewrite Up. unfold page_size. lia.
Qed.

Lemma xr_ok_of_zero : ltac2:(tb__ "0|9|
S9S39S8A1S0S43SaSaA2S0S0S58Q40M0ScR6S44SaSaR3A3A2A2S0S58G0ScR7S46SaSaR4A3A2A2S0S3S0S50R2Z8M1A2Z0M2A3S4bS4cR3R2A2S4eZ2Z40A2M3A2S4bG2R6A2S4bR6G3A2S3S0S50R8G1A2G2A3M4G4S0S4S4bR9R1A2S4dR1S4cR9R8A2A2A2S4S4bRcS4cReS53R2G1A2A2M5A2S4dG5RbA2A2F_;Fa;S0S4S4bRcR1A2S4dR1RbA2A2S3S3bS57Q8M6A1M7A1S10R11S59G0R2A2M8A2S42G7S59G6G2A2A2A3F_;Fz;S0S4S4bRdR1A2S4dR1RcA2A2S26R12R11G8A3F_;Fz;S61R11R10RfReA4F_;F_;F_;F_;F_;F_;F_;F_;F_;TL;TB;Fhi;Flo;Fr;Foff;Fobjs;Frho;").
Proof.
  intros rho objs off r lo hi B L HB8 HBL Hlo Hhi Hlo8 Hhi8 Hin Hz Hout.
  unfold xr_ok. cbv zeta. fold B L. split; [exact HB8|]. split; [exact HBL|].
  intros a Ha. pose proof (Hin a Ha) as Hs.
  assert (W : forall j, 0 <= j < 8 -> lo <= (off + a / 8) / 8 * 8 + j < hi).
  { intros j Hj. pose proof (Z.div_mod (off + a / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (off + a / 8) 8 ltac:(lia)).
    apply Z.mod_divide in Hlo8 as [kl Hkl]; [|lia]. apply Z.mod_divide in Hhi8 as [kh Hkh]; [|lia]. nia. }
  split; [lia|]. split.
  - unfold shadow_addr. apply Hout. lia.
  - split.
    + intros j Hj. unfold word_byte. split; [apply Hout; apply W; exact Hj|]. rewrite Hz; [discriminate | apply W; exact Hj].
    + exists (Z_to_bv 8 0). unfold shadow_addr. split; [apply Hz; lia|]. left. reflexivity.
Qed.

Lemma obj_holds_to_unknown : ltac2:(tb__ "0|0|
S9S67S8S3S15S11R1A1S16A3S12S4aR4R3R2A4S12S4aR5R4S82R3A1A4F_;F_;Fo;Fms;Frho;").
Proof.
  intros rho ms o Hz (Hb & Hw & Hc & Hd & Hi). unfold obj_to_unknown. rewrite Hz in *.
  split; [exact Hb|]. split; [exact Hw|]. split; [exact Hc|]. split; [|exact I].
  cbn [ob_dflt ob_cells ob_lo ob_base]. intros off Hoff Hnc. cbn. exists (Z_to_bv 8 0). exact (Hd off Hoff Hnc).
Qed.

Lemma mem_match_to_unknown : ltac2:(tb__ "0|1|
S9S39S8A1M0S8G0S67S3S15S11R3A1S16A3S17S4aR6S3fS8R5S3dS8R4R3A3A3R2A4S17S4aR7S3fS8R6S3dS8S82R5A1R4A3A3R3A4F_;F_;Fms;FB;Fx;FA;Frho;").
Proof.
  intros rho A x B ms Hz (Hh & Hpd & Hfr).
  assert (RNG : obj_range rho (obj_to_unknown x) = obj_range rho x) by reflexivity.
  split; [|split].
  - apply Forall_app in Hh as [HA HxB]. inversion HxB; subst. apply Forall_app. split; [exact HA|]. constructor; [apply obj_holds_to_unknown; assumption | assumption].
  - rewrite (pairwise_disjoint_pdr) in Hpd |- *. rewrite map_app in Hpd |- *. cbn [map] in Hpd |- *. rewrite RNG. exact Hpd.
  - intros a Hout. apply Hfr. unfold outside_all in Hout |- *. rewrite Forall_app in Hout |- *. destruct Hout as [HA HB].
    split; [exact HA|]. inversion HB; subst. constructor; [rewrite <- RNG; assumption | assumption].
Qed.

Lemma SPA_obj_to_unknown : ltac2:(tb__ "0|3|
S63S9S5bS3cS39S57Q40M0A1A1S70S8aR3S48S8SeS5aR4A1A1A2A2S3S39S43SaSaA2M1A1S5eR5A1S40G1A1A3S3S15S11S7bS8R5SeS5aR6A1A1S9aS59G0Z0A2A1A4A1S16A3S3S3aS8cS5aR7A1M2S83G2R6A2A2S3eA3S62S4aRaR8R9R6R5A6S62S4aRbS5cR9S83S5aR9A1R8A2A2RaR7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i tp w Hi HX Hz Hsame Hsp.
  destruct (firstn_skipn_split (ss_objs (ax_S A)) i Hi) as (x & H1 & H2).
  assert (Hx : nth i (ss_objs (ax_S A)) (zero_page_obj (Z_to_bv 64 0)) = x).
  { rewrite H2. rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn. replace (i - Nat.min i (length (ss_objs (ax_S A))))%nat with 0%nat by lia. reflexivity. }
  rewrite Hx in Hz.
  apply (SPA_reobj segsA J rho A (unknown_obj_at (ax_S A) i) tp w Hsame).
  - reflexivity.
  - exact Hsp.
  - destruct Hsp as [Hsm _]. pose proof (smatchA_smatch segsA _ _ _ _ Hsm) as S0.
    destruct w as [tr [ms md]]. unfold virt in S0. cbn [w_tr w_cfg fst snd cfg_ms cfg_model] in S0 |- *.
    pose proof (smatch_mm segsA _ _ _ _ _ S0) as MM.
    unfold unknown_obj_at. cbn [ss_objs set_objs]. rewrite H1. cbn [map]. rewrite H2 in MM.
    apply mem_match_to_unknown; assumption.
  - unfold xshadow_outside. rewrite HX. constructor.
Qed.

Lemma SPA_split_chain : ltac2:(tb__ "0|0|
S63S9S39S43S3cSaA2A1S5bSfS39S57Q40A1A1S70S3S3bSfA1S85S5aR4A1R5A2S42SfR3A2A3S62Vsegs;R8R5R7R3R2A6S62Vsegs;R9S5cR6R5A2R8R4R3A6F_;F_;Fw;Ftp;FS';FA;Fl;Frho;FJ;").
Proof.
  intros J rho l. induction l as [|[i mid] l IH]; intros A S' tp w H Hsp; cbn [split_chain] in H.
  - injection H as <-. rewrite ax_setS_self. exact Hsp.
  - destruct (split_obj_at (ax_S A) i mid) as [S1|] eqn:E; [|discriminate].
    pose proof (SPA_split segs J rho A i mid S1 tp w E Hsp) as H1.
    pose proof (IH (ax_setS A S1) S' tp w H H1) as H2. rewrite ax_setS_ax_setS in H2. exact H2.
Qed.

Definition KxAt (m : Model) (B : Z) (tp0 : list word) : jpredA := ltac2:(tb__ "0|1|
S9S39S57Q40A1A1M0S39S6aA1S69S4S3G0R3Vtp0;A3S8bVm;VB;R4R3R2R1A6A2Lmd;Ltr;Lt;Lr;").

Lemma stableA_KxAt : ltac2:(tb__ "0|0|
S1S69S0S39S57Q40A1A1S64Vsegs;R4S94R3R2R1A3A3Ftp0;FB;Fm;Fn;").
Proof.
  intros n m B tp0 rho rho' tp tr md md' Hag Hme [-> HK]. split; [reflexivity|].
  exact (stableA_KxA segs n m B rho rho' tp0 tr md md' Hag Hme HK).
Qed.

Lemma call_pureA : ltac2:(tb__ "0|4|
S73S5bS5bS39S5dA1S89S39S8A1M0S69S0S39S57Q40A1A1M1S9S73S63S9G1S39S6aA1M2S69R5R4R3R2R1A4S3G2R3S40S6aA1A3F_;Fmd;Ftr;Ftp;Frho;S66Vsegs;RdR2A3F_;FJ;S3S3bG0A1S9cRbRaR8A3S42G0R7A2A3S3S3aS9bRcRbR9R8S7aS5dS5bS5fRaA4A5S3eA3S63S9G1S66Vsegs;R11R3A3S64Vsegs;S13S5aR10A1A1R4A3S72Vsegs;R13S62Vsegs;R5R11R4R3A5S65Vsegs;R5S13S5aR11A1A1M3R4R3R10A6A4F_;F_;Ftp1;Frho1;FJ;S5dS9S76S5dR2ReA3S1dG3R9R2A3S72Vsegs;R13S62Vsegs;S8bRdRcA2S9dRfR11S5fR4A1R12ReA5R3RbA5R9A4F_;F_;Frho';FL;S72Vsegs;R10S62Vsegs;S8bRaR9A2RfR7R8A5R6A4F_;F_;F_;F_;F_;FQ;Frho;Ftp0;FB;Fm;FR;Fs;FPosts;FPre;FC;Fok;").
Proof.
  intros ok C Pre Posts s R m B tp0 rho Q OKF He Hchk Hsum Hcont.
  apply (call_soundA segs ok (KxA m B) (KxAt m B tp0) (KxAt m B tp0) (KxAt m B tp0) C Pre s R Posts Q rho tp0 He Hchk).
  - intros rho1 tp1. apply Hsum; [|apply stableA_KxAt]. apply OKF. intros r t tr md [_ HK]. exact (KxA_nil _ _ _ _ _ _ HK).
  - intros tr ms md Hsm HK. split; [reflexivity | exact HK].
  - intros L rho' rhoL tpL tr ms md tr' md' Hin Hsm HK HLK [-> HK']. split; [reflexivity | exact HK'].
  - intros L rho' tpL Hin Hag n HgQ w [Hsm [-> HK]]. apply (Hcont L rho' Hin Hag n HgQ w). split; [exact Hsm | exact HK].
Qed.

Lemma ecall_pureA : ltac2:(tb__ "0|2|
S5bS5bS39S5dA1S89S39S8A1M0S69S0S39S57Q40A1A1M1S9S70OF_;S3S3bG0A1S9cRaR9R7A3S42G0R6A2A3S3S3aS9bRbRaR8R7S7aS5dS5bS5fR9A4A5S3eA3S63S9G1S64Vsegs;S13S5aReA1A1R3A3S71Vsegs;S62Vsegs;R4RfR3R2A5S65Vsegs;R4S13S5aRfA1A1R3R2ReA6A3F_;Ftp1;Frho1;FJ;S5dS9S76S5dR2RdA3S1dS13S5aR10A1A1R8R2A3S71Vsegs;S62Vsegs;S8bRcRbA2S9dReR10S5fR4A1R11RdA5R3RaA5R8A3F_;F_;Frho';FL;S71Vsegs;S62Vsegs;S8bR9R8A2ReR6R7A5R5A3F_;F_;F_;F_;FQ;Frho;Ftp0;FB;Fm;FR;Fs;FPosts;FPre;FC;").
Proof.
  intros C Pre Posts s R m B tp0 rho Q He Hchk Hsum Hcont.
  apply (call_completeA segs (KxA m B) (KxAt m B tp0) (KxAt m B tp0) (KxAt m B tp0) C Pre s R Posts Q rho tp0 He Hchk).
  - intros rho1 tp1. apply Hsum. apply stableA_KxAt.
  - intros tr ms md Hsm HK. split; [reflexivity | exact HK].
  - intros L rho' rhoL tpL tr ms md tr' md' Hin Hsm HK HLK [-> HK']. split; [reflexivity | exact HK'].
  - intros L rho' tpL Hin Hag w [Hsm [-> HK]]. apply (Hcont L rho' Hin Hag w). split; [exact Hsm | exact HK].
Qed.

Lemma mem_match_replace : ltac2:(tb__ "0|1|
S9S39S8A1M0S8S8G0S67S3S43S0S0A2SdR6R3A2SdR6R4A2A3S12S4aR7R2R5A4S12S4aR8R3R5A4F_;S17S4aR8S3fS8R7S3dS8R6R4A3A3R3A4S17S4aR9S3fS8R8S3dS8R6R5A3A3R4A4F_;F_;F_;Fms;FB;Fo';Fo;FA;Frho;").
Proof.
  intros rho A o o' B ms RNG Himp (Hh & Hpd & Hfr). split; [|split].
  - apply Forall_app in Hh as [HA HxB]. inversion HxB; subst. apply Forall_app. split; [exact HA|]. constructor; [apply Himp; assumption | assumption].
  - rewrite (pairwise_disjoint_pdr) in Hpd |- *. rewrite map_app in Hpd |- *. cbn [map] in Hpd |- *. rewrite RNG. exact Hpd.
  - intros a Hout. apply Hfr. unfold outside_all in Hout |- *. rewrite Forall_app in Hout |- *. destruct Hout as [HA HB].
    split; [exact HA|]. inversion HB; subst. constructor; [rewrite <- RNG; assumption | assumption].
Qed.

Lemma firstn_skipn_of_split : forall {T} (l1 l2 : list T) (a : T),
  firstn (length l1) (l1 ++ a :: l2) = l1 /\ skipn (S (length l1)) (l1 ++ a :: l2) = l2.
Proof.
  intros T l1 l2 a. split.
  - rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r.
  - rewrite skipn_app. replace (S (length l1) - length l1)%nat with 1%nat by lia.
    rewrite skipn_all2 by lia. reflexivity.
Qed.

Lemma outside_all_ranges : ltac2:(tb__ "0|3|
S9S39S8A1M0G0S57Q40A1S3S39S43S0S0A2M1A1S7aS8G1SdR4A1M2R2A4S7aS8G1G2R3A4A3S26R5R4R2A3S26R6R4R3A3F_;F_;Fa;Fobjs';Fobjs;Frho;").
Proof.
  intros rho objs objs' a Hm H. unfold outside_all in *. rewrite Forall_forall in H |- *. intros o' Ho'.
  assert (Hin : In (obj_range rho o') (map (obj_range rho) objs)) by (rewrite <- Hm; apply in_map; exact Ho').
  apply in_map_iff in Hin as (o & Ho & Hino). cbv zeta. rewrite <- Ho. exact (H o Hino).
Qed.

Lemma xshadow_outside_ranges : ltac2:(tb__ "0|3|
S9S5bS39S8A1M0G0S3S39S43S0S0A2M1A1S7aS8G1SdR4A1M2R1A4S7aS8G1G2R2A4A3S99R5R4R3A3S99R6R5R3A3F_;F_;Fobjs';Fobjs;FA;Frho;").
Proof.
  intros rho A objs objs' Hm H. unfold xshadow_outside in *. rewrite Forall_forall in H |- *. intros r Hr a j Ha Hj.
  eapply outside_all_ranges; [exact Hm | exact (H r Hr a j Ha Hj)].
Qed.

Lemma SPA_replace_obj : ltac2:(tb__ "0|1|
S63S9S5bS3cS8S8S39S57Q40A1A1S70S3S3bS8A1S77S8SeS5aR6A1A1R5A3S42S8R4A2A3S3S43S0S0A2SdR8R4A2SdR8R5A2A3S67S27S4aR1A2S12S4aRbR2R8A4S12S4aRcR3R8A4F_;F_;Fms;S3S3aS8cS5aR9A1M0S7cG0R8R6A3A2S3eA3S62S4aRcRaRbR6R5A6S62S4aRdS5cRbS7cS5aRbA1RaR8A3A2RcR7R6A6F_;F_;F_;F_;F_;Fw;Ftp;Fo';Fo;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i o o' tp w Hn RNG Himp Hsame Hsp.
  destruct (nth_error_split _ _ Hn) as (l1 & l2 & Hl & Hlen).
  assert (Eobjs : ss_objs (replace_obj_at (ax_S A) i o') = l1 ++ o' :: l2).
  { unfold replace_obj_at. cbn [ss_objs set_objs]. rewrite Hl, <- Hlen. destruct (firstn_skipn_of_split l1 l2 o) as [-> ->]. reflexivity. }
  apply (SPA_reobj segsA J rho A (replace_obj_at (ax_S A) i o') tp w Hsame).
  - reflexivity.
  - exact Hsp.
  - destruct Hsp as [Hsm _]. pose proof (smatchA_smatch segsA _ _ _ _ Hsm) as S0.
    destruct w as [tr [ms md]]. unfold virt in S0. cbn [w_tr w_cfg fst snd cfg_ms cfg_model] in S0 |- *.
    pose proof (smatch_mm segsA _ _ _ _ _ S0) as MM. pose proof S0 as (_ & _ & _ & _ & Hrom & _). cbn [cfg_ms w_cfg snd] in Hrom.
    rewrite Eobjs. rewrite Hl in MM.
    apply (mem_match_replace rho l1 o o' l2); [exact RNG | apply Himp; exact Hrom | exact MM].
  - destruct Hsp as [Hsm _]. apply (xshadow_outside_ranges rho A (ss_objs (ax_S A))).
    + rewrite Eobjs, Hl, !map_app. cbn [map]. rewrite RNG. reflexivity.
    + apply shadow_ok_outside. exact (smatchA_shadow segsA _ _ _ _ Hsm).
Qed.

Lemma cells_clear_lit_uncovered : ltac2:(tb__ "0|0|
S9S39S14A1S0S0S3S3aS7eR3R2R1A3S3eA3Sa5R5R4R3R2A4F_;Fk;Foff;Fcells;Frho;").
Proof.
  intros rho cells off k H j Hj Hcov. unfold SymState.covered in Hcov. apply Exists_exists in Hcov as (c & Hc & Hin).
  pose proof (proj1 (forallb_forall _ _) H c Hc) as X. cbv beta in X. unfold in_cell in Hin.
  destruct (c_off c) as [co| | | | | | |]; try discriminate. rewrite soff_lit in Hin.
  apply Bool.orb_true_iff in X as [X|X]; [apply Z.leb_le in X | apply Z.leb_le in X]; lia.
Qed.

Lemma obj_holds_add_img_cell : ltac2:(tb__ "0|5|
S9S67S8S0S0S0S0S0S27S4aR7A2S12S4aR9R8R7A4S3S15S11R8A1S2eA3S3SaS23R9A1SbZ0M0A1A3S3SaS25RaA1SbR9A1M1A3S3SaS24RbA1G1A3S4bS52S4eZ2Z3fA2M2A1RbA2S4dRbG2A2S4bRdRbA2S4bS4cRcRbA2RdA2S4S4dG0RcA2S4bRcZ8A2A2S3S3aS7eS1bR11A1ReRdA3S3eA3S3S3bS39S57Q8A1A1M3A1S8eS4aRfS56ReA1M4A3S42G3S1fG4S59Q40RdA2A2A2A3S12S4aR15R14S7dR13S20SbR10A1RfSbReA1A3A2A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fv;Fk;Foff;Fhi;Flo;Fo;Fms;Frho;").
Proof.
  intros rho ms o lo hi off k v Hrom Ho Hz Hb Hlo Hhi Hlo63 Hhi63 H1 H2 Hk Hclr Himg.
  assert (Elo : obj_lo_of rho o = lo) by (unfold obj_lo_of; rewrite Hlo; apply soff_lit_small; lia).
  assert (Ehi : obj_hi_of rho o = hi) by (unfold obj_hi_of; rewrite Hhi; apply soff_lit_small; lia).
  unfold add_cell_front.
  apply (obj_holds_add_cells segsA rho ms o [mkCell (SLit off) k (SLit v)] Ho).
  constructor; [|constructor]. unfold cell_holds. cbn [c_off c_width c_val]. rewrite soff_lit_small by lia. rewrite Elo, Ehi.
  split; [lia|]. split; [lia|].
  rewrite (obj_read_image segsA rho ms o off k _ Hrom Ho Hz Hb ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia) ltac:(lia)
             (cells_clear_lit_uncovered rho _ _ _ Hclr) Himg).
  reflexivity.
Qed.

Lemma SPA_add_img_cell : ltac2:(tb__ "0|8|
S63S9S5bS3cS8S0S0S0S0S0S39S57Q40M0A1A1S70S3S3bS8A1S77S8SeS5aRaA1A1R9A3S42S8R8A2A3S3S15S11R9A1S2eA3S3SaS23RaA1SbZ0M1A1A3S3SaS25RbA1SbRaA1M2A3S3SaS24RcA1G2A3S4bS52S4eZ2Z3fA2M3A1RcA2S4dRcG3A2S4bReRcA2S4bS4cRdRcA2ReA2S4S4dG1RdA2S4bRdZ8A2A2S3S3aS7eS1bR12A1RfReA3S3eA3S3S3bS39S57Q8A1A1M4A1S8eS4aR10S56RfA1M5A3S42G4S1fG5S59G0ReA2A2A2A3S3S3aS8cS5aR16A1M6S7cG6R15S7dR14S20SbR11A1M7R10SbRfA1A3A2A3A2S3eA3S62S4aR19R17R18RfReA6S62S4aR1aS5cR18S7cS5aR18A1R17S7dR16S20SbR13A1R12G7A3A2A3A2R19R10RfA6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Fv;Fk;Foff;Fhi;Flo;Fo;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i o lo hi off k v tp w Hn Hz Hb Hlo Hhi Hlo63 Hhi63 H1 H2 Hk Hclr Himg Hsame Hsp.
  apply (SPA_replace_obj J rho A i o); try assumption.
  - reflexivity.
  - intros ms Hrom Ho. eapply obj_holds_add_img_cell; eauto.
Qed.

Lemma smatch_carve_unknown : ltac2:(tb__ "0|5|
S9SfS39S6aA1M0S67S69SaS0S0S1S1eS4aR9R8S41G0S74R7S75R6R5A2A4A4S22S2bR9A1S2cR9A1S29R9A1S28R9A1S2dR9A1S3fS8SeR9A1S3dS8S21R5SbR4A1SbR3A1S40S14A1S2fA5S40S8A1A3A3S1cR9A1R2S2aR9A1A9SfS3S3aS34R1A1S3eA3S58Q40M1ScRcR7A2A2S0S4bS52S4eZ2M2Z3fA2M3A1R7A2S4S4bR8R7A2S4dR7G3A2A2S4dS54R8R9A2G3A2S4bZ0S4cR4RaA2A2S4bS4cR5RaA2S4eG2Z40A2A2S79S8S8S18SdR13R1A2S41S0S0S4cR7RdA2S4cR7RcA2A4A2Lo';SeR11A1A3S0S4S4bS4cR8ReA2R1A2S4dR1S4cR8RdA2A2A2S5S3S3bS57Q8A1M4A1S10R15S59G1R2A2A2S47G4A1A3A1F_;Fa;S1eS4aR14RaS41G0S74R12S75R11R10A2A4A4F_;F_;F_;F_;F_;F_;F_;Tb;F_;TS';F_;Fnx;Fhi;Flo;Fbase;Fmd;Fms;Ftr;FS;Frho;").
Proof.
  intros rho S tr ms md base lo hi nx Hsm S' Hwf' b Hs1 Hs2 Hs3 Hlo Hhi Hdisj Hbytes.
  destruct Hsm as (Hswf & Hpc & Hpend & Hhalt & Hrom & Hro & Hr & Hf & Hc & Hv & (Hall & Hpd & Hfr) & Hfa).
  cbn [fst snd cfg_ms cfg_model] in *.
  set (newo := mkObj base (SLit lo) (SLit hi) [] DUnknown).
  assert (Hlo' : soff rho (SLit lo) = lo) by (rewrite soff_lit_small; lia).
  assert (Hhi' : soff rho (SLit hi) = hi) by (rewrite soff_lit_small; lia).
  assert (Hnr : obj_range rho newo = (b + lo, b + hi)).
  { unfold obj_range, obj_lo_of, obj_hi_of, newo. cbn [ob_base ob_lo ob_hi]. rewrite Hlo', Hhi'. reflexivity. }
  assert (Hout : forall a, b + lo <= a < b + hi -> outside_all rho (ss_objs S) (Z_to_bv 64 a)).
  { intros a Ha. apply Forall_forall. intros o Ho. cbn zeta. pose proof (proj1 (Forall_forall _ _) Hdisj o Ho) as D.
    unfold ranges_disjoint in D. cbn [fst snd] in D. rewrite u64_of_lit by lia. lia. }
  assert (MEM : forall a, b + lo <= a < b + hi -> exists v, ms_mem ms (Z_to_bv 64 a) = Some v).
  { intros a Ha. rewrite (Hfr _ (Hout a Ha)). destruct (rm rho (Z_to_bv 64 a)) as [v|] eqn:E; [exists v; reflexivity | exfalso; exact (Hbytes a Ha E)]. }
  unfold smatch. cbn [fst snd cfg_ms cfg_model].
  split; [exact Hwf'|]. split; [exact Hpc|]. split; [exact Hpend|]. split; [exact Hhalt|]. split; [exact Hrom|]. split; [exact Hro|].
  split; [exact Hr|]. split; [exact Hf|]. split; [exact Hc|]. split; [exact Hv|]. split; [|exact Hfa].
  cbn [ss_objs]. split; [|split].
  - apply Forall_app. split; [exact Hall|]. constructor; [|constructor].
    unfold obj_holds, obj_lo_of, obj_hi_of, newo. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt dflt_writable]. fold b. rewrite Hlo', Hhi'.
    split; [lia|]. split.
    { intros off Hoff _. unfold wview. destruct (MEM (b + off) ltac:(lia)) as [v Hmv]. rewrite Hmv. discriminate. }
    split; [constructor|]. split; [|exact I].
    intros off Hoff _. unfold dflt_holds, rd, ms_read_byte. destruct (MEM (b + off) ltac:(lia)) as [v Hmv]. rewrite Hmv. exists v. reflexivity.
  - apply pairwise_disjoint_app1; [exact Hpd|]. apply Forall_forall. intros o Ho. fold newo. rewrite Hnr. exact (proj1 (Forall_forall _ _) Hdisj o Ho).
  - intros x Hx. apply outside_all_app in Hx as [Hx1 Hx2]. apply Hfr. exact Hx1.
Qed.

Lemma SPA_carve_unknown : ltac2:(tb__ "0|b|
S63S9S5bS39S57Q40M0A1A1S39S6aA1M1S67S69SaS0S0S1S62S4aRbR9RaR8S41G1S74R7S75R6R5A2A4A6S22S2bS5aRaA1M2A1S2cG2A1S29G2A1S28G2A1S2dG2A1S3fS8SeG2A1S3dS8S21R5SbR4A1SbR3A1S40S14A1S2fA5S40S8A1A3A3S1cG2A1R2S2aG2A1A9SfS3S3aS34R1A1S3eA3S97S13S5aRcA1A1R4A2S58G0ScReR8A2A2S0S4bS52S4eZ2M3Z3fA2M4A1R8A2S4S4bR9R8A2S4dR8G4A2A2S4dS54R9RaA2G4A2S4bZ0M5S4cR4RbA2A2S4bS4cR5RbA2S4eG3Z40A2A2S79S8S8S18SdR15R1A2S41S0S0S4cR7ReA2S4cR7RdA2A4A2Lo';SeS5aR13A1A1A3S0S4S4bS4cR8RfA2R1A2S4dR1S4cR8ReA2A2A2S5S3S3bS57Q8A1M6A1S10R17S59G0R2A2A2S47G6A1A3A1F_;Fa;S43SaSaA2M7S0S0S76G7R3S5eR18A1A3S4S4bS58G0ScR1aS44SaSaR4A3A2A2M8R3A2S4dR3S4cG8S58G0ScR1aS46SaSaR4A3A2A2A2A2A2S4S4bG5R3A2S4dR3Z8M9A2A2S5S4S4bS4cReR15A2S4cS4fS53S4cS58G0ScR1cS60R1bA1A2A2S53R5G9A2A2G9A2G9A2R4A2MaA2S4dGaS4cReR14A2A2A2A1F_;F_;F_;Fj;Fy;Frr;S62S4aR18S5cR16RcA2R17R15S41G1S74R14S75R13R12A2A4A6F_;F_;F_;F_;F_;F_;F_;F_;Tb;F_;F_;TS';F_;Fnx;Fhi;Flo;Fbase;Fmd;Fms;Ftr;Ftp;FA;Frho;FJ;").
Proof.
  intros J rho A tp tr ms md base lo hi nx [(Hsm & HMI & Hwf & Hsh & Hhz) Hk] S' Hwf' Hnx b Hs1 Hs2 Hs3 Hlo Hhi Hdisj Hbytes Hxs.
  split; [|exact Hk].
  split; [|split; [exact HMI | split; [|split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [fst snd cfg_ms cfg_model w_tr w_cfg ax_S ax_setS] in Hsm |- *.
    apply (smatch_carve_unknown rho (ax_S A) tr (vms md tp ms) (vmd md) base lo hi nx Hsm Hwf' Hs1 Hs2 Hs3 Hlo Hhi Hdisj Hbytes).
  - unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  - apply shadow_ok_transport_objs; [|exact Hsh]. cbn [ax_X ax_base ax_S ax_setS ss_objs].
    intros x (rr & y & j & Hr & Hy & Hj & Hz & ->) Hout _.
    apply outside_all_app_iff. split; [exact Hout|].
    constructor; [|constructor]. cbn zeta.
    unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. fold b.
    rewrite !soff_lit_small by lia.
    destruct (word_byte_range _ j Hz Hj) as (B1 & B2 & B3). rewrite B2. exact (Hxs rr y j Hr Hy Hj).
Qed.

Lemma SPA_released_defined : ltac2:(tb__ "0|6|
S63S5bS9S39S57Q40M0A1A1S39S6aA1M1S67S69S39S8A1M2S8S3G2SeS5aR8A1A1S3fS8R2S3dS8R1S40S8A1M3A3A3A3S3S3aS37S11R2A1A1S3eA3S4bZ643000S44S0S0SdR9R3A2A3A2S62S4aRcRbRaR9S41G1S74R8S75R7R6A2A4A6S0S4S4bS44S0S0SdRcR6A2M4A3R1A2S4dR1S46S0S0G4A3A2A2S5S3S3bS57Q8A1M5A1S10S87RdS3dS8R7G3A3S90R9RcRaA3A3S59G0R2A2A2S47G5A1A3A1F_;Fa;F_;F_;F_;F_;Fo;Fobjs;Fmd;Fms;Ftr;Ftp;Frho;FA;FJ;").
Proof.
  intros J A rho tp tr ms md objs o Ho Hw Hlo [Hsm _] a Ha.
  pose proof (smatchA_smatch segsA _ _ _ _ Hsm) as S0. unfold virt in S0. cbn [w_tr w_cfg fst snd cfg_ms cfg_model] in S0.
  pose proof (smatch_mm segsA _ _ _ _ _ S0) as (Hh & _ & _).
  pose proof (proj1 (Forall_forall _ _) Hh o ltac:(rewrite Ho; apply in_app_iff; right; left; reflexivity)) as ((B1 & B2 & B3 & B4) & Hwv & _).
  unfold obj_range in Ha, Hlo. cbn [fst snd] in Ha, Hlo.
  rewrite rm_absorb_inside.
  - specialize (Hwv (a - bv_unsigned (eval rho (ob_base o))) ltac:(lia) Hw).
    replace (bv_unsigned (eval rho (ob_base o)) + (a - bv_unsigned (eval rho (ob_base o)))) with a in Hwv by lia.
    unfold wview in Hwv. destruct (ms_mem (vms md tp ms) (Z_to_bv 64 a)) as [v|] eqn:E; [congruence|].
    exfalso. apply Hwv. change (Z.of_N 1) with 1. rewrite (find_segment_none_A (bv_unsigned (Z_to_bv 64 a))); [reflexivity|].
    rewrite u64_of_lit by lia. lia.
  - exists o. split; [left; reflexivity|]. unfold obj_range. cbn [fst snd]. rewrite u64_of_lit by lia. lia.
Qed.

Definition bump_next (St : sstate) (nx : positive) : sstate := ltac2:(tb__ "0|0|
S22S2bVSt;A1S2cVSt;A1S29VSt;A1S28VSt;A1S2dVSt;A1SeVSt;A1S1cVSt;A1Vnx;S2aVSt;A1A9").

Lemma smatch_bump_agree : ltac2:(tb__ "0|0|
S9S9SfS1S43S39S6aA1S74A2S1dS13R3A1R5R4A3S97S13R4A1R3A2S1eS4aR7R5R3A4S1eS4aR7S93R6R5A2R4A4F_;F_;F_;Fw;Fnx;FS;Frho';Frho;").
Proof.
  intros rho rho' S nx [tr [ms md]] Hag Hle Hsm.
  pose proof (smatch_agree segsA rho rho' S _ Hag Hsm) as H.
  destruct H as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  unfold smatch, bump_next. cbn [fst snd cfg_ms cfg_model ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in *.
  split; [apply swf_mono_next; assumption|].
  repeat (split; [assumption|]). exact Hfacts.
Qed.

Lemma SPA_bump_agree : ltac2:(tb__ "0|1|
S63S9S9S5bS1S39S57Q40A1A1M0S70S9S9G0S39S6aA1S69RcR5R3R2R1A4RdR5R4R3R2A4F_;Fmd;Ftr;Ft;Fr';Fr;S1dS13S5aR5A1A1R7R6A3S97S13S5aR6A1A1R5A2S62S4aRaR7R9R5R4A6S62S4aRbS5cR8S93S5aR8A1R7A2A2R9R6R5A6F_;F_;F_;F_;Fw;Ftp;Fnx;FA;Frho';Frho;FJ;").
Proof.
  intros J rho rho' A nx tp w HJ Hag Hle [(Hsm & HMI & Hwf & Hsh & Hhz) Hk]. split; [|eapply HJ; exact Hk].
  split; [|split; [exact HMI | split; [|split; [|exact Hhz]]]].
  - unfold virt in Hsm |- *. cbn [ax_S ax_setS]. apply (smatch_bump_agree rho rho'); assumption.
  - unfold axwf in Hwf |- *. cbn [ax_S ax_setS ax_X ax_base bump_next ss_next] in Hwf |- *. apply andb_prop in Hwf as [HX Hb].
    apply andb_true_intro. split.
    + apply forallb_forall. intros r Hr. pose proof (proj1 (forallb_forall _ _) HX r Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2]. apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  - apply (shadow_ok_stable A _ rho rho' Hag Hwf (proj1 Hsm) eq_refl eq_refl eq_refl Hsh).
Qed.

Definition M4096 : Z := 18446744073709547520.

Lemma U_and_m4096 : ltac2:(tb__ "0|2|
S9SaS3S0S58Q40M0ScR2S30Sa1R1SbS95A1A3A2A2S54S58G0ScR2R1A2A2M1S50G1Z1000A2A2A3Fe;Frho;").
Proof.
  intros rho e. cbn [eval]. rewrite and_val. unfold M4096. rewrite u64_of_lit by lia.
  change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite land_high_mask; [reflexivity | lia | apply urange].
Qed.

Lemma U_remu_4096 : ltac2:(tb__ "0|2|
S9SaS3S0S58Q40M0ScR2S35Sa2R1SbZ1000M1A1A3A2A2S50S58G0ScR2R1A2A2G1A2A3Fe;Frho;").
Proof.
  intros rho e. cbn [eval]. unfold mul_div. rewrite u64_of_lit by lia. cbn [Z.eqb].
  rewrite bv_modu_unsigned. rewrite u64_of_lit by lia. reflexivity.
Qed.

Lemma U_add_lit : ltac2:(tb__ "0|1|
S9SaS0S4bZ0R1A2S4dS4cS58Q40M0ScR4R3A2A2R2A2S4eZ2Z40A2A2S3S0S58G0ScR5S30Sa0R4SbR3A1A3A2A2S4cS58G0ScR5R4A2A2R3A2A3F_;F_;Fc;Fe;Frho;").
Proof.
  intros rho e c Hc Hb. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned.
  pose proof (urange (eval rho e)). rewrite (bv_wrap_small 64 c) by (change (bv_modulus 64) with (2 ^ 64); lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

Lemma triple_SPA_absurd : ltac2:(tb__ "0|0|
S70OF_;S63S5bS9S39S57Q40A1A1S73S79S33S31R3A1S1cS5aR4A1A1A3S6F_;S72S4aR7S62S4aR6R5R4R3A5R2A4F_;FQ;Ftp;Frho;FA;FJ;Fok;").
Proof.
  intros ok J A rho tp Q H. apply triple_factsA. intros HF. exfalso. exact (H HF).
Qed.
Lemma etriple_SPA_absurd : ltac2:(tb__ "0|0|
S63S5bS9S39S57Q40A1A1S70OF_;S79S33S31R3A1S1cS5aR4A1A1A3S6F_;S71S4aS62S4aR6R5R4R3A5R2A3F_;FQ;Ftp;Frho;FA;FJ;").
Proof.
  intros J A rho tp Q H. apply etriple_factsA. intros HF. exfalso. exact (H HF).
Qed.

Definition is_zero_cell (c : cell) : bool := ltac2:(tb__ "0|4|
SaS3aLx;S36Vc;A1S0S0S3aLz;R1S3eS1S45Lp;M0G0X0x3Lz;S1S45Li;Sa3SaSaS45Lb;La;M1Lop;M2G2Sa4G1Lop;M3G3S3aS2SaS45La;Lw;Lsgn;S1SaS0S45Lk;Li;Ll;Xax8").
Definition drop_zero_cells (o : sobj) : sobj := ltac2:(tb__ "0|0|
S21S23Vo;A1S25Vo;A1S24Vo;A1S78S14S14S49S96R1A1A1Lc;S1bVo;A1A3S11Vo;A1A5").

Lemma Z_to_le_bytes_zero : ltac2:(tb__ "0|4|
S3cS3cS3S57Q8M0A1M1S7bG1R1S9eR2Z0M2A2S59G0G2A2M3A4G3A3Fj;Fk;").
Proof.
  induction k as [|k IH]; intros j; cbn; [destruct j; reflexivity|].
  destruct j as [|j]; [reflexivity|]. change (Z.shiftr 0 8) with 0. apply IH.
Qed.
Lemma enc_bytes_zero : ltac2:(tb__ "0|4|
S3cS3cS3S57Q8M0A1M1S7bG1R1S1fR2S59Q40Z0M2A2A2S59G0G2A2M3A4G3A3Fj;Fk;").
Proof.
  intros k j. unfold enc_bytes. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0. apply Z_to_le_bytes_zero.
Qed.

Lemma obj_holds_drop_zero_cells : ltac2:(tb__ "0|0|
S9S67S8S3S15S11R1A1S16A3S12S4aR4R3R2A4S12S4aR5R4S92R3A1A4F_;F_;Fo;Fms;Frho;").
Proof.
  intros rho ms o Hz (Hb & Hw & Hc & Hd & Hi). unfold drop_zero_cells. rewrite Hz in *.
  split; [exact Hb|]. split; [exact Hw|]. split.
  - apply Forall_forall. intros c Hcin. apply filter_In in Hcin as [Hcin _]. exact (proj1 (Forall_forall _ _) Hc c Hcin).
  - split; [|exact I]. cbn [ob_dflt ob_cells ob_base ob_lo ob_hi]. intros off Hoff Hnc.
    assert (DEC : forall c, {in_cell rho off c} + {~ in_cell rho off c}).
    { intros c0. unfold in_cell. destruct (Z_le_dec (soff rho (c_off c0)) off); [destruct (Z_lt_dec off (soff rho (c_off c0) + c_width c0)); [left; lia | right; lia] | right; lia]. }
    destruct (Exists_dec (in_cell rho off) (ob_cells o) DEC) as [Hcov|Hncov]; [|exact (Hd off Hoff Hncov)].
    unfold SymState.covered in Hcov. apply Exists_exists in Hcov as (c & Hcin & Hin).
    destruct (is_zero_cell c) eqn:Ez.
    2:{ exfalso. apply Hnc. unfold SymState.covered. apply Exists_exists. exists c. split; [|exact Hin]. apply filter_In. split; [exact Hcin|]. rewrite Ez. reflexivity. }
    pose proof (proj1 (Forall_forall _ _) Hc c Hcin) as (C1 & C2 & C3).
    unfold is_zero_cell in Ez. destruct (c_val c) as [z| | | | | | |] eqn:Ev; try discriminate. destruct z; try discriminate.
    cbn [eval] in C3. unfold in_cell in Hin.
    assert (Hnw : bv_unsigned (oaddr rho (ob_base o) (soff rho (c_off c))) + Z.of_nat (Z.to_nat (c_width c)) <= 2 ^ 64).
    { unfold oaddr. rewrite Z_to_bv_unsigned. unfold obj_lo_of, obj_hi_of in *.
      rewrite bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia. }
    pose proof (rd_bytes_nth _ _ _ _ (Z.to_nat (off - soff rho (c_off c))) C3 ltac:(lia) Hnw) as R.
    unfold dflt_holds.
    replace (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off))
      with (Z_to_bv 64 (bv_unsigned (oaddr rho (ob_base o) (soff rho (c_off c))) + Z.of_nat (Z.to_nat (off - soff rho (c_off c))))).
    2:{ unfold oaddr. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
        rewrite Z2Nat.id by lia. rewrite Zplus_mod_idemp_l. f_equal. lia. }
    rewrite R. f_equal. apply enc_bytes_zero.
Qed.

Lemma SPA_drop_zero_cells : ltac2:(tb__ "0|1|
S63S9S5bS3cS8S39S57Q40A1A1S70S3S3bS8A1S77S8SeS5aR5A1A1R4A3S42S8R3A2A3S3S15S11R4A1S16A3S3S3aS8cS5aR7A1M0S7cG0R6S92R5A1A3A2S3eA3S62S4aRaR8R9R5R4A6S62S4aRbS5cR9S7cS5aR9A1R8S92R7A1A3A2RaR6R5A6F_;F_;F_;F_;Fw;Ftp;Fo;Fi;FA;Frho;FJ;").
Proof.
  intros J rho A i o tp w Hn Hz Hsame Hsp.
  apply (SPA_replace_obj J rho A i o); try assumption.
  - reflexivity.
  - intros ms _ Ho. apply obj_holds_drop_zero_cells; assumption.
Qed.

Lemma SPA_X0 : ltac2:(tb__ "0|1|
S63S9S5bS39S57Q40A1A1S70S3S39S43SaSaA2M0A1S5eR3A1S40G0A1A3S62S4aR6R4R5R3R2A6S62S4aR7S86R5A1R6R4R3A6F_;F_;Fw;Ftp;FA;Frho;FJ;").
Proof.
  intros J rho A tp w HX Hsp. unfold withX0, X0.
  replace (mkAX (ax_S A) [(SLit 0, SLit 0)] (ax_base A)) with (ax_setX A ((SLit 0, SLit 0) :: ax_X A)) by (rewrite HX; destruct A; reflexivity).
  apply SPA_x_publish; [reflexivity | | exact Hsp].
  unfold xr_ok. cbn [fst snd eval]. rewrite !u64_of_lit by lia. split; [reflexivity|]. split; [lia|]. intros a Ha. lia.
Qed.
Lemma SPA_noX : ltac2:(tb__ "0|0|
S63S9S5bS39S57Q40A1A1S70S62S4aR5R3R4R2R1A6S62S4aR6S84R4A1R5R3R2A6F_;Fw;Ftp;FA;Frho;FJ;").
Proof.
  intros J rho A tp w Hsp. unfold noX. replace (mkAX (ax_S A) [] (ax_base A)) with (ax_setX A []) by (destruct A; reflexivity).
  apply SPA_x_sub; [intros r [] | exact Hsp].
Qed.

End WithSegs.
End StartGlueA.

(* [comment removed for export] *)
Module StartNodes2.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "reg_sv"; "valuation"; "rw"; "SVar"; "eval"; "rm"; "ss_next"; "ss_objs"; "ss_pc"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_base"; "mkAX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@Corelib.Init.Datatypes"; "list"; "bool"; "nil"; "prod"; "true"; "pair"; "Some"; "option"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "modulo"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "alloc_top"; "m_vmmaps"; "map_has"; "map_remove"; "region_free"; "vm_init_sp"; "vm_maps"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "objs_clear_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "@Stdlib.Lists.List"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes2.Munmap"; "munmap_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple1"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_n"; "mmap_nZ"; "munmap_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA SysCallA MmapA MmapFixedA MmapFixedA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib KxA Placement.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysStartA SysStartA2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section Munmap.
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S32S7S17S10Q40A1A1S17S23A1M0S24R5R4R3R2R1A4S0G0R3S19S23A1A3F_;Fmd;Ftr;Ftp;Frho;S33S16Vok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S32S7S17S10Q40A1A1S17S23A1M0S24R5R4R3R2R1A4S0G0R3S19S23A1A3F_;Fmd;Ftr;Ftp;Frho;S3fS16Vok;R2A3F_;FJ;").

Variables (E : axst) (v : positive) (lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)) (nxt : positive).
Let n : word := Z_to_bv 64 lenZ.
Definition munmap_ok : axst := ltac2:(tb__ "0|1|
S15S3cS13VE;A1M0S5Z0A1SdG0A1Vnxt;A4S19S1aS4S4A2A1S5S2fA1A3").

Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S4S14VE;A1S5S2fA1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S1eS2cA1S3dS16SeS13VE;A1A1A2S1dS2cS2dA2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1Z11A2S5Zd7A1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1ZaA2S9Vv;A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1ZbA2S5VlenZ;A1A3").
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hsmall : lenZ < 2 ^ 62.
Hypothesis Hnxt : ltac2:(tb__ "0|0|
S40ScS13VE;A1A1Vnxt;A2").
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S18S30VGl;S13VE;A1A2S1bA3").
Hypothesis Htop : init_sp_ok (m_vmmaps m).

Lemma n_valM : bv_unsigned n = lenZ.
Proof using Hpos Hsmall. clear - Hpos Hsmall. unfold n. apply u64_of_lit. lia. Qed.
Lemma mmap_n_lit : ltac2:(tb__ "0|2|
S1S0S10Q40M0A1S37S11G0VlenZ;A2M1A1Vn;A3S0S12S38G1A1VlenZ;A3A2").
Proof using Hnl Hpos Hsmall.
  clear - Hnl Hpos Hsmall.
  assert (E : mmap_nZ (Z_to_bv 64 lenZ) = lenZ).
  { unfold mmap_nZ, page_round_up_Z. change page_size with 4096. rewrite u64_of_lit by lia.
    pose proof Hnl as H. apply Z.mod_divide in H as [k Hk]; [|lia]. rewrite Hk.
    replace (k * 4096 + 4096 - 1) with (4095 + k * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  split; [|exact E]. unfold mmap_n, n. rewrite E. reflexivity.
Qed.

Theorem munmap_node : ltac2:(tb__ "0|8|
S7S17S10Q40M0A1M1A1S8R2Vv;A2G1S0S12S22SfG0R1A2Z1000A2Z0A3S3S20S1fSfG0R2A2M2VlenZ;A2Z10000A2S20Z643000G2A2A2S20S1fSfG0R3A2VlenZ;A2S25S26Vm;A1M3A1A2S0S12SfG0S8R6P1A2A2SfG0S2aG3A1A2A3S0S18S27S2bG3A1M4R5Vn;A3S1bA3G1S34S1aG1G1A2S1cG1G1R7R1A4G4A3S0G1R2Vn;A3F_;Fs;S0S18S29S28G4R7A2R7Vn;A3S1bA3S4S12S34S1aS4S12A2S1cS4S12R2R1A4VGl;A3S12S1S20SfG0RcA2M5R1A2S21R1S1fG5VlenZ;A2A2A2S2S1S20SfG0SaRfR5A2A2M6R2A2S21R2S1fG6R4A2A2A2A1F_;Fx;F_;Fsz;Fe;S36S16Vok;S31S16S2eVm;VB;A2VE;RbRaA5S31S16S2eS39Vm;R9Vn;A3VB;A2S35S3bRbS3aSbRbA1R9Vn;A3A2S3eSfG0R9A2M7S1fG7VlenZ;A2RaA3A5A4F_;F_;F_;F_;F_;F_;F_;F_;Ta;Ftp;Frho;").
Proof using All.
  intros rho tp a Hal Hlo Hceil Hv1 Hhas Huniq Hfree HG. pose proof (alloc_top_lt (m_vmmaps m)) as CL. pose proof n_valM as Nv.
  destruct mmap_n_lit as [MN MNZ].
  apply triple1_ecall_detA; [apply OKF; intros; eapply KxA_nil; eassumption | apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & _).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & _).
  rewrite R10 in G0. rewrite R11 in G1. cbn [eval] in G0, G1. change (rw rho v) with a in G0.
  assert (H215 : bv_unsigned (Z_to_bv 64 215) = 215) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite G1. intros E0. apply (f_equal bv_unsigned) in E0. rewrite u64_of_lit in E0 by lia. rewrite u64_of_lit in E0 by lia. lia. }
  assert (Hwrap : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= TASK_SIZE).
  { rewrite G0, G1, MNZ. unfold TASK_SIZE. pose proof (alloc_top_bounds _ Htop) as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB. lia. }
  assert (Hhas' : map_has (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, G1, MN, Evm. exact Hhas. }
  assert (Hal' : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite G0; exact Hal).
  split.
  - eapply (OKP (KxA m B)); [intros; eapply KxA_nil; eassumption | exact HK | exact Hp |].
    apply (munmap_exact_only_okA segsA ms md _ H215 Hal' Hlen Hwrap Hhas').
  - intros w' Hw.
    pose proof (wstep_munmap_exact_invA segsA ms md _ Hh H215 Hal' Hlen Hwrap Hhas' [] w' Hp Hw) as ->.
    rewrite G0, G1, MN.
    set (h' := munmap_vm (m_vmmaps md) a n).
    assert (Emd : munmap_model md a n = vm_forget_range (bv_unsigned a) (bv_unsigned a + bv_unsigned n) (with_vmmaps h' md)) by reflexivity.
    rewrite Emd. split.
    + unfold munmap_ok. rewrite <- Nv.
      replace (mkAX (S_after (ax_S E) (SLit 0) (ss_objs (ax_S E)) nxt) [] (SLit SHB)) with (ax_setS E (S_after (ax_S E) (SLit 0) (ss_objs (ax_S E)) nxt))
        by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
      apply (smatchA_after_munmap segsA rho _ tp E [] ms md [] h' a n (Z_to_bv 64 0) (SLit 0) nxt Hsp).
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * rewrite Evm. exact Huniq.
      * rewrite Evm. exact Hfree.
      * exact Hal.
      * rewrite Nv. exact Hnl.
      * rewrite Nv. unfold two_pow_64 in CL. lia.
      * intros o Ho. rewrite Nv.
        apply (objs_clear_e_sound rho Gl (ax_S E) a lenZ (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear ltac:(lia) ltac:(right; revert Hceil; unfold alloc_top; rewrite stack_max_size_val, <- Hv1; intros Hceil; exact Hceil)); [|exact HG|exact Ho].
        intros x Hx. lia.
      * rewrite HX. intros rr y [].
      * apply agree_below_refl.
      * exact Hnxt.
      * reflexivity.
      * reflexivity.
    + cbn [w_tr w_cfg fst snd cfg_model]. split; [reflexivity|]. split.
      * unfold munmap_model, with_mmap_destroyed. unfold h'. rewrite Evm. apply erase_mat_cong_forget. exact Hem.
      *
        pose proof HMI as (HW & HT & Hmat & Hsub & HpaidMI & Hlc & Hivs & Hlm & Htm).
        pose proof (used_munmap_le md h' a n Hivs ltac:(rewrite Evm; exact Hfree) eq_refl eq_refl) as U1.
        set (md1 := with_vmmaps h' md) in *.
        set (lo := bv_unsigned a) in *. set (hi := lo + bv_unsigned n) in *.
        assert (Wl1 : ivs_wf (m_vm_lazy md1)) by (unfold md1; rewrite m_vm_lazy_with_vmmaps; exact (proj2 (proj2 Hivs))).
        assert (HT' : List.NoDup (tp_forget lo (lo + lenZ) tp)) by (unfold tp_forget; apply List.NoDup_filter; exact HT).
        assert (U2 : (length (unpaid (vm_forget_range lo hi md1) (tp_forget lo (lo + lenZ) tp)) <= length (unpaid md tp))%nat).
        { apply List.NoDup_incl_length; [unfold unpaid; apply List.NoDup_filter; exact HT'|].
          intros p Hpp. assert (Hp' : In p (unpaid (vm_forget_range lo hi md1) tp)).
          { unfold unpaid in Hpp |- *. apply filter_In in Hpp as [Hpp Hb]. apply filter_In. split; [|exact Hb].
            unfold tp_forget in Hpp. apply filter_In in Hpp as [Hpp _]. exact Hpp. }
          pose proof (unpaid_forget_incl md1 lo hi tp p Wl1 Hp') as Hq. unfold md1 in Hq. rewrite (unpaid_ext md (with_vmmaps h' md) tp) in Hq by reflexivity. exact Hq. }
        unfold paid in Hpaid |- *. pose proof page_size_pos. nia.
Qed.
End Munmap.
End StartNodes2.

(* [comment removed for export] *)
Module StartArgF.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "rw"; "sprop"; "SLit"; "valuation"; "SAlu"; "SVar"; "obj_range"; "cell"; "holds"; "mkObj"; "odefault"; "eval"; "ob_base"; "ob_hi"; "ob_lo"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "leb"; "pow"; "mul"; "opp"; "sub"; "@Corelib.Init.Datatypes"; "false"; "bool"; "list"; "nat"; "andb"; "fst"; "snd"; "true"; "Some"; "length"; "option"; "orb"; "prod"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "ALU_SLL"; "aluop"; "mulop"; "branch_cond"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartArgF"; "ARG_LIM"; "arg_layout"; "fact_ule_lit"; "obj_below_b"; "objs_below_except_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartALibS"; "ARGF"; "@Corelib.Lists.ListDef"; "Forall"; "seq"; "@LinuxProcessSemantics.Riscv.Sem"; "alu64"; "@Stdlib.Lists.List"; "existsb"; "In"; "combine"; "forallb"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "eqb"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundV SymSoundR SymFrame Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartALibS.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition ARG_LIM : Z := 0x7fff80000000.

Definition fact_ule_lit (facts : list sprop) (k : positive) (lim : Z) : bool := ltac2:(tb__ "0|6|
S3dS9S9S9S20Lf;R1S33S6S6S1fLb;La;M0Lc;S9S1fLp;G0S6S6S6S20La;R2S0S1fLz;S1S6S20Lb;R2S0S23S23S42R2Vk;A2S1aZ0R1A2A2S1aR1Vlim;A2A2Lc;S1S1fLi;S31S6S6S1fLb0;La0;M1Lop;M2G2S32G1Lop;M3G3S20S2S6S1fLa0;Lw;Lsgn;M4S1S6S0S1fLk0;Li;Ll;M5X6x8Lk';G2G2G3G3G4G5X6x8Lb;La;G0S1fS1S0S1fLa;Li;X9x7Lf;Vfacts;A3").

Lemma fact_ule_lit_sound : ltac2:(tb__ "0|0|
SbS21S9A1S1S0S3aS9S10R4A1R3A3S2dS20S36R4R3R2A3S26A3S17S3Q40S8R6R4A2A2R3A2F_;F_;Flim;Fk;Ffacts;Frho;").
Proof.
  intros rho facts k lim HF Hb. unfold fact_ule_lit in Hb. apply existsb_exists in Hb as (f & Hin & Hf).
  destruct f as [ | | |a b| | | ]; try discriminate. destruct a as [|k'| | | | | |]; try discriminate. destruct b as [z| | | | | | |]; try discriminate.
  apply andb_prop in Hf as [Hf H2]. apply andb_prop in Hf as [H0 H1].
  apply Pos.eqb_eq in H0. subst k'. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as X. cbn [holds eval] in X. rewrite Z_to_bv_unsigned in X.
  pose proof (urange (rw rho k)). unfold bv_wrap in X. change (bv_modulus 64) with (2 ^ 64) in X.
  destruct (Z_lt_dec z (2 ^ 64)); [rewrite Z.mod_small in X by lia; lia | lia].
Qed.

Definition obj_below_b (facts : list sprop) (o : sobj) : bool := ltac2:(tb__ "0|8|
S6S20Lx;M0S16Vo;A1S0G0S15Vo;A1S0S23S23S23S1aS1dS1bZ2Z3eA2M1A1R2A2S1aR2R1A2A2S1aR1G1A2A2G0S14Vo;A1S0S23S1aZ0R1A2S1aS18R1R2A2S34A2A2Lb;S1S20S20L_;S42R1P1A2S1aR2Z10A2S36Vfacts;R1S1eS34R2A2A3X20x2Lk;S31S6S6S1fLb;La;M2Lop;M3G3S32G2Lop;M4G4S20S2S6S1fLa;Lw;Lsgn;M5S1S6S0S1fLk;Li;Ll;M6X6x8A2Lhi;S1S1fLi;M7G3G3G4G4G5G6X6x8Llo;G7G3G3G4G4G5G6X6x8").

Lemma obj_below_sound : ltac2:(tb__ "0|3|
SbS21S9A1S7S4Q40M0A1S3aS9S10R4A1R3A3S17S34S3G0S8R5P1A2A2A2S2dS20S37R5R4A2S26A3S39R7R4A2S2eS2cS17S24S0S0SeR8R6A2M1A3S3G0R5A2M2A2S19G2S25S0S0G1A3A2A2A1F_;F_;F_;F_;Fa;Fo;Ffacts;Frho;").
Proof.
  intros rho facts o a HF H1 Hb [Ha _] Hr.
  unfold obj_below_b in Hb. destruct o as [base lo hi cells dflt]. cbn [ob_lo ob_hi ob_base] in Hb.
  destruct lo as [lo| | | | | | |]; try discriminate. destruct hi as [hi| | | | | | |]; try discriminate.
  apply andb_prop in Hb as [Hb Hbase]. apply andb_prop in Hb as [Hb Hhi]. apply andb_prop in Hb as [Hlo Hlohi].
  apply Z.leb_le in Hlo. apply Z.leb_le in Hlohi. apply Z.leb_le in Hhi.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. cbn [ob_base ob_lo ob_hi fst snd] in Hr.
  rewrite !soff_lit_small in Hr by lia. unfold ARG_LIM in *.
  destruct base as [b|k| | | | | |]; try discriminate.
  - apply andb_prop in Hbase as [Hb0 Hbh]. apply Z.leb_le in Hb0. apply Z.leb_le in Hbh.
    cbn [eval] in Hr. rewrite Z_to_bv_unsigned in Hr. unfold bv_wrap in Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    rewrite Z.mod_small in Hr by lia. lia.
  - cbn [eval] in Hr. destruct (Pos.eqb_spec k 1) as [->|Hk].
    + apply Z.leb_le in Hbase. lia.
    + pose proof (fact_ule_lit_sound rho facts k _ HF Hbase). lia.
Qed.

Definition objs_below_except_b (facts : list sprop) (skip : list nat) (objs : list sobj) : bool := ltac2:(tb__ "0|1|
S40S2bS22S7A2M0G0S2aS3dS22S45S24S22S7R1A3A1Vskip;A3S37Vfacts;S25S22S7R1A3A2A2Lio;S3fS22S7S3bU0S28S7Vobjs;A2A2Vobjs;A4A3").

Lemma combine_seq_In : forall {A} (l : list A) (s : nat) x, In x l -> exists i, In (i, x) (combine (seq s (length l)) l).
Proof.
  intros A l. induction l as [|y l IH]; intros s x Hin; [destruct Hin|].
  destruct Hin as [<-|Hin]; [exists s; left; reflexivity|].
  destruct (IH (S s) x Hin) as [i Hi]. exists i. right. exact Hi.
Qed.
Lemma combine_seq_nth : forall {A} (l : list A) (s i : nat) x, In (i, x) (combine (seq s (length l)) l) -> nth_error l (i - s) = Some x /\ (s <= i)%nat.
Proof.
  intros A l. induction l as [|y l IH]; intros s i x Hin; [destruct Hin|].
  destruct Hin as [E|Hin].
  - injection E as <- <-. rewrite Nat.sub_diag. split; [reflexivity | lia].
  - destruct (IH (S s) i x Hin) as [Hn Hle]. replace (i - s)%nat with (S (i - S s))%nat by lia. cbn. split; [exact Hn | lia].
Qed.

Lemma objs_below_except_sound : ltac2:(tb__ "0|3|
SbS21S9A1S21S22A1S21S7A1S4Q40M0A1S3aS9S10R5A1R4A3S17S34S3G0S8R6P1A2A2A2S2dS20S38R6R5R4A3S26A3S39R8R4A2S22S7S3eS22R2R9A3S2dS29S7A1S41S7R9R3A3S27S7R2A2A3S2eS2cS17S24S0S0SeRdR3A2M1A3S3G0R9A2M2A2S19G2S25S0S0G1A3A2A2A1F_;F_;Fo;Fi;S2eS44RaR7R6A3A1F_;F_;F_;F_;F_;Fa;Fobjs;Fskip;Ffacts;Frho;").
Proof.
  intros rho facts skip objs a HF H1 Hb Ha Hskip (o & Ho & Hr).
  destruct (combine_seq_In objs 0 o Ho) as [i Hi].
  pose proof (proj1 (forallb_forall _ _) Hb _ Hi) as X. cbn [fst snd] in X.
  apply Bool.orb_prop in X as [X|X].
  - apply existsb_exists in X as (j & Hj & Hij). apply Nat.eqb_eq in Hij. subst j.
    destruct (combine_seq_nth objs 0 i o Hi) as [Hn _]. rewrite Nat.sub_0_r in Hn. exact (Hskip i o Hj Hn Hr).
  - exact (obj_below_sound rho facts o a HF H1 X Ha Hr).
Qed.

Lemma U_add_small : ltac2:(tb__ "0|1|
S4Q40M0A1S0S17Z0R1A2S19S18S3G0R3A2R2A2S1bZ2Z40A2A2S2dS0S3G0S3cS2fR4S5G0R3A2A3A2S18S3G0R4A2R3A2A3F_;F_;Fc;Fx;").
Proof.
  intros x c Hc Hb. unfold alu64, alu. rewrite bv_add_unsigned, Z_to_bv_unsigned. pose proof (urange x).
  rewrite (bv_wrap_small 64 c) by (change (bv_modulus 64) with (2 ^ 64); lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma U_add_words : ltac2:(tb__ "0|3|
S4Q40M0A1M1G1S19S18S3G0R2A2M2S3G0R1A2A2S1bZ2Z40A2A2S2dS0S3G0S3cS2fR3R2A3A2S18S3G0R3A2G2A2A3F_;Fy;Fx;").
Proof.
  intros x y Hb. unfold alu64, alu. rewrite bv_add_unsigned. pose proof (urange x). pose proof (urange y).
  apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.
Lemma U_sll3 : ltac2:(tb__ "0|1|
S4Q40M0A1S19S3G0R1A2S1bZ2Z3cA2A2S2dS0S3G0S3cS30R2S5G0Z3A2A3A2S1cZ8S3G0R2A2A2A3F_;Fx;").
Proof.
  intros x Hx. rewrite sll_val. change (3 mod 64) with 3. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  pose proof (urange x). rewrite Z.mod_small by lia. lia.
Qed.

Definition arg_layout (rho : valuation) : Prop := ltac2:(tb__ "0|5|
S2cS17S3Q40M0S8Vrho;P1A2A2M1S1bZ2Z2fA2A2S2cS17S3G0S8Vrho;P2A2A2M2Z400A2S2cS17S3G0S8Vrho;P3A2A2M3Z100A2S2cS17S3G0S8Vrho;P5A2A2Z1ffffA2S2dS0S3G0S8Vrho;P4A2A2S18S18S18G1Zb8A2S1cZ8M4G2A2A2S1cG4G3A2A2A3A2A2A2A2").

Lemma arg_layout_ext : ltac2:(tb__ "0|1|
SbSbS1S43R1P7A2S2dS4Q40A1S8R3R2A2S8R4R2A2A3F_;Fi;S35R3A1M0G0F_;F_;Frho';Frho;").
Proof. intros rho rho' E H. unfold arg_layout in *. rewrite !E by lia. exact H. Qed.

Lemma argf_not_env : ltac2:(tb__ "0|4|
SbS21SfA1S12S4Q40M0A1S35R4A1S39R5R2A2S11ScS2fScS2fSdP1A1ScS30SdP2A1SaZ3A1M1A3A3SaZ10A1A3SaZ0A1ScS2fScS30SdP3A1G1A3SaZ8A1A3R5R4A5S7S2eS2cS17S24S0S0SeR7R1A2M2A3S3G0R4A2M3A2S19G3S25S0S0G2A3A2A2A1To;F_;F_;Fa;Fd;Fcs;Frho;").
Proof.
  intros rho cs d a (L1 & L2 & L3 & L5 & L4) [Ha Hor]. cbv zeta.
  unfold obj_range, obj_lo_of, obj_hi_of, soff. cbn [ob_base ob_lo ob_hi fst snd eval].
  pose proof (urange (rw rho 1%positive)) as U1. pose proof (urange (rw rho 2%positive)) as U2. pose proof (urange (rw rho 3%positive)) as U3.
  pose proof (urange (rw rho 5%positive)) as U5.
  rewrite (U_add_small _ 16); [| lia | rewrite U_add_words; rewrite ?U_sll3; lia].
  rewrite U_add_words by (rewrite U_sll3; lia). rewrite !U_sll3 by lia.
  replace (bv_signed (Z_to_bv 64 0)) with 0 by reflexivity.
  rewrite signed_small by (rewrite U_add_small; rewrite ?U_sll3; lia). rewrite U_add_small by (rewrite ?U_sll3; lia). rewrite U_sll3 by lia.
  lia.
Qed.

Lemma argf_not_str0 : ltac2:(tb__ "0|3|
SbS21SfA1S12S4Q40M0A1S35R4A1S39R5R2A2S11SdP4A1SaZ0A1ScS2fSdP5A1SaZ1A1A3R5R4A5S7S2eS2cS17S24S0S0SeR7R1A2M1A3S3G0R4A2M2A2S19G2S25S0S0G1A3A2A2A1To;F_;F_;Fa;Fd;Fcs;Frho;").
Proof.
  intros rho cs d a (L1 & L2 & L3 & L5 & L4) [Ha Hor]. cbv zeta.
  unfold obj_range, obj_lo_of, obj_hi_of, soff. cbn [ob_base ob_lo ob_hi fst snd eval].
  pose proof (urange (rw rho 5%positive)) as U5. pose proof (urange (rw rho 4%positive)) as U4.
  pose proof (urange (rw rho 1%positive)) as U1. pose proof (urange (rw rho 2%positive)) as U2. pose proof (urange (rw rho 3%positive)) as U3.
  replace (bv_signed (Z_to_bv 64 0)) with 0 by reflexivity.
  rewrite signed_small by (rewrite U_add_small; lia). rewrite U_add_small by lia. lia.
Qed.

Lemma argf_not_based : ltac2:(tb__ "0|3|
SbS6S0S0S21SfA1S12S4Q40M0A1S0S2dS0S3G0S13R8R7A2A2R1A3S2cS17Z0R7A2S17R7R6A2A2S19R7S1bZ2Z3eA2A2S17S18R4R8A2S34A2S17S34S3G0S8RcP1A2A2A2S39RdR7A2S2eS2cS17S24S0S0SeReS11RdSaRcA1SaRbA1RaR9A5A2M1A3S3G0R8A2M2A2S19G2S25S0S0G1A3A2A2A1F_;F_;F_;F_;F_;F_;Fb;Fa;Fd;Fcs;Fhi;Flo;Fe;Frho;").
Proof.
  intros rho e lo hi cs d a b He Hlh Hhi Hb H1 [Ha _].
  unfold obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi fst snd]. rewrite He, !soff_lit_small by lia. lia.
Qed.
End StartArgF.

(* [comment removed for export] *)
Module StartNodes3.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "ex"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "reg_sv"; "valuation"; "ss_next"; "sprop"; "SPUle"; "SVar"; "eval"; "rw"; "SPAlign"; "agree_below"; "rm"; "ss_objs"; "ss_pc"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "mkAX"; "ax_base"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@Corelib.Init.Datatypes"; "prod"; "list"; "nil"; "cons"; "pair"; "bool"; "true"; "Some"; "app"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "m_vmmaps"; "Model"; "vm_maps"; "vm_reserved"; "vm_init_sp"; "VmMaps"; "mkVmMapsFull"; "vm_add_lazy"; "vm_brk"; "vm_limit"; "vm_mmap_base"; "vm_noaccess"; "vm_start_brk"; "with_vmmaps"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "objs_clear_e"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes"; "LB_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "alloc_ceiling_hi"; "mmap_place_ok"; "@Stdlib.Lists.List"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "segments_reserved"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "mmap_flags_core"; "mmap_modeled_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "band_covered"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.StartNodes3.LazyNullRw"; "null_rw_facts"; "null_rw_h"; "null_rw_model"; "null_rw_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "triple1"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "S_after"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "S_ret_lit"; "enomem_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA SysCallA MmapA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts StartLib KxA Placement.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysSpecStart.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A Require Import SysStartA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma mmap_modeled_b_intro_core : ltac2:(tb__ "0|2|
S16Q40M0A1M1G1G1S0S24S17G0R3A2Z3A3S0S24S45R3A1Z22A3S0G1R3S18G0Z0A2A3S0S1fS46R6R5R4A3S20A3F_;F_;F_;Foff;Fflags;Fprot;").
Proof.
  intros prot flags off Hp Hf ->. unfold mmap_modeled_b.
  rewrite Hp, Hf. unfold PROT_READ, PROT_WRITE, PROT_NONE, MAP_PRIVATE, MAP_ANONYMOUS. cbn. reflexivity.
Qed.

Section LazyNullRw.
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S37S7S1bS16Q40A1A1S1bS25A1M0S27R5R4R3R2R1A4S0G0R3S1cS25A1A3F_;Fmd;Ftr;Ftp;Frho;S38S19Vok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S37S7S1bS16Q40A1A1S1bS25A1M0S27R5R4R3R2R1A4S0G0R3S1cS25A1A3F_;Fmd;Ftr;Ftp;Frho;S57S19Vok;R2A3F_;FJ;").

Variables (E : axst) (lenZ : Z) (m : Model) (B : Z) (Gl : list (sv * Z)) (nxt : positive).
Let n : word := Z_to_bv 64 lenZ.
Definition null_rw_h (md : Model) (a : word) : VmMaps := ltac2:(tb__ "0|1|
S26Vmd;A1S2bS2cS29R1A1S1dS1aS16Q40A1M0G0A2S1eG0G0Va;Vn;A4S28R1A1A3S31R1A1S32R1A1S2eR1A1S2fR1A1S30R1A1S2aR1A1A8Th;").
Definition null_rw_model (md : Model) (a : word) : Model := ltac2:(tb__ "0|0|
S2dVa;Vn;S33S4bVmd;Va;A2Vmd;A2A3").

Definition null_rw_facts : list sprop := ltac2:(tb__ "0|2|
S1dS9SeS8S13VE;A1A1M0ZcA2S1dS9SaS5S3fVlenZ;A1A1SbG0A1M1A2S1dS9SaG1S5S3bS41VlenZ;A2A1A2S1cS9A1A3A3A3").
Definition null_rw_ok : axst := ltac2:(tb__ "0|1|
S14S52S4aS53S13VE;A1M0SbS8G0A1A1S11G0A1Vnxt;A4A2S1cS1aS4S4A2A1S5S34A1A3").

Hypothesis HX : ax_X E = [].
Hypothesis Hbase : ltac2:(tb__ "0|0|
S0S4S15VE;A1S5S34A1A3").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S23S3cA1S56S19S12S13VE;A1A1A2S21S3cS3dA2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1Z11A2S5ZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1ZaA2S5Z0A1A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1ZbA2S5VlenZ;A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1ZcA2S5Z3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1ZdA2S5Z4022A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1ZeA2S5ZffffffffffffffffA1A3").
Hypothesis R15 : ltac2:(tb__ "0|0|
S0S4S6S13VE;A1ZfA2S5Z0A1A3").
Hypothesis Hnl : lenZ mod 4096 = 0.
Hypothesis Hpos : 0 < lenZ.
Hypothesis Hsmall : lenZ < 2 ^ 62.
Hypothesis Hnxt : ltac2:(tb__ "0|0|
S58S8S13VE;A1A1Vnxt;A2").
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S1fS35VGl;S13VE;A1A2S20A3").
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S1bS1aS16Q40A1M0G0A2A1S29S26Vm;A1A1S44S19A1A3").

Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hband : ltac2:(tb__ "0|2|
S49S22S1aS16Q40A1M0G0A2S29S26Vm;A1M1A1S28G1A1A3S48S47A3").

Variable rho_of : ltac2:(tb__ "0|0|
S7S16Q40A1S7F_;F_;").
Hypothesis Hrho_ag : ltac2:(tb__ "0|0|
S7S16Q40A1SfS8S13VE;A1A1S51R2S50S10R2A1R1Vn;A3A2Vrho_of;R2R1A2A3Fa;Frho;").
Hypothesis Hrho_at : ltac2:(tb__ "0|1|
S7S16Q40A1M0S0G0SdVrho_of;R2R1A2S8S13VE;A1A1A2R1A3Fa;Frho;").

Lemma n_valW : bv_unsigned n = lenZ.
Proof using Hpos Hsmall. unfold n. apply u64_of_lit. clear -Hpos Hsmall. lia. Qed.

Lemma place_ok_none_of : ltac2:(tb__ "0|3|
S16Q40M0A1M1S27G1G1S42S18G0Z0A2M2R4R3R2R1A5S40G2R4R3R2A4F_;Fa;Flen;Fmd;Fflags;").
Proof. intros flags md len a (P1 & P2 & P3 & P4 & _). unfold mmap_place_ok_none. repeat split; assumption. Qed.

Theorem lazy_null_rw_node : ltac2:(tb__ "0|6|
S7S1bS16Q40M0A1M1A1S4S24S43S1aS4S24A2S1eS4S24R2R1A4VGl;A3S3S2G1G1S2G1G1S1S43S1aG1G1A2S1eG1G1R2R1A4S28S26Vm;A1M2A1A3S1S3aS17G0R2A2M3S17G0ScR7R5A2A2M4A2S3aS39G4R4A2S39G3S17G0R1A2A2A2A2A2Ls;A2Lb;A2S3aS39S17G0ScR5R3A2A2R2A2S3fVlenZ;A1A2A2F_;Fsz;Fe;S0S24S17G0SdR3P1A2A2S17G0S2aG2A1A2A3S4eS19Vok;S36S19S3eVm;VB;A2M5VE;R4R3A5S4fS3S36S19G5S14S54S13VE;A1S55A2S1cS1aS4S4A2A1S5S34A1A3R5R4R1A6S2G1G1S1S40S18G0Z0A2Vm;Vn;R1A4S36S19S3eS4cVm;R1A2VB;A2S4dVrho_of;R6R1A2R5R2A6A2La;A2A2Lw;A4F_;F_;Ftp;Frho;").
Proof using All.
  intros rho tp HG Hv1.
  pose proof n_valW as Nv. pose proof (alloc_top_lt (m_vmmaps m)) as CL.
  apply triple1_ecall_detA; [apply OKF; intros; eapply KxA_nil; eassumption | apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & Efds & Ehalt & Etid & Efs & Estdin).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp. rewrite R17 in Hp. cbn [eval] in Hp.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  pose proof (smatch_pendingA_swf segsA _ _ _ _ Hsp) as Hswf.
  destruct (pending_argsA segsA rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in G0, G1, G2, G3, G4, G5. fold n in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0).
  { rewrite G1. intros X. apply (f_equal bv_unsigned) in X. rewrite Nv in X. change (bv_unsigned (Z_to_bv 64 0)) with 0 in X. lia. }
  assert (Hshape : mmap_modeled_b (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5) = true).
  { apply mmap_modeled_b_intro_core; [rewrite G2; reflexivity | rewrite G3; apply mmap_flags_core_16418; reflexivity | rewrite G5; reflexivity]. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = lenZ).
  { rewrite G1. unfold mmap_nZ, page_round_up_Z, page_size. rewrite Nv.
    pose proof Hnl as Hnl'. apply Z.mod_divide in Hnl' as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 4096 + 4096 - 1) with (4095 + q * 4096) by lia. rewrite Z.div_add by lia. change (4095 / 4096) with 0. lia. }
  assert (HnZ : mmap_n (ms_gpr ms 1) = n) by (unfold mmap_n; rewrite HnZ'; reflexivity).
  split.
  - apply (OKP (KxA m B) ltac:(intros; eapply KxA_nil; eassumption) rho tp [] ms md (Z_to_bv 64 222));
      [split; [reflexivity|split; [exact Hem|exact Hpaid]] | exact Hp |].
    apply (mmap_only_okA segsA ms md _ Hh H222 Hlen Hshape).
  - intros w' Hw.
    destruct (wstep_mmap_invA segsA ms md _ Hh H222 Hlen Hshape [] w' Hp Hw) as [-> | (a & Hpl & ->)].
    + left. split; [|split; [reflexivity|split; [exact Hem|exact Hpaid]]].
      change (mkAX (S_ret_lit (ax_S E) enomem_ret) [] (SLit SHB)) with (ax_setS (mkAX (ax_S E) [] (SLit SHB)) (S_after (ax_S E) (SLit (bv_unsigned (errno_ret ENOMEM))) (ss_objs (ax_S E)) (ss_next (ax_S E)))).
      replace (mkAX (ax_S E) [] (SLit SHB)) with E by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
      eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    + right. exists a.
      rewrite G0, G1 in Hpl.
      assert (HnZn : mmap_nZ n = lenZ) by (rewrite <- G1; exact HnZ').
      assert (Hmn : mmap_n n = n) by (rewrite <- G1 at 1; exact HnZ).
      assert (Hplm : mmap_place_ok_none (Z_to_bv 64 0) m n a).
      { apply (place_ok_none_of (ms_gpr ms 3) m n a). unfold mmap_place_ok in Hpl |- *. rewrite Evm in Hpl.
        destruct Hpl as (P1 & P2 & P3 & P4 & P5). repeat split; try assumption.
        unfold mmap_noreserve_backed_ok in P5 |- *. rewrite G3 in P5 |- *. rewrite (mmap_noreserve_b_16418 (Z_to_bv 64 16418) eq_refl) in P5 |- *. exact P5. }
      split; [exact Hplm|].
      pose proof Hplm as (Pal & Ppos & Pceil & Pfree). rewrite HnZn in Pceil. rewrite Hmn in Pfree.
      pose proof (place_LB_A m lenZ a Htop Hres Hband ltac:(lia) Hnl Hplm) as (PLB & Pimg & Pband & Ptop & Phi).
      assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a n = true) by (rewrite Evm; exact (region_free_app_r _ _ _ _ Pfree)).
      assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = true) by (rewrite G3; apply mmap_noreserve_b_16418; reflexivity).
      unfold mmap_rw_model, mmap_rw_vm, with_mmap_backing. rewrite Enr, HnZ.
      set (rho' := rho_of rho a).
      split.
      * unfold null_rw_ok.
        assert (SM : smatchA segsA rho' tp (ax_setS E (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E)) nxt))
                       ([], mkCfg (after_sys_mem ms a (zero_range (ms_mem ms) a n)) (vm_add_lazy a n (with_vmmaps (null_rw_h md a) md)))).
        { eapply (smatchA_after_grant_lazy segsA rho rho' tp E [] ms md [] (null_rw_h md a)); try exact Hsp.
          -- reflexivity.
          -- reflexivity.
          -- reflexivity.
          -- exact Pal.
          -- rewrite Nv. exact Hnl.
          -- rewrite Nv. exact Hpos.
          -- rewrite Nv. unfold two_pow_64 in CL. lia.
          -- exact Hfree_m.
          -- intros z Hz. apply find_segment_none_A. rewrite Nv in Hz. lia.
          -- intros o Ho. rewrite Nv.
             apply (objs_clear_e_sound rho Gl (ax_S E) a lenZ (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear).
             ++ lia.
             ++ right. revert Pceil. unfold alloc_top. rewrite stack_max_size_val, <- Hv1. intros Pceil. exact Pceil.
             ++ intros x Hx. lia.
             ++ intros e sz Hin x Hx Hblk. destruct (HG e sz Hin) as [(b & s0 & Hm & Hb1 & Hb2) | Hlow]; [|lia].
                pose proof (region_free_In _ _ _ _ _ Hfree_m ltac:(rewrite Evm; exact Hm)) as R.
                unfold iv_overlap in R. rewrite Nv in R.
                apply andb_false_iff in R. destruct R as [R|R]; apply Z.ltb_ge in R; lia.
             ++ exact Ho.
          -- rewrite HX. intros rr y [] _.
          -- subst rho'. apply Hrho_ag.
          -- lia.
          -- cbn. apply Pos.ltb_lt. exact Hnxt.
          -- subst rho'. cbn [eval]. apply Hrho_at. }

        replace E with (mkAX (ax_S E) [] (SLit SHB)) in SM by (destruct E as [S0 X0 b0]; cbn in HX, Hbase |- *; rewrite HX, Hbase; reflexivity).
        destruct SM as (Ssm & SMI & Swf & Ssh & Shz). cbn [ax_S ax_setS ax_X ax_base] in Ssm, Swf, Ssh.
        split; [|split; [exact SMI|split; [|split; [|exact Shz]]]].
        -- cbn [ax_S]. apply smatch_add_facts; [exact Ssm| |].
           ++ unfold null_rw_facts. assert (E1 : rw rho' (ss_next (ax_S E)) = a) by (subst rho'; apply Hrho_at).
              repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E1.
              ** change (2 ^ 12) with 4096. split; [lia|exact Pal].
              ** rewrite u64_of_lit by (pose proof (LB_of_range lenZ); lia). exact PLB.
              ** unfold alloc_ceiling_hi in *. rewrite u64_of_lit by lia. lia.
           ++ assert (X : (ss_next (ax_S E) <? nxt)%positive = true) by (apply Pos.ltb_lt; exact Hnxt). cbn. rewrite !X. reflexivity.
        -- unfold axwf in Swf |- *. cbn [ax_S ax_X ax_base ss_next add_facts] in Swf |- *. exact Swf.
        -- unfold shadow_ok. cbn. constructor.
      * assert (Hclr : tp_clear_of tp (lazy_interior a n)).
        { eapply (tp_clear_of_region_free md); [exact (MI_tp_in_maps segsA _ _ HMI) | exact (proj1 (MI_ivs_wf segsA _ _ HMI)) | exact Hfree_m |].
          rewrite Nv. unfold two_pow_64 in CL. lia. }
        assert (Hpaid' : paid (null_rw_model md a) tp <= B).
        { unfold null_rw_model. rewrite (paid_add_lazy (with_vmmaps (null_rw_h md a) md) a n tp Hclr), paid_with_vmmaps.
          pose proof (used_rw_noreserve_le md (null_rw_h md a) a n (MI_ivs_wf segsA _ _ HMI)
                        Pal ltac:(rewrite Nv; exact Hnl) ltac:(rewrite Nv; exact Hpos)
                        ltac:(rewrite Nv; unfold two_pow_64 in CL; lia) eq_refl eq_refl) as U.
          lia. }
        assert (Hem' : erase_mat (null_rw_model md a) = erase_mat (null_rw_model m a)).
        { unfold null_rw_model, null_rw_h. rewrite <- Evm. apply erase_mat_cong_lazy. exact Hem. }
        split; [reflexivity|split; [exact Hem'|exact Hpaid']].
Qed.
End LazyNullRw.
End StartNodes3.

(* [comment removed for export] *)
Module MuslMalloc40Nodes.


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "div"; "leb"; "pow"; "sub"; "modulo"; "mul"; "opp"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "Z_to_bv"; "bv_sub"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sprop"; "valuation"; "rw"; "eval"; "SLit"; "ss_facts"; "sobj"; "ss_regs"; "holds"; "rm"; "ss_next"; "SVar"; "ss_objs"; "obj_range"; "ranges_disjoint"; "rl"; "SPAlign"; "SPUle"; "ob_base"; "ob_lo"; "sprop_below"; "ss_pc"; "sstate"; "sv_eqb"; "@Corelib.Init.Datatypes"; "list"; "pair"; "prod"; "bool"; "true"; "nil"; "option"; "Some"; "app"; "cons"; "snd"; "fst"; "false"; "andb"; "orb"; "None"; "nat"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "m_vmmaps"; "event"; "vm_maps"; "vm_reserved"; "Model"; "vm_brk"; "m_halted"; "region_free"; "with_vmmaps"; "ENOMEM"; "SyscallEffect"; "errno_ret"; "in_arg"; "VmMaps"; "alloc_top"; "vm_limit"; "vm_start_brk"; "map_contains"; "mkEffectU"; "vm_forget_range"; "vm_noaccess"; "MemCopy"; "m_vm_lazy"; "maps_subtract"; "mkVmMapsFull"; "page_size"; "vm_init_sp"; "vm_mmap_base"; "m_vm_materialized"; "two_pow_64"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "ok_frameA"; "smatchA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_base"; "axst"; "ax_X"; "ax_setS"; "shadow_addr"; "word_byte"; "@Stdlib.Lists.List"; "In"; "forallb"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "sys_input"; "segments_reserved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA"; "KxA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "wstep"; "triple1"; "etriple"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "ms_gpr"; "ms_svc_pending"; "machine_state"; "ms_mem"; "find_segment"; "@Corelib.Lists.ListDef"; "nth"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes.Malloc40"; "TOP"; "brk0w"; "brk0"; "mf_res"; "mg"; "n8w"; "reqw"; "pgw"; "mf_exp"; "n2w"; "n3w"; "rho20f"; "Fgrant"; "mg_dead"; "mgrant"; "RM19"; "a4"; "mg_ok"; "rho20"; "tp20"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.MuslMallocIface"; "D_M"; "facts_M"; "X_M"; "vSP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "mmap_place_ok_none"; "mmap_nZ"; "mmap_fixed_dead_model"; "mmap_fixed_ok_model"; "is_ret"; "mmap_n"; "mmap_none_vm"; "alloc_ceiling_hi"; "alloc_ceiling_lo"; "brk_eff"; "mmap_fixed_dead_vm"; "mmap_fixed_inv"; "mmap_fixed_ok_vm"; "mmap_rw_vm"; "mprotect_expose_inv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.MuslMalloc40States"; "E20f"; "E21f"; "N18"; "refuse"; "E20g"; "E19"; "S20f"; "S20g_ko"; "S21f"; "U24"; "S20g_ok"; "cont"; "E18t"; "S18"; "S19f"; "S19g"; "U24c"; "vBRK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement"; "SHADOW_BAND_LO"; "band_covered"; "SHADOW_BAND_HI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "after_sys"; "after_sys_mem"; "unmap_range"; "zero_range"; "eff_mem";
"@Stdlib.PArith.BinPos.Pos"; "succ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n5.MuslMalloc40Nodes"; "objs_clear_M"; "sp_clear_b"; "obj_clear_M"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "mmap_obj"; "S_after"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect"; "mprotect_model_next"; "mprotect_budget_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "only_okA"; "smatch_pendingA"; "A_after"; "ok_pframeA"; "vm_same"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@LinuxProcessSemantics.LinuxProcessSem.Monad"; "Ok"; "outcome"; "@LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap"; "brk_model_next"; "brk_grow_ok"; "mmap_fixed_noaccess_b"; "mmap_modeled_b"; "mmap_noaccess_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib"; "SHB"; "eblk_clear_b"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "tp_in_maps"; "@LinuxProcessSemantics.LinuxProcessSem.Specs"; "syscall_spec"; "@LinuxProcessSemantics.Riscv.Instr"; "instr"; "Ecall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartLib"; "img_clear_b"; "lit_of"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymHeap"; "enomem_ret"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "instr_at"; "uleq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.BackingAlgebra"; "ivs_wf"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Refusable.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymCall SymSummary Glue3 SymHeap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import
  Restrict BackingAlgebra Virt LedgerA StepA SoundA EntailA CompleteA GlueA GlueA2 SysCallA MmapA MmapFixedA MmapBrkA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require ImageFacts Init Code KxA Placement PlacementA StartLib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n8.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Init OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Code OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.KxA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Placement OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.PlacementA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.StartLib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.StartNodes OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.StartALib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n8.MuslMallocIface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n1.MuslMalloc40States.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma u64_of_lit : ltac2:(tb__ "0|1|
S13S1S5Z0R1A2S7R1SaZ2Z40A2A2A2S0S13SfQ40M0S11G0R2A2A2R2A3F_;Fz;").
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.

Lemma grant_facts_none_A : ltac2:(tb__ "0|6|
S10Q40M0A1M1S44G1G1S93R4R3R2R1A4S0S2fS31G1G1A2M2A1S43S40R4A1A1S6eS15A1A3S1S13S1S5SfG0R4A2M3R1A2S7R1S6G3S94R5A1A2A2A2S3S1S5Z10000R2A2S7R2Z643000A2A2A1F_;Fx;G1G1S69G2S30G1G1R2R1A4S42S40R7A1A1A3S13S1S5SfG0R7A2M4R1A2S7R1S6G4S94R8A1A2A2A2S3S1S5SfG0R5A2M5R2A2S7R2S6G5G3A2A2A2A1F_;Fx;F_;Fm;Fb;A2F_;F_;Fa;Flen;Fmd;Faddr;").
Proof.
  intros addr md len a (Hal & Hpos & Hceil & Hfree) Hres.
  destruct (mmap_nw (m_vmmaps md) a len Hceil) as [En _].
  rewrite Hres, segments_reserved_A in Hfree.
  split.
  - intros x Hx Himg. rewrite <- En in Hx.
    assert (R : forall b m, In (b, m) ([(Z_to_bv 64 0x10000, Z_to_bv 64 0x2b000); (Z_to_bv 64 0x3b000, Z_to_bv 64 0xa6000);
                             (Z_to_bv 64 0xe1000, Z_to_bv 64 0x5000); (Z_to_bv 64 0xe6000, Z_to_bv 64 0x55d000)] ++ vm_maps (m_vmmaps md)) ->
                ~ (bv_unsigned b <= x < bv_unsigned b + bv_unsigned m)).
    { intros b m Hin. exact (region_free_disj _ a (mmap_n len) b m Hfree Hin x Hx). }
    pose proof (R (Z_to_bv 64 0x10000) (Z_to_bv 64 0x2b000) (or_introl eq_refl)) as R1.
    pose proof (R (Z_to_bv 64 0x3b000) (Z_to_bv 64 0xa6000) (or_intror (or_introl eq_refl))) as R2.
    pose proof (R (Z_to_bv 64 0xe1000) (Z_to_bv 64 0x5000) (or_intror (or_intror (or_introl eq_refl)))) as R3.
    pose proof (R (Z_to_bv 64 0xe6000) (Z_to_bv 64 0x55d000) (or_intror (or_intror (or_intror (or_introl eq_refl))))) as R4.
    rewrite !u64_of_lit in R1, R2, R3, R4 by lia. lia.
  - intros b m Hin x Hx. rewrite <- En in Hx. eapply (region_free_disj _ a (mmap_n len) b m Hfree); [|exact Hx].
    apply in_app_iff. right. exact Hin.
Qed.

Lemma smatchA_after_ret_fresh : ltac2:(tb__ "0|4|
S2fScaA1S18S2fS10Q40A1M0A1S64S2fS41A1M1S76S44G1S44G0S2fS17A1Sc6RbRaR9R8S30G1S6bR7S6cR6R5A2A4A5S0S35G0A1S46R4A1S3eG0A1A3Sc9R7R5A2S0S32S6aS17S2bSbcS21S62RbA1A1A1A1R4A3S33A3S7aS17S1fSc0ReS21S62RcA1A1R6A3A1R5A3S61R10Sc0RfS21S62RdA1M2A1M3R7A3ReS66RdSdbR6Sc2G2S22G3A1S23G2A1SbcG3A1A4A2A2S30G1S6bR9S6cSb7RbR7A2R8A2A4A5F_;F_;F_;F_;F_;Fnewfacts;Fr;Fmd';Ftr';Fmd;Fms;Ftr;FA;Ftp;Frho;Fsegs;").
Proof.
  intros segs rho tp A tr ms md tr' md' r newfacts HspA Hh' Hvs Hfb Hf.
  set (nx := ss_next (ax_S A)) in *. set (rho' := rho_set_rw rho nx r) in *.
  assert (Hag : agree_below nx rho rho') by (unfold rho'; apply agree_below_set_rw; lia).
  pose proof HspA as (Hsp & HMI & Hwf & Hsh & Hhz).
  pose proof (smatch_pendingA_swf segs _ _ _ _ HspA) as Hswf.
  set (S' := S_after (ax_S A) (SVar nx) (ss_objs (ax_S A)) (Pos.succ nx)).
  assert (S1 : smatch segs rho' S' (virt tp (tr', mkCfg (after_sys ms r) md'))).
  { unfold virt. cbn [fst snd cfg_ms cfg_model w_tr w_cfg].
    rewrite (vm_same_vms md md' tp _ Hvs), vms_after_sys.
    rewrite virt_unfold in Hsp.
    pose proof (smatch_pending_agree segs _ rho' (ax_S A) tr _ (vmd md) Hag Hsp) as Hsp2.
    unfold after_sys, S'. eapply smatch_after_sys; [exact Hsp2 | | | | | | |].
    + apply model_idle_vmd. exact Hh'.
    + lia.
    + cbn. apply Pos.ltb_lt. lia.
    + unfold rho'. cbn [eval]. apply rho_set_rw_at.
    + apply forallb_forall. intros o Ho. eapply obj_wf_mono; [|exact (proj1 (forallb_forall _ _) (swf_objs _ Hswf) o Ho)]. lia.
    + apply mem_match_after_sys_same. exact (smatch_pending_mem segs _ _ _ _ _ Hsp2).
    + exact (smatch_pending_ro_clear segs _ _ _ _ _ Hsp2). }
  split; [|split; [eapply vm_same_MI; eauto | split; [|split]]].
  - cbn [ax_S ax_setS]. unfold add_facts.
    change (mkSS (ss_pc S') (ss_regs S') (ss_fregs S') (ss_fcsr S') (ss_resv S') (ss_objs S') (newfacts ++ ss_facts S') (ss_next S') (ss_lenient S'))
      with (with_facts S' (newfacts ++ ss_facts S')).
    apply smatch_refacts; [exact S1 | |].
    + unfold S'. cbn [ss_next ss_facts S_after]. rewrite forallb_app. apply andb_true_intro. split; [exact Hfb|].
      apply forallb_forall. intros f Hfi. eapply sprop_below_mono; [|exact (proj1 (forallb_forall _ _) (swf_facts _ Hswf) f Hfi)]. lia.
    + apply Forall_app. split; [exact Hf | exact (smatch_facts segs _ _ _ S1)].
  - unfold axwf in Hwf |- *. cbn. apply andb_prop in Hwf as [HX Hb]. apply andb_true_intro. split.
    + apply forallb_forall. intros rr Hr. pose proof (proj1 (forallb_forall _ _) HX rr Hr) as Y.
      unfold xr_below in Y |- *. apply andb_prop in Y as [Y1 Y2].
      apply andb_true_intro; split; eapply sv_below_mono; try eassumption; lia.
    + eapply sv_below_mono; [|exact Hb]. lia.
  - apply (shadow_ok_stable A _ rho rho' Hag Hwf Hswf eq_refl eq_refl eq_refl Hsh).
  - cbn. intros a Ha. rewrite (vm_same_hid md md' tp Hvs) in Ha. cbn. rewrite (proj1 Hvs). exact (Hhz a Ha).
Qed.

Section BrkA.
  Variable segs : list Segment.
  Variables (ms : machine_state) (m : Model) (x8 : word).
  Hypothesis Hh : m_halted m = None.
  Hypothesis Hno : bv_unsigned x8 = 214%Z.

  Lemma brk_query_only_okA : ltac2:(tb__ "0|1|
S0S10Q40M0A1S74Vms;U0A2S11G0Z0A2A3Sc5S6dVsegs;Vms;Vx8;A3Vm;A2F_;").
  Proof using Hh Hno.
    intros Hq. eapply only_okA_of_inv; [intros R; exact (@brk_query_inv (sys_input segs ms x8) m R Hno Hq)| |].
    - intros E; unfold is_ret in E; discriminate.
    - intros eff m' evs E _; unfold is_ret in E; inversion E; subst;
        cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app]; rewrite materialize_nil; discriminate.
  Qed.

  Lemma wstep_brk_query_invA : ltac2:(tb__ "0|3|
S2fS41A1M0S70S0S35S10Q40M1A1M2A1S75Vms;A1S36G2Vx8;A2A3S0G2S74Vms;U0A2S11G1Z0A2A3S71Vsegs;S30G0S6bR4S6cVms;Vm;A2A4R3A3S0S70R4S30G0S6bR5S6cSb7Vms;S45S40Vm;A1A1A2Vm;A2A4A3F_;F_;F_;Fw';Ftr;").
  Proof using Hh Hno.
    intros tr w' Hp Hq Hw. eapply wstep_ret_invA; [exact Hp | exact Hh | | exact Hh | exact Hw].
    intros R HR. exact (@brk_query_inv (sys_input segs ms x8) m R Hno Hq HR).
  Qed.

  Lemma wstep_brk_query_introA : ltac2:(tb__ "0|3|
S2fS41A1M0S0S35S10Q40M1A1M2A1S75Vms;A1S36G2Vx8;A2A3S0G2S74Vms;U0A2S11G1Z0A2A3S71Vsegs;S30G0S6bR3S6cVms;Vm;A2A4S30G0S6bR3S6cSb7Vms;S45S40Vm;A1A1A2Vm;A2A4A3F_;F_;Ftr;").
  Proof using Hh Hno.
    intros tr Hp Hq. eapply wstep_ret_introA; [exact Hp | exact Hh | | exact Hh].
    exact (@brk_query_intro (sys_input segs ms x8) m Hno Hq).
  Qed.

  Hypothesis Hsb : ltac2:(tb__ "0|2|
S5SfQ40M0S50S40Vm;A1M1A1A2SfG0S45G1A1A2A2").
  Hypothesis Hlt : ltac2:(tb__ "0|1|
S7SfQ40M0S45S40Vm;A1A1A2SfG0S74Vms;U0A2A2A2").

  Lemma brk_grow_only_okA : ltac2:(tb__ "0|0|
Sc5S6dVsegs;Vms;Vx8;A3Vm;A2").
  Proof using Hh Hno Hsb Hlt.
    eapply only_okA_of_inv; [intros R; exact (@brk_grow_inv (sys_input segs ms x8) m R Hno Hsb Hlt)| |].
    - intros [(_ & E) | E]; unfold is_ret in E; discriminate.
    - intros eff m' evs [(_ & E) | E] _; unfold is_ret in E; inversion E; subst;
        cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app]; rewrite materialize_nil; discriminate.
  Qed.

  Lemma wstep_brk_grow_invA : ltac2:(tb__ "0|4|
S2fS41A1M0S70S0S35S10Q40A1M1A1S75Vms;A1S36G1Vx8;A2A3S71Vsegs;S30G0S6bR3S6cVms;Vm;A2A4R2A3S2S1S0S32SceVm;S74Vms;U0A2M2G2A3S33A3S0S70R3S30G0S6bR4S6cSb8Vms;G2SbbVms;S9cS40Vm;A1M3G2G2A3A2A3S48ScdG3G2G2A3Vm;A2A2A4A3A2S0S70R3S30G0S6bR4S6cSb7Vms;S45G3A1A2Vm;A2A4A3A2F_;F_;Fw';Ftr;").
  Proof using Hh Hno Hsb Hlt.
    intros tr w' Hp Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply (@brk_grow_inv (sys_input segs ms x8) m _ Hno Hsb Hlt) in Hspec.
    destruct Hspec as [(Hg & E) | E]; unfold is_ret in E; inversion E; subst.
    - left. split; [exact Hg|].
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
      + cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app brk_eff] in Hm. rewrite materialize_nil in Hm.
        injection Hm as <-. rewrite advance_apply_effect, app_nil_r by reflexivity. reflexivity.
      + exfalso. revert Hcd. rewrite m_halted_with_vmmaps. congruence.
    - right. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
      injection Hm as <-. now rewrite app_nil_r, advance_apply_ret.
  Qed.

  Lemma wstep_brk_grow_intro_failA : forall tr,
    ms_svc_pending ms = Some x8 ->
    brk_grow_ok m (ms_gpr ms 0) (ms_gpr ms 0) = false ->
    wstep segs (tr, mkCfg ms m) (tr, mkCfg (after_sys ms (vm_brk (m_vmmaps m))) m).
  Proof using Hh Hno Hsb Hlt.
    intros tr Hp Hg. eapply wstep_ret_introA; [exact Hp | exact Hh | | exact Hh].
    exact (@brk_grow_intro_fail_ns (sys_input segs ms x8) m Hno Hsb Hlt Hg).
  Qed.

  Lemma wstep_brk_grow_intro_okA : forall tr,
    ms_svc_pending ms = Some x8 ->
    brk_grow_ok m (ms_gpr ms 0) (ms_gpr ms 0) = true ->
    wstep segs (tr, mkCfg ms m)
      (tr, mkCfg (after_sys_mem ms (ms_gpr ms 0) (eff_mem ms (brk_eff (m_vmmaps m) (ms_gpr ms 0) (ms_gpr ms 0))))
                 (with_vmmaps (brk_model_next (m_vmmaps m) (ms_gpr ms 0) (ms_gpr ms 0)) m)).
  Proof using Hh Hno Hsb Hlt.
    intros tr Hp Hg.
    pose proof (@brk_grow_intro_ok (sys_input segs ms x8) m Hno Hsb Hlt Hg) as Hs.
    assert (HM : materialize_model_accesses (with_vmmaps (brk_model_next (m_vmmaps m) (ms_gpr ms 0) (ms_gpr ms 0)) m)
                   (syscall_effect_accesses (brk_eff (m_vmmaps m) (ms_gpr ms 0) (ms_gpr ms 0)))
                 = Some (with_vmmaps (brk_model_next (m_vmmaps m) (ms_gpr ms 0) (ms_gpr ms 0)) m)).
    { cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app brk_eff]. apply materialize_nil. }
    pose proof (wstep_pending_runA segs tr ms m x8 _ _ _ [] Hp Hh Hs ltac:(rewrite m_halted_with_vmmaps; exact Hh) HM) as W.
    rewrite app_nil_r, advance_apply_effect in W by reflexivity. exact W.
  Qed.
End BrkA.

Section FixedNoneA.
  Variable segs : list Segment.
  Variables (ms : machine_state) (m : Model) (x8 : word).
  Let addr := ms_gpr ms 0.
  Let len := ms_gpr ms 1.
  Let flags := ms_gpr ms 3.
  Let n := mmap_n len.
  Hypothesis Hh : m_halted m = None.
  Hypothesis Hno : bv_unsigned x8 = 222%Z.
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hshape : ltac2:(tb__ "0|0|
S0S32ScfS74Vms;U2A2S74Vms;U3A2S74Vms;U5A2A3S33A3").
  Hypothesis Hnot_none : ltac2:(tb__ "0|0|
S0S32Sd1S74Vms;U2A2S74Vms;U3A2S74Vms;U5A2A3S3bA3").
  Hypothesis Hnot_rw : ltac2:(tb__ "0|0|
S0S32Sd0S74Vms;U2A2S74Vms;U3A2S74Vms;U5A2A3S3bA3").
  Hypothesis Hceil : ltac2:(tb__ "0|0|
S5S6SfQ40Vaddr;A2S94Vlen;A1A2S4eS40Vm;A1A1A2").
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S13ScSfQ40Vaddr;A2S59A2Z0A3").
  Hypothesis Hpos : (0 < bv_unsigned addr)%Z.
  Hypothesis Hfree : ltac2:(tb__ "0|0|
S0S32S47S43S40Vm;A1A1Vaddr;Vn;A3S33A3").
  Hypothesis Hcont : ltac2:(tb__ "0|0|
S0S32S51S42S40Vm;A1A1Vaddr;Vn;A3S33A3").

  Let INV : ltac2:(tb__ "0|d|
SccS4aA1M0Sd5S6dVsegs;Vms;Vx8;A3M1Vm;R1A3S2S97R2S4bS49A1M2Vm;S34S41A1M3A4S2S0G0R2ScbS4aS52S4cG1U0A2M4S34S31S10Q40A1M5S2fS10Q8A1A1A2A1M6S34S31G5G5A2M7A1M8S38G7S30G5G5G4S98S4cG1U1A2A1M9A4G8A3MaS34S55A1MbS34S31G5S3fA2A1McA6S96S4cG1U3A2Vm;G4G9A4G3A4A3S0G0R2ScbS4aS52G2G6G8GaGbGcA6S95Vm;G4G9A3G3A4A3A2A2F_;FR;") := ltac2:(tb__ "0|0|
S9eS6dVsegs;Vms;Vx8;A3Vm;VHno;VHlen;VHshape;VHnot_none;VHnot_rw;VHceil;VHalign;VHpos;VHfree;VHcont;Ac").

  Lemma mmap_fixed_ok_model_halted : ltac2:(tb__ "0|1|
S10Q40A1M0G0G0S0S35G0A1S46S96R3Vm;R2R1A4A1S46Vm;A1A3Fk;Fa;Ffl;").
  Proof using .
    intros. unfold mmap_fixed_ok_model, with_mmap_replacement, with_mmap_backing, vm_add_lazy, vm_forget_range.
    destruct (mmap_noreserve_b fl); autorewrite with model; reflexivity.
  Qed.
  Lemma mmap_fixed_dead_model_halted' : ltac2:(tb__ "0|1|
S10Q40A1M0G0S0S35G0A1S46S95Vm;R2R1A3A1S46Vm;A1A3Fk;Fa;").
  Proof using .
    intros. unfold mmap_fixed_dead_model, with_mmap_destroyed, vm_forget_range. autorewrite with model. reflexivity.
  Qed.

  Lemma fixed_none_only_okA : ltac2:(tb__ "0|0|
Sc5S6dVsegs;Vms;Vx8;A3Vm;A2").
  Proof using INV.
    eapply only_okA_of_inv; [intros R; exact (INV R)| |].
    - intros [E | [E | E]]; unfold is_ret in E; discriminate.
    - intros eff m' evs [E | [E | E]] _; unfold is_ret in E; inversion E; subst;
        cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app]; rewrite materialize_nil; discriminate.
  Qed.

  Lemma wstep_fixed_none_invA : ltac2:(tb__ "0|4|
S2fS41A1M0S70S0S35S10Q40A1M1A1S75Vms;A1S36G1Vx8;A2A3S71Vsegs;S30G0S6bR3S6cVms;Vm;A2A4R2A3S2S0S70R3S30G0S6bR4S6cSb7Vms;S4bS49A1M2A2Vm;A2A4A3S2S0S70R3S30G0S6bR4S6cSb8Vms;Vaddr;Sb9S77Vms;A1Vaddr;Vn;A3M3A3S96Vflags;Vm;Vaddr;Vn;A4A2A4A3S0S70R3S30G0S6bR4S6cSb8Vms;G2G3A3S95Vm;Vaddr;Vn;A3A2A4A3A2A2F_;F_;Fw';Ftr;").
  Proof using INV Hh.
    intros tr w' Hp Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply INV in Hspec.
    destruct Hspec as [E | [E | E]]; unfold is_ret in E; inversion E; subst.
    - left. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
      injection Hm as <-. now rewrite app_nil_r, advance_apply_ret.
    - right; left.
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
      + cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
        injection Hm as <-. now rewrite app_nil_r, advance_apply_unmap1.
      + exfalso. revert Hcd. unfold flags, addr, n, len. rewrite mmap_fixed_ok_model_halted. congruence.
    - right; right.
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
      + cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
        injection Hm as <-. now rewrite app_nil_r, advance_apply_unmap1.
      + exfalso. revert Hcd. unfold addr, n, len. rewrite mmap_fixed_dead_model_halted'. congruence.
  Qed.

  Lemma wstep_fixed_none_intro_okA : forall tr,
    ms_svc_pending ms = Some x8 ->
    wstep segs (tr, mkCfg ms m)
      (tr, mkCfg (after_sys_mem ms addr (unmap_range (ms_mem ms) addr n)) (mmap_fixed_ok_model flags m addr n)).
  Proof using Halign Hceil Hcont Hfree Hh Hlen Hno Hnot_none Hnot_rw Hpos Hshape.
    intros tr Hp.
    pose proof (@mmap_fixed_intro_ok (sys_input segs ms x8) m Hno Hlen Hshape Hnot_none Hnot_rw Hceil Halign Hpos Hfree Hcont) as Hs.
    pose proof (wstep_pending_runA segs tr ms m x8 _ _ _ [] Hp Hh Hs ltac:(rewrite mmap_fixed_ok_model_halted; exact Hh) (materialize_nil _)) as W.
    rewrite app_nil_r, advance_apply_unmap1 in W. exact W.
  Qed.

End FixedNoneA.

Lemma maps_subtract_noop : ltac2:(tb__ "0|6|
S2fS31S10Q40M0A1M1G1A2M2A1M3S13S13S5R2R1A2G2S69G2R1R5A3S1S7Z0SfG0S39G1G1R2A3A2M4A2S2S5S6SfG0S3aG1G1R2A3A2M5G4A2R5A2S5R4G5A2A2A2F_;Fr;S0G3S57R5R4R3A3R5A3F_;F_;Fhi;Flo;Fl;").
Proof.
  intros l lo hi Hlh H. induction l as [|[a sz] l IH]; [reflexivity|].
  cbn [maps_subtract]. rewrite IH by (intros r Hr; apply H; right; exact Hr).
  destruct (H (a, sz) (or_introl eq_refl)) as [Hpos Hdis]. cbn [fst snd] in Hpos, Hdis.
  pose proof (urange a) as Ra. pose proof (urange sz) as Rs.
  unfold iv_subtract. destruct Hdis as [Hl | Hr].
  - rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite (proj2 (Z.ltb_ge hi (bv_unsigned a + bv_unsigned sz))) by lia. cbn [app].
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite (proj2 (Z.ltb_ge (bv_unsigned a) lo)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [app].
    rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma vm_forget_range_noop : ltac2:(tb__ "0|6|
S13S13S44S5R3R2A2S31S10Q40M0A1M1G1A2M2S69G2R1S56R3A1A3S1S7Z0SfG0S39G1G1R2A3A2M3A2S2S5S6SfG0S3aG1G1R2A3A2M4G3A2R6A2S5R5G4A2A2A2F_;Fr;G1S69G1R1S5cR4A1A3S3S1S5R7SfG0R2A2M5A2S7G5R6A2A2A1F_;Fp;S0S44S53R6R5R4A3R4A3F_;F_;F_;Fmd;Fhi;Flo;").
Proof.
  intros lo hi md Hlh Hl Hm. unfold vm_forget_range. rewrite (maps_subtract_noop _ lo hi Hlh Hl).
  replace (List.filter (page_outside_range lo hi) (m_vm_materialized md)) with (m_vm_materialized md).
  - apply with_vm_backing_id.
  - symmetry. apply List.forallb_filter_id. apply forallb_forall. intros p Hp. unfold page_outside_range.
    apply negb_true_iff. apply andb_false_iff. destruct (Z.le_gt_cases lo (bv_unsigned p)); [right; apply Z.ltb_ge | left; apply Z.leb_gt]; pose proof (Hm p Hp); lia.
Qed.

Lemma region_free_shrink : ltac2:(tb__ "0|4|
S2fS31S10Q40M0A1M1G1A2A1G1G1G1G1S0S32S47R5R4R3A3S33A3S5SfG0R5A2M2SfG0R3A2M3A2S5S6SfG0R4A2G3A2S6SfG0R6A2G2A2A2S0S32S47R8R5R4A3S33A3F_;F_;F_;Fn';Fa';Fn;Fa;Fl;").
Proof.
  intros l a n a' n' Hf H1 H2. apply region_free_of_forall. intros b s Hin.
  pose proof (region_free_In _ _ _ _ _ Hf Hin) as Q. unfold iv_overlap in Q |- *.
  apply andb_false_iff in Q. apply andb_false_iff. destruct Q as [Q|Q]; apply Z.ltb_ge in Q; [left|right]; apply Z.ltb_ge; lia.
Qed.

Section MprotectA.
  Variable segs : list Segment.
  Variables (ms : machine_state) (m : Model) (x8 : word).
  Let addr := ms_gpr ms 0.
  Let len := ms_gpr ms 1.
  Let n := mmap_n len.
  Hypothesis Hh : m_halted m = None.
  Hypothesis Hno : bv_unsigned x8 = 226%Z.
  Hypothesis Hprot : bv_unsigned (ms_gpr ms 2) = 3%Z.
  Hypothesis Halign : ltac2:(tb__ "0|0|
S0S13ScSfQ40Vaddr;A2S59A2Z0A3").
  Hypothesis Hlen : len <> Z_to_bv 64 0.
  Hypothesis Hwrap : ltac2:(tb__ "0|0|
S7S6SfQ40Vaddr;A2S94Vlen;A1A2S5dA2").
  Hypothesis Hna : ltac2:(tb__ "0|0|
S0S32S51S54S40Vm;A1A1Vaddr;Vn;A3S33A3").
  Hypothesis Hmp : ltac2:(tb__ "0|0|
S0S32S51S42S40Vm;A1A1Vaddr;Vn;A3S33A3").

  Let INV : ltac2:(tb__ "0|9|
SccS4aA1M0Sd5S6dVsegs;Vms;Vx8;A3M1Vm;R1A3S2S97R2S4bS49A1Vm;S34S41A1M2A4S1S0S32Sc4Vm;S4cG1U0A2M3S98S4cG1U1A2A1M4A3S33A3S0G0R2ScbS4aS52S11Q40M5Z0A2S34S31S10G5A1M6S2fS10Q8A1A1A2A1S38S31G6G6A2M7S30G6G6G3G4A4S34G7A1M8A3G8S34S55A1S34S31G6S3fA2A1A6Sc3Vm;G3G4A3G2A4A3A2A2F_;FR;") := ltac2:(tb__ "0|0|
Sa1S6dVsegs;Vms;Vx8;A3Vm;VHno;VHprot;VHalign;VHlen;VHwrap;VHna;VHmp;A9").

  Lemma mprotect_model_next_halted : ltac2:(tb__ "0|1|
S10Q40A1M0G0S0S35G0A1S46Sc3Vm;R2R1A3A1S46Vm;A1A3Fk;Fa;").
  Proof using . intros. unfold mprotect_model_next. autorewrite with model. reflexivity. Qed.

  Lemma mprotect_expose_only_okA : ltac2:(tb__ "0|0|
Sc5S6dVsegs;Vms;Vx8;A3Vm;A2").
  Proof using INV.
    eapply only_okA_of_inv; [intros R; exact (INV R)| |].
    - intros [E | [_ E]]; unfold is_ret in E; discriminate.
    - intros eff m' evs [E | [_ E]] _; unfold is_ret in E; inversion E; subst;
        cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app]; rewrite materialize_nil; discriminate.
  Qed.

  Lemma wstep_mprotect_expose_invA : ltac2:(tb__ "0|3|
S2fS41A1M0S70S0S35S10Q40M1A1M2A1S75Vms;A1S36G2Vx8;A2A3S71Vsegs;S30G0S6bR3S6cVms;Vm;A2A4R2A3S2S0S70R3S30G0S6bR4S6cSb7Vms;S4bS49A1A2Vm;A2A4A3S0S70R3S30G0S6bR4S6cSb8Vms;S11G1Z0A2SbaS77Vms;A1Vaddr;Vn;A3A3Sc3Vm;Vaddr;Vn;A3A2A4A3A2F_;F_;Fw';Ftr;").
  Proof using INV Hh.
    intros tr w' Hp Hw.
    destruct (wstep_pending_inv Hp Hh Hw) as (eff & m' & evs0 & Hspec & Hcases).
    apply INV in Hspec.
    destruct Hspec as [E | [Hb E]]; unfold is_ret in E; inversion E; subst.
    - left. destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)]; [|congruence].
      cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
      injection Hm as <-. now rewrite app_nil_r, advance_apply_ret.
    - right.
      destruct Hcases as [(Hh' & m'' & Hm & ->) | (code & Hcd & _)].
      + cbn [syscall_effect_accesses eff_copyins eff_writes write_accesses app] in Hm. rewrite materialize_nil in Hm.
        injection Hm as <-. now rewrite app_nil_r, advance_apply_zero1.
      + exfalso. revert Hcd. unfold addr, n, len. rewrite mprotect_model_next_halted. congruence.
  Qed.

  Lemma wstep_mprotect_expose_intro_failA : ltac2:(tb__ "0|2|
S2fS41A1M0S0S35S10Q40A1M1A1S75Vms;A1S36G1Vx8;A2A3S0S32Sc4Vm;Vaddr;Vn;A3S3bA3S71Vsegs;S30G0S6bR3S6cVms;Vm;A2A4S30G0S6bR3S6cSb7Vms;S4bS49A1A2Vm;A2A4A3F_;F_;Ftr;").
  Proof using INV Hh.
    intros tr Hp Hb. eapply wstep_ret_introA; [exact Hp | exact Hh | | exact Hh].
    exact (@mprotect_expose_intro_fail (sys_input segs ms x8) m Hno Hprot Halign Hlen Hwrap Hna Hmp Hb).
  Qed.

  Lemma wstep_mprotect_expose_intro_okA : ltac2:(tb__ "0|3|
S2fS41A1M0S0S35S10Q40M1A1M2A1S75Vms;A1S36G2Vx8;A2A3S0S32Sc4Vm;Vaddr;Vn;A3S33A3S71Vsegs;S30G0S6bR3S6cVms;Vm;A2A4S30G0S6bR3S6cSb8Vms;S11G1Z0A2SbaS77Vms;A1Vaddr;Vn;A3A3Sc3Vm;Vaddr;Vn;A3A2A4A3F_;F_;Ftr;").
  Proof using INV Hh.
    intros tr Hp Hb.
    pose proof (@mprotect_expose_intro_ok (sys_input segs ms x8) m Hno Hprot Halign Hlen Hwrap Hna Hmp Hb) as Hs.
    pose proof (wstep_pending_runA segs tr ms m x8 _ _ _ [] Hp Hh Hs ltac:(rewrite mprotect_model_next_halted; exact Hh) (materialize_nil _)) as W.
    rewrite app_nil_r, advance_apply_zero1 in W. exact W.
  Qed.
End MprotectA.

Definition sp_clear_b (facts : list sprop) (o : sobj) : bool := ltac2:(tb__ "0|2|
S35S13A1S32Lx;SdaS2aVo;A1A1S13S3cS3cS9SeS8fA1R1A2S9R1SaZ2Z28A2A2A2S3dS2eS29Vo;A1M0S92A2S3cS9Z0M1R1A2SdeVfacts;S92G1G0A4A2A2A2Llo;S3bX35x2").
Definition obj_clear_M (facts : list sprop) (Ge : list (sv * Z)) (o : sobj) : bool := ltac2:(tb__ "0|0|
S3dS3dSd9Vo;A1SbeVfacts;Vo;A2A2Sd3VGe;Vo;A2A2").
Definition objs_clear_M (Ge : list (sv * Z)) (S : sstate) : bool := ltac2:(tb__ "0|0|
S6aS1dSbfS1cVS;A1VGe;A2S23VS;A1A3").

Lemma sp_clear_sound : ltac2:(tb__ "0|2|
S18S2fS17A1S10Q40M0A1S13S13S1dS7aS17S1fR6A1R5A3S0S32SbeR6R2A2S33A3S5Z0R5A2S5S6SfG0R7A2R6A2R5A2S5S6R6S8fA2SfG0S19RaPaA2A2A2S25S24RbR6A2S30S13S13SfG0R9A2M1S6G1R8A2A4A2F_;F_;F_;F_;F_;Fo;Ftop;Fn;Fa;Ffacts;Frho;").
Proof.
  intros rho facts a n top o HF Hb Hn Hceil HSP. unfold sp_clear_b in Hb.
  destruct (lit_of (ob_lo o)) as [lo|] eqn:Elo; [|discriminate]. apply lit_of_sound in Elo.
  apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold D_M in H1.
  assert (HB : bv_unsigned (rw rho 10%positive) - D_M <= bv_unsigned (eval rho (ob_base o)) + lo).
  { apply Bool.orb_prop in H3 as [H3|H3].
    - apply sv_eqb_sound in H3. rewrite H3. unfold vSP. cbn [eval]. unfold D_M in *. lia.
    - apply andb_prop in H3 as [H4 H5]. apply Z.leb_le in H4. pose proof (uleq_sound rho facts _ _ _ HF H5) as U1.
      unfold U, vSP in U1. cbn [eval] in U1. unfold D_M in *. lia. }
  unfold obj_range, obj_lo_of, obj_hi_of. rewrite Elo. rewrite soff_lit_small by lia.
  unfold ranges_disjoint. cbn [fst snd]. unfold D_M in *. lia.
Qed.

Lemma objs_clear_M_sound : ltac2:(tb__ "0|6|
S18S2fS31S16S13A2M0A1S2dS10Q40M1A1S13S13S7aS17S1fR6A1S1cR4A1A3S0S32SbdR6R5A2S33A3S5Z0R4A2S5S6SfG1R6A2R5A2R4A2S5S6R5S8fA2SfG1S19RaPaA2A2A2S13S1S5SfG1R9A2M2R1A2S7R1S6G2R8A2A2A2S3S1S5Z10000R2A2S7R2Z643000A2A2A1F_;Fx;S16S13S69G0S30S16S13R2R1A4RdA3S13S1S5SfG1RdA2M3R1A2S7R1S6G3RcA2A2A2S3S1S5SfG1S1aR11R5A2A2M4R2A2S7R2S6G4R4A2A2A2A1F_;Fx;F_;Fsz;Fe;S1dS69S1dR1S23RcA1A3S25S24RfR2A2S30S13S13SfG1RcA2M5S6G5RbA2A4A2F_;Fo;F_;F_;F_;F_;F_;F_;F_;Ftop;Fn;Fa;FS;FGe;Frho;").
Proof.
  intros rho Ge S a n top HF Hb Hn Hceil HSP Hpw HG o Hin.
  pose proof (proj1 (forallb_forall _ _) Hb o Hin) as Ho. unfold obj_clear_M in Ho.
  apply Bool.orb_prop in Ho as [Ho|Ho]; [apply Bool.orb_prop in Ho as [Ho|Ho]|].
  - eapply img_clear_sound; eauto.
  - eapply sp_clear_sound; eauto.
  - eapply eblk_clear_sound; eauto.
Qed.

Lemma band_clear_of_free : ltac2:(tb__ "0|3|
S2fS31S10Q40M0A1M1G1A2A1G1G1Sb5R3Sb4Sb6A3S0S32S47R4R3R2A3S33A3S7Z0SfG0R3A2A2S13S1S5SfG0R6A2M2R1A2S7R1S6G2SfG0R5A2A2A2A2S3S1S5Sb4R2A2S7R2S6Sb4SbSb6Sb4A2A2A2A2A1F_;Fx;F_;F_;F_;Fn;Fa;Fl;").
Proof.
  intros l a n Hb Hf Hn x Hx.
  pose proof (grant_avoids_band l _ _ a n Hb ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) Hf Hn). lia.
Qed.

Lemma band_covered_subtract : ltac2:(tb__ "0|4|
S2fS31S10Q40A1M0G0A2M1A1M2G2S13S13S13S13SdfR5A1S5R5R4A2M3S2S5R3R6A2G3A2Sb5S37G1R9R8A3R5R4A3Sb5S37G1RaS57R9R8R7A3A3R6R5A3F_;F_;F_;F_;Fbhi;Fblo;Fhi;Flo;Fl;Fres;").
Proof.
  intros res l lo hi blo bhi Hwf Hlh Hd H x Hx. destruct (H x Hx) as (b & s & Hin & Hbs).
  apply in_app_iff in Hin as [Hin|Hin].
  - exists b, s. split; [apply in_app_iff; left; exact Hin | exact Hbs].
  - destruct (maps_subtract_keeps l lo hi (b, s) x (x + 1) Hwf Hlh Hin ltac:(cbn [fst]; lia) ltac:(cbn [fst snd]; lia) ltac:(lia) ltac:(lia))
      as ([b' s'] & Hin' & H1 & H2). cbn [fst snd] in H1, H2.
    exists b', s'. split; [apply in_app_iff; right; exact Hin' | lia].
Qed.

Section Malloc40.
Variable ok : assn.
Hypothesis OKF : ltac2:(tb__ "0|1|
S5fS18S2fS10Q40A1A1S2fS41A1M0S44R5R4R3R2R1A4S0G0R3S34S41A1A3F_;Fmd;Ftr;Ftp;Frho;S60S15Vok;R2A3F_;FJ;").
Hypothesis OKP : ltac2:(tb__ "0|1|
S5fS18S2fS10Q40A1A1S2fS41A1M0S44R5R4R3R2R1A4S0G0R3S34S41A1A3F_;Fmd;Ftr;Ftp;Frho;Sc8S15Vok;R2A3F_;FJ;").
Variables (m : Model) (B : Z).
Definition brk0w : word := vm_brk (m_vmmaps m).
Definition brk0 : Z := bv_unsigned brk0w.
Hypothesis Hres : ltac2:(tb__ "0|1|
S0S2fS31S10Q40A1M0G0A2A1S43S40Vm;A1A1S6eS15A1A3").
Hypothesis Hsb : ltac2:(tb__ "0|1|
S0S10Q40A1S50S40Vm;A1M0A1S45G0A1A3").
Hypothesis Hal : brk0 mod 4096 = 0.
Hypothesis Hlo : 0x643000 <= brk0.
Hypothesis Hhi : brk0 <= 0x80643000.
Hypothesis HB : ltac2:(tb__ "0|0|
S5S6VB;Z3000A2S4fS40Vm;A1A1A2").

Hypothesis Htop : init_sp_ok (m_vmmaps m).
Hypothesis Hband : ltac2:(tb__ "0|2|
Sb5S37S31S10Q40A1M0G0A2S43S40Vm;A1M1A1S42G1A1A3Sb4Sb6A3").

Definition TOP : Z := alloc_top (m_vmmaps m).
Lemma TOP_bounds : ltac2:(tb__ "0|0|
S1S5S9bS7bA2S5S7bS9aA2A2").
Proof using Htop. exact (alloc_top_bounds _ Htop). Qed.

Lemma OKFx : ltac2:(tb__ "0|0|
S44S13S60S15Vok;S6fR2R1A2A3FBx;Fmx;").
Proof using OKF. intros. apply OKF. intros; eapply KxA_nil; eassumption. Qed.
Lemma OKPx : ltac2:(tb__ "0|0|
S44S13Sc8S15Vok;S6fR2R1A2A3FBx;Fmx;").
Proof using OKP. intros. apply OKP. intros; eapply KxA_nil; eassumption. Qed.

Lemma regs_of_pending : ltac2:(tb__ "0|4|
S18S2fS10Q40A1M0A1S64S2fS41A1M1S76S44Sc6S15R6R5R4S30G1S6bR3S6cR2R1A2A4A5S1S0G0S74R3U0A2S1aR7S79S16UaS1eS62R5A1A1M2S1bZ0A1M3A4A2A3S1S0G0S74R3U1A2S1aR7S79S16UbG2G3A4A2A3S1S0G0S74R3U2A2S1aR7S79S16UcG2G3A4A2A3S1S0G0S74R3U3A2S1aR7S79S16UdG2G3A4A2A3S1S0G0S74R3U4A2S1aR7S79S16UeG2G3A4A2A3S1S0G0S74R3U5A2S1aR7S79S16UfG2G3A4A2A3S0S35G0A1S75R3A1S36G0S1aR7S79S16U11G2G3A4A2A2A3A2A2A2A2A2A2F_;Fmd;Fms;Ftr;FA;Ftp;Frho;").
Proof.
  clear Hres Hsb Hal Hlo Hhi HB Htop Hband. intros rho tp A tr ms md Hsp. pose proof (pending_argsA segsA rho tp A tr ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5).
  pose proof (smatch_pendingA_pending segsA _ _ _ _ _ _ Hsp) as Hp.
  unfold reg_sv in *. repeat split; assumption.
Qed.

Theorem node18 : ltac2:(tb__ "0|1|
S18S2fS10Q40A1A1S72S15Vok;S5eS15S6fVm;VB;A2M0SaeR2R1A5S5eS15G0SafSc0R2Sa4S7cA3R1A5A4Ftp;Frho;").
Proof using OKF OKP Hal Hlo Hhi.
  clear Htop Hband. intros rho tp. pose proof E18_at as (Hpc & Hecall & R17 & R10).
  apply triple1_ecall_detA; [apply OKFx | apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & _ & _ & _).
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  destruct (regs_of_pending rho tp E18t [] ms md Hsp) as (G0 & _ & _ & _ & _ & _ & Hp).
  rewrite R17 in Hp. rewrite R10 in G0. cbn [eval] in Hp, G0.
  assert (H214 : bv_unsigned (Z_to_bv 64 214) = 214%Z) by reflexivity.
  split.
  - eapply (OKPx m B); [exact HK | exact Hp | exact (brk_query_only_okA segsA ms md _ Hh H214 G0)].
  - intros w' Hw. rewrite (wstep_brk_query_invA segsA ms md _ Hh H214 [] w' Hp G0 Hw).
    split; [| cbn [w_tr w_cfg fst snd cfg_model]; exact HK].
    unfold S18, cont. rewrite Evm. fold brk0w.
    assert (HN : ss_next (ax_S E18t) = N18) by reflexivity. rewrite <- HN.
    eapply smatchA_after_ret_fresh; [exact Hsp | exact Hh | apply vm_same_refl | OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc |].
    rewrite HN. unfold F18, vBRK, brk0 in *.
    constructor; [|constructor; [|constructor; [|constructor]]]; cbn [holds eval]; rewrite rho_set_rw_at.
    + split; [lia|]. change (2 ^ 12) with 4096. exact Hal.
    + rewrite (u64_of_lit 0x643000) by lia. lia.
    + rewrite (u64_of_lit 0x80643000) by lia. lia.
Qed.

Lemma xshadow_clear_of_disj : ltac2:(tb__ "0|a|
S18S64S10Q40M0A1S13S13S13S0S2fS31S16S16A2M1A1S65R5A1S91A3S0S16S63R6A1S1bSd2A1A3S7aS17S1fR8A1S1cS62R7A1A1A3S17S69S17R1S90A3S69S17R2S1cS62RaA1A1A3F_;Ff;S5R6Z10006fdf0000A2S5Z10007fff8000S6R7R6A2A2S13S1S5SfG0RbA2M2R1A2S7R1S6G2RaA2A2A2S3S1S5RaR2A2S7R2S6RaR9A2A2A2A1F_;Fx;S1G1S13S69G1R2S65ReA1A3S1S5SfG0S1aR10S3aS16S16R3A3A2A2M3R2A2S7R2S6G3SfG0S1aR10S39S16S16R3A3A2A2A2A2A2S3S1S5SfG0RfA2M4SfG0S67SfG0S1aR11S63R10A1A2A2R3A2A2M5A2S7G5S6G4ReA2A2A2A1F_;F_;Fy;Frr;G1S13S13S69G1R3S65RfA1A3S1S5SfG0S1aR11S3aS16S16R4A3A2A2M6R3A2S7R3S6G6SfG0S1aR11S39S16S16R4A3A2A2A2A2A2S1S5Z0R3A2S7R3Z8M7A2A2S3S1S5SfG0R11A2M8SfG0S68S6SfG0S1aR13S63R12A1A2A2S8R5G7A2A2R4A2A2M9A2S7G9S6G8R10A2A2A2A1F_;F_;F_;Fj;Fy;Frr;A2F_;F_;F_;F_;F_;F_;F_;FsZ;FbZ;FnZ;Fa;FA;Frho;").
Proof.
  clear Hres Hsb Hal Hlo Hhi HB Htop Hband.
  intros rho A a nZ bZ sZ HX Hb HF Hin Hb1 Hb2 Hdisj. rewrite HX, Hb.
  assert (F1 : holds rho (SPUle (SLit 0x7fff7f000000) vXB)) by (apply (proj1 (Forall_forall _ _) HF); apply Hin; unfold facts_M; cbn [In]; tauto).
  assert (F2 : holds rho (SPUle (SAlu ALU_ADD vXB vXL) (SLit (2 ^ 47)))) by (apply (proj1 (Forall_forall _ _) HF); apply Hin; unfold facts_M; cbn [In]; tauto).
  assert (F3 : holds rho (SPUle vXL (SLit (2 ^ 40)))) by (apply (proj1 (Forall_forall _ _) HF); apply Hin; unfold facts_M; cbn [In]; tauto).
  assert (F4 : holds rho (SPUle vXB (SLit (2 ^ 48)))) by (apply (proj1 (Forall_forall _ _) HF); apply Hin; unfold facts_M; cbn [In]; tauto).
  cbn [holds eval] in F1, F2, F3, F4. unfold vXB, vXL in F1, F2, F3, F4. cbn [eval] in F1, F2, F3, F4.
  rewrite (u64_of_lit 0x7fff7f000000) in F1 by lia. rewrite (u64_of_lit (2 ^ 47)) in F2 by lia.
  rewrite (u64_of_lit (2 ^ 40)) in F3 by lia. rewrite (u64_of_lit (2 ^ 48)) in F4 by lia.
  unfold alu64, alu in F2. rewrite bv_add_unsigned in F2.
  rewrite bv_wrap_small in F2 by (change (bv_modulus 64) with (2 ^ 64); pose proof (urange (rw rho 52)); pose proof (urange (rw rho 53)); lia).
  cbn [eval]. unfold SHB. rewrite (u64_of_lit 0x7fff8000) by lia.
  split.
  - intros rr y [<-|[]] Hy. cbn [fst snd] in Hy. unfold vXB, vXL in Hy. cbn [eval] in Hy.
    assert (Hy8 : 0x7fff7f000000 / 8 <= y / 8 < 2 ^ 44) by (split; [apply Z.div_le_mono; lia | apply Z.div_lt_upper_bound; lia]).
    change (0x7fff7f000000 / 8) with 17591915511808 in Hy8.
    unfold shadow_addr. rewrite u64_of_lit by lia. intros Hc. apply (Hdisj (2147450880 + y / 8)); lia.
  - intros rr y j [<-|[]] Hy Hj. cbn [fst snd] in Hy. unfold vXB, vXL in Hy. cbn [eval] in Hy.
    assert (Hy8 : 0x7fff7f000000 / 8 <= y / 8 < 2 ^ 44) by (split; [apply Z.div_le_mono; lia | apply Z.div_lt_upper_bound; lia]).
    change (0x7fff7f000000 / 8) with 17591915511808 in Hy8.
    pose proof (Z.div_mod (2147450880 + y / 8) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (2147450880 + y / 8) 8 ltac:(lia)) as M.
    assert ((2147450880 + y / 8) / 8 <= 17594333495295 / 8) by (apply Z.div_le_mono; lia).
    change (17594333495295 / 8) with 2199291686911 in H.
    unfold word_byte. rewrite u64_of_lit by lia. intros Hc. apply (Hdisj ((2147450880 + y / 8) / 8 * 8 + j)); lia.
Qed.

Definition reqw : word := Z_to_bv 64 (brk0 + 8192).
Definition n2w : word := Z_to_bv 64 8192.

Definition n3w : word := Z_to_bv 64 12288.
Lemma n3w_val : bv_unsigned n3w = 12288.
Proof. reflexivity. Qed.
Definition mg : Model := ltac2:(tb__ "0|0|
S48ScdS40Vm;A1S81S81A3Vm;A2").

Lemma reqw_val : ltac2:(tb__ "0|0|
S0S13SfQ40S81A2S6S7dZ2000A2A3").
Proof using Hlo Hhi. unfold reqw. apply u64_of_lit. unfold brk0 in *. lia. Qed.
Lemma n2w_val : bv_unsigned n2w = 8192.
Proof. reflexivity. Qed.
Lemma req_sub : ltac2:(tb__ "0|1|
S0S10Q40M0A1S12G0S81S7cA3S84A3").
Proof using Hlo Hhi.
  apply bv_eq. rewrite bv_sub_unsigned, reqw_val, n2w_val. unfold brk0.
  replace (bv_unsigned brk0w + 8192 - bv_unsigned brk0w) with 8192 by lia. reflexivity.
Qed.

Lemma brk_model_next_grow : ltac2:(tb__ "0|1|
S4dS0S10Q40A1M0S45R1A1S7cA3S0S4dScdR2S81S81A3S58S43R2A1S38S31G0G0A2S30G0G0S7cS84A4S42R2A1A3S54R2A1S50R2A1S81S4fR2A1S5bR2A1S5aR2A1A8A3F_;Fhh;").
Proof using Hlo Hhi.
  intros hh Hb. pose proof reqw_val as RV. unfold brk_model_next. rewrite Hb.
  rewrite (brk_unmaps_grow reqw brk0w) by (unfold brk0 in *; lia). cbn [maps_subtract_ranges fold_left].
  unfold brk_maps_next. rewrite Hb.
  replace ((0 <? bv_unsigned brk0w) && (bv_unsigned reqw <? bv_unsigned brk0w))%Z%bool with false
    by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; unfold brk0 in *; lia).
  unfold brk_grants, brk_is_grow. rewrite (w_is0_pos reqw) by (unfold brk0 in *; lia). cbn [negb andb].
  rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned brk0w))) by (unfold brk0 in *; lia).
  rewrite (proj2 (Z.ltb_lt (bv_unsigned brk0w) (bv_unsigned reqw))) by (unfold brk0 in *; lia). cbn [andb app].
  rewrite req_sub. reflexivity.
Qed.

Lemma mg_vmmaps : ltac2:(tb__ "0|2|
S0S4dS40S7fA1S58S43S40Vm;A1M0A1S38S31S10Q40A1M1G1A2S30G1G1S7cS84A4S42G0A1A3S54G0A1S50G0A1S81S4fG0A1S5bG0A1S5aG0A1A8A3").
Proof using Hlo Hhi. unfold mg. rewrite m_vmmaps_with_vmmaps. apply brk_model_next_grow. reflexivity. Qed.

Lemma objs_clear_E19 : ltac2:(tb__ "0|0|
S0S32SbdS34S31S16S13A2A1S62Sa7A1A2S33A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma facts_M_in_E19 : ltac2:(tb__ "0|0|
S17S69S17R1S90A3S69S17R2S1cS62Sa7A1A1A3F_;Ff;").
Proof. intros f Hf. vm_compute in Hf. vm_compute. tauto. Qed.

Definition RM19 (rho rho1 : valuation) : Prop := ltac2:(tb__ "0|8|
S1S14S0S10Q40M0A1M1S19Vrho1;R1A2S19Vrho;R1A2A3Fi;S1S14S0S2fS10Q8M2A1M3A1S26Vrho1;R1A2S26Vrho;R1A2A3Fl;S1G1S3S1S5S7dSfG0R1A2M4A2S7G4S6S7dZ2000A2A2A2M5A1S0S35G3A1M6S20Vrho1;R2A2M7S20Vrho;R2A2A3F_;Fa;G1G5S0G6G7S36G3S11G2Z0A2A2A3F_;Fa;A2A2A2").

Theorem node19 : ltac2:(tb__ "0|5|
S18S2fS10Q40M0A1M1A1S0G1S19R2Sa4A2S7cA3S5S6S7bS8fA2SfG0S19R3PaA2A2A2S72S15Vok;S5eS15S6fVm;VB;A2M2Sa7R4R3A5S70S2S4S18S18S1S5S6S7dZ2000M3A2S7bA2S1S0S32S47S37S31G1G1A2S43S40Vm;A1M4A1S42G4A1A3S7cS85A3S33A3S1S8aR6R1A2S5eS15S6fS7fS6VB;G3A2A2Sb1R1R5R2A6A2A2A2Lrho1;A2S5eS15G2Sb0R5R4R1A6A2Lw;A4F_;F_;Ftp;Frho;").
Proof using OKF OKP Hres Hsb Hal Hlo Hhi HB Htop Hband.
  intros rho tp HN18 HSP. pose proof E19_at as (Hpc & Hecall & R17 & R10 & Hnx).
  pose proof reqw_val as RV. pose proof TOP_bounds as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB. pose proof n2w_val as NV. pose proof n3w_val as NV3.
  apply triple1_ecall_detA; [apply OKFx | apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & _ & _).
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (regs_of_pending rho tp E19 [] ms md Hsp) as (G0 & _ & _ & _ & _ & _ & Hp).
  rewrite R17 in Hp. rewrite R10 in G0. cbn [eval] in Hp, G0. unfold vBRK in G0. cbn [eval] in G0. rewrite HN18 in G0.
  assert (Ereq : ms_gpr ms 0 = reqw).
  { rewrite G0. apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, RV, (u64_of_lit 8192) by lia. unfold brk0.
    apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). pose proof (urange brk0w). unfold brk0 in *. lia. }
  assert (H214 : bv_unsigned (Z_to_bv 64 214) = 214%Z) by reflexivity.
  assert (Ebrk : vm_brk (m_vmmaps m) = brk0w) by reflexivity.
  assert (Hsb' : bv_unsigned (vm_start_brk (m_vmmaps md)) <= bv_unsigned (vm_brk (m_vmmaps md))) by (rewrite Evm, Hsb; lia).
  assert (Hlt : bv_unsigned (vm_brk (m_vmmaps md)) < bv_unsigned (ms_gpr ms 0)) by (rewrite Evm, Ereq, RV, Ebrk; unfold brk0; lia).
  split.
  - eapply (OKPx m B); [exact HK | exact Hp | exact (brk_grow_only_okA segsA ms md _ Hh H214 Hsb' Hlt)].
  - intros w' Hw.
    destruct (wstep_brk_grow_invA segsA ms md _ Hh H214 Hsb' Hlt [] w' Hp Hw) as [[Hg ->] | ->].
    +   left.
      rewrite Ereq in Hg |- *. rewrite Evm.

      assert (Hgate : brk0 + 8192 <= TOP /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) brk0w n3w = true).
      { unfold brk_grow_ok in Hg. rewrite Evm, Ebrk in Hg.
        rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned brk0w))) in Hg by (unfold brk0 in *; lia).
        rewrite (proj2 (Z.ltb_lt (bv_unsigned brk0w) (bv_unsigned reqw))) in Hg by (rewrite RV; unfold brk0; lia). cbn [andb] in Hg.
        rewrite (page_round_up_Z_id (bv_unsigned brk0w)) in Hg by exact Hal.
        rewrite RV in Hg. rewrite (page_round_up_Z_id (brk0 + 8192)) in Hg
          by (unfold page_size; replace (brk0 + 8192) with (brk0 + 2 * 4096) by lia; rewrite Z_mod_plus_full; exact Hal).
        unfold brk0 in Hg. rewrite (proj2 (Z.ltb_lt (bv_unsigned brk0w) (bv_unsigned brk0w + 8192))) in Hg by lia.
        apply andb_prop in Hg as [Hg _]. apply andb_prop in Hg as [Hc Hf]. apply Z.leb_le in Hc.
        rewrite Z_to_bv_bv_unsigned in Hf. unfold page_size in Hf. replace (bv_unsigned brk0w + 8192 + 4096 - bv_unsigned brk0w) with 12288 in Hf by lia.
        fold n3w in Hf. unfold brk0, TOP. split; [lia | exact Hf]. }
      destruct Hgate as [Hceil Hfree3].
      assert (Hfree : region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) brk0w n2w = true).
      { apply (region_free_shrink _ brk0w n3w); [exact Hfree3 | lia | rewrite NV, NV3; lia]. }
      rewrite (brk_eff_grow_aligned (m_vmmaps m) reqw);
        [| rewrite Ebrk; exact Hal
         | rewrite RV; unfold page_size; replace (brk0 + 8192) with (brk0 + 2 * 4096) by lia; rewrite Z_mod_plus_full; exact Hal
         | rewrite Ebrk, RV; unfold brk0 in *; lia].
      rewrite Ebrk, req_sub.
      change (eff_mem ms (mkEffect reqw [] [(brk0w, n2w)])) with (zero_range (ms_mem ms) brk0w n2w).
      pose proof (band_clear_of_free _ brk0w n3w Hband Hfree3 ltac:(rewrite NV3; lia)) as HBD. rewrite NV3 in HBD.
      pose proof (xshadow_clear_of_disj rho E19 brk0w 8192 SHADOW_BAND_LO (SHADOW_BAND_HI - SHADOW_BAND_LO) eq_refl eq_refl
                    (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) facts_M_in_E19
                    ltac:(unfold SHADOW_BAND_LO; lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) ltac:(intros x Hx; apply HBD; lia)) as [_ HXw].
      set (h' := brk_model_next (m_vmmaps m) reqw reqw).
      set (ms' := after_sys_mem ms reqw (zero_range (ms_mem ms) brk0w n2w)).
      set (md' := with_vmmaps h' md).
      set (Ofull := mkObj vBRK (SLit 0) (SLit (bv_unsigned n2w)) [] DZero).
      set (A1 := ax_setS E19 (S_after (ax_S E19) (SAlu ALU_ADD vBRK (SLit 8192)) (ss_objs (ax_S E19) ++ [Ofull]) (Pos.succ N18))).
      assert (Hfreem : region_free (vm_maps (m_vmmaps md)) brk0w n2w = true) by (rewrite Evm; exact (region_free_app_r _ _ _ _ Hfree)).
      assert (Hsm1 : smatchA segsA rho tp A1 ([], mkCfg ms' md')).
      { eapply (smatchA_after_grant_obj segsA rho rho tp E19 [] ms md [] h' brk0w n2w reqw (SAlu ALU_ADD vBRK (SLit 8192)) vBRK (Pos.succ N18) Hsp).
        -- unfold h'. rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm. reflexivity.
        -- unfold h'. rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm. reflexivity.
        -- unfold h'. rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm. reflexivity.
        -- rewrite NV. lia.
        -- rewrite NV. unfold brk0 in *. lia.
        -- exact Hfreem.
        -- unfold headroom. rewrite Evm, NV. lia.
        -- intros x Hx. apply (grant_no_ro_A brk0w 8192); [intros z Hz; unfold brk0 in *; lia|]. rewrite NV in Hx. exact Hx.
        -- rewrite NV. intros o Ho.
           apply (objs_clear_M_sound rho [] (ax_S E19) brk0w 8192 TOP (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) objs_clear_E19);
             [lia | unfold brk0 in *; lia | exact HSP | intros x Hx; unfold brk0 in *; lia | intros i sz [] | exact Ho].
        -- rewrite NV. exact HXw.
        -- apply agree_below_refl.
        -- rewrite Hnx. apply Pos.le_refl.
        -- OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
        -- rewrite <- Ereq, G0. unfold vBRK. cbn [eval]. rewrite HN18. reflexivity.
        -- OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
        -- unfold vBRK. cbn [eval]. exact HN18. }
      assert (HK1 : KxA mg (B + 8192) rho tp [] md').
      { split; [reflexivity|]. split.
        -- unfold mg, md', h'. rewrite <- Evm. apply erase_mat_cong_vmmaps. exact Hem.
        -- unfold md'. rewrite paid_with_vmmaps.
           pose proof (used_maps_cons_le md h' brk0w n2w (MI_ivs_wf segsA _ _ HMI)
                        ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite NV; unfold brk0 in *; lia)
                        ltac:(unfold h'; rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm; reflexivity)
                        ltac:(unfold h'; rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm; reflexivity)) as U.
           rewrite NV in U. lia. }

      pose proof (SPA_unobj segsA (KxA mg (B + 8192)) rho A1 (ss_objs (ax_S E19)) [Ofull] tp [] ms' md' eq_refl (conj Hsm1 HK1) (fun K => K)) as HS2.
      cbn zeta in HS2. set (rho1 := rho_absorb rho [Ofull] (vms md' tp ms')) in HS2.
      exists rho1. split; [exact Hceil|]. split; [exact Hfree3|].
      assert (Hrng : obj_range rho Ofull = (brk0, brk0 + 8192)).
      { unfold obj_range, obj_lo_of, obj_hi_of, Ofull, vBRK. cbn [ob_base ob_lo ob_hi eval]. rewrite HN18, NV.
        rewrite !soff_lit_small by lia. unfold brk0. f_equal; lia. }
      split.
      *   unfold RM19, rho1, rho_absorb. cbn [rw rl rm]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split.
        -- intros a Ha. destruct (in_ranges_dec rho [Ofull] a) as [Hin|Hnin]; [|reflexivity].
           exfalso. destruct Hin as (o & [<-|[]] & Hr). rewrite Hrng in Hr. cbn [fst snd] in Hr. exact (Ha Hr).
        -- intros a Ha. destruct (in_ranges_dec rho [Ofull] a) as [Hin|Hnin].
           ++ unfold vms, restrict, ms'. cbn [ms_mem]. unfold mrestrict.
              rewrite (hid_ext md md' tp) by reflexivity.
              rewrite (hid_false_of_region_free md tp brk0w n2w a (MI_lazy_in_maps segsA _ _ HMI) (MI_ivs_wf segsA _ _ HMI) Hfreem)
                by (rewrite NV; unfold brk0 in Ha; lia).
              rewrite after_sys_memq, zero_range_at. rewrite (proj2 (in_range_spec brk0w n2w a)) by (rewrite NV; unfold brk0 in Ha; lia). reflexivity.
           ++ exfalso. apply Hnin. exists Ofull. split; [left; reflexivity|]. rewrite Hrng. cbn [fst snd]. exact Ha.
      *
        replace S19g with (ax_setS A1 (set_objs (ax_S A1) (ss_objs (ax_S E19)))); [exact HS2|].
        unfold S19g, cont, A1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    +   right. split; [| cbn [w_tr w_cfg fst snd cfg_model]; exact HK].
      unfold S19f, cont. cbn [add_facts app].
      change (add_facts [] (S_after (ax_S E19) vBRK (ss_objs (ax_S E19) ++ []) (Pos.succ N18)))
        with (S_after (ax_S E19) vBRK (ss_objs (ax_S E19) ++ []) (Pos.succ N18)).
      rewrite app_nil_r, <- Hnx. rewrite Evm, Ebrk.
      change (S_after (ax_S E19) vBRK (ss_objs (ax_S E19)) (ss_next (ax_S E19))) with (ax_S (A_after E19 vBRK)).
      eapply (smatchA_after_ret_expr segsA rho tp E19 [] ms md [] md brk0w vBRK Hsp Hh (vm_same_refl md));
        [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | unfold vBRK; cbn [eval]; exact HN18].
Qed.

Theorem enode19_any : forall (rho : valuation) (tp : list word),
  rw rho N18 = brk0w -> TOP + D_M <= bv_unsigned (rw rho 10%positive) ->
  etriple segsA (SPA segsA (KxA m B) E19 rho tp)
    (fun w => (exists rho1, brk0 + 8192 <= TOP /\
                 region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) brk0w n3w = true /\
                 RM19 rho rho1 /\ SPA segsA (KxA mg (B + 8192)) S19g rho1 tp w) \/
              SPA segsA (KxA m B) S19f rho tp w).
Proof using Hres Hsb Hal Hlo Hhi HB Htop Hband.
  intros rho tp HN18 HSP. pose proof E19_at as (Hpc & Hecall & R17 & R10 & Hnx).
  pose proof reqw_val as RV. pose proof TOP_bounds as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB. pose proof n2w_val as NV. pose proof n3w_val as NV3.
  apply etriple_ecall_detA; [apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & Elz & _ & _).
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (regs_of_pending rho tp E19 [] ms md Hsp) as (G0 & _ & _ & _ & _ & _ & Hp).
  rewrite R17 in Hp. rewrite R10 in G0. cbn [eval] in Hp, G0. unfold vBRK in G0. cbn [eval] in G0. rewrite HN18 in G0.
  assert (Ereq : ms_gpr ms 0 = reqw).
  { rewrite G0. apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, RV, (u64_of_lit 8192) by lia. unfold brk0.
    apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). pose proof (urange brk0w). unfold brk0 in *. lia. }
  assert (H214 : bv_unsigned (Z_to_bv 64 214) = 214%Z) by reflexivity.
  assert (Ebrk : vm_brk (m_vmmaps m) = brk0w) by reflexivity.
  assert (Hsb' : bv_unsigned (vm_start_brk (m_vmmaps md)) <= bv_unsigned (vm_brk (m_vmmaps md))) by (rewrite Evm, Hsb; lia).
  assert (Hlt : bv_unsigned (vm_brk (m_vmmaps md)) < bv_unsigned (ms_gpr ms 0)) by (rewrite Evm, Ereq, RV, Ebrk; unfold brk0; lia).
  destruct (brk_grow_ok md (ms_gpr ms 0) (ms_gpr ms 0)) eqn:Hg.
  - eexists. split; [exact (wstep_brk_grow_intro_okA segsA ms md _ Hh H214 Hsb' Hlt [] Hp Hg)|].
    left.
    rewrite Ereq in Hg |- *. rewrite Evm.

    assert (Hgate : brk0 + 8192 <= TOP /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) brk0w n3w = true).
    { unfold brk_grow_ok in Hg. rewrite Evm, Ebrk in Hg.
      rewrite (proj2 (Z.ltb_lt 0 (bv_unsigned brk0w))) in Hg by (unfold brk0 in *; lia).
      rewrite (proj2 (Z.ltb_lt (bv_unsigned brk0w) (bv_unsigned reqw))) in Hg by (rewrite RV; unfold brk0; lia). cbn [andb] in Hg.
      rewrite (page_round_up_Z_id (bv_unsigned brk0w)) in Hg by exact Hal.
      rewrite RV in Hg. rewrite (page_round_up_Z_id (brk0 + 8192)) in Hg
        by (unfold page_size; replace (brk0 + 8192) with (brk0 + 2 * 4096) by lia; rewrite Z_mod_plus_full; exact Hal).
      unfold brk0 in Hg. rewrite (proj2 (Z.ltb_lt (bv_unsigned brk0w) (bv_unsigned brk0w + 8192))) in Hg by lia.
      apply andb_prop in Hg as [Hg _]. apply andb_prop in Hg as [Hc Hf]. apply Z.leb_le in Hc.
      rewrite Z_to_bv_bv_unsigned in Hf. unfold page_size in Hf. replace (bv_unsigned brk0w + 8192 + 4096 - bv_unsigned brk0w) with 12288 in Hf by lia.
      fold n3w in Hf. unfold brk0, TOP. split; [lia | exact Hf]. }
    destruct Hgate as [Hceil Hfree3].
    assert (Hfree : region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) brk0w n2w = true).
    { apply (region_free_shrink _ brk0w n3w); [exact Hfree3 | lia | rewrite NV, NV3; lia]. }
    rewrite (brk_eff_grow_aligned (m_vmmaps m) reqw);
      [| rewrite Ebrk; exact Hal
       | rewrite RV; unfold page_size; replace (brk0 + 8192) with (brk0 + 2 * 4096) by lia; rewrite Z_mod_plus_full; exact Hal
       | rewrite Ebrk, RV; unfold brk0 in *; lia].
    rewrite Ebrk, req_sub.
    change (eff_mem ms (mkEffect reqw [] [(brk0w, n2w)])) with (zero_range (ms_mem ms) brk0w n2w).
    pose proof (band_clear_of_free _ brk0w n3w Hband Hfree3 ltac:(rewrite NV3; lia)) as HBD. rewrite NV3 in HBD.
    pose proof (xshadow_clear_of_disj rho E19 brk0w 8192 SHADOW_BAND_LO (SHADOW_BAND_HI - SHADOW_BAND_LO) eq_refl eq_refl
                  (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) facts_M_in_E19
                  ltac:(unfold SHADOW_BAND_LO; lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) ltac:(intros x Hx; apply HBD; lia)) as [_ HXw].
    set (h' := brk_model_next (m_vmmaps m) reqw reqw).
    set (ms' := after_sys_mem ms reqw (zero_range (ms_mem ms) brk0w n2w)).
    set (md' := with_vmmaps h' md).
    set (Ofull := mkObj vBRK (SLit 0) (SLit (bv_unsigned n2w)) [] DZero).
    set (A1 := ax_setS E19 (S_after (ax_S E19) (SAlu ALU_ADD vBRK (SLit 8192)) (ss_objs (ax_S E19) ++ [Ofull]) (Pos.succ N18))).
    assert (Hfreem : region_free (vm_maps (m_vmmaps md)) brk0w n2w = true) by (rewrite Evm; exact (region_free_app_r _ _ _ _ Hfree)).
    assert (Hsm1 : smatchA segsA rho tp A1 ([], mkCfg ms' md')).
    { eapply (smatchA_after_grant_obj segsA rho rho tp E19 [] ms md [] h' brk0w n2w reqw (SAlu ALU_ADD vBRK (SLit 8192)) vBRK (Pos.succ N18) Hsp).
      -- unfold h'. rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm. reflexivity.
      -- unfold h'. rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm. reflexivity.
      -- unfold h'. rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm. reflexivity.
      -- rewrite NV. lia.
      -- rewrite NV. unfold brk0 in *. lia.
      -- exact Hfreem.
      -- unfold headroom. rewrite Evm, NV. lia.
      -- intros x Hx. apply (grant_no_ro_A brk0w 8192); [intros z Hz; unfold brk0 in *; lia|]. rewrite NV in Hx. exact Hx.
      -- rewrite NV. intros o Ho.
         apply (objs_clear_M_sound rho [] (ax_S E19) brk0w 8192 TOP (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) objs_clear_E19);
           [lia | unfold brk0 in *; lia | exact HSP | intros x Hx; unfold brk0 in *; lia | intros i sz [] | exact Ho].
      -- rewrite NV. exact HXw.
      -- apply agree_below_refl.
      -- rewrite Hnx. apply Pos.le_refl.
      -- OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
      -- rewrite <- Ereq, G0. unfold vBRK. cbn [eval]. rewrite HN18. reflexivity.
      -- OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
      -- unfold vBRK. cbn [eval]. exact HN18. }
    assert (HK1 : KxA mg (B + 8192) rho tp [] md').
    { split; [reflexivity|]. split.
      -- unfold mg, md', h'. rewrite <- Evm. apply erase_mat_cong_vmmaps. exact Hem.
      -- unfold md'. rewrite paid_with_vmmaps.
         pose proof (used_maps_cons_le md h' brk0w n2w (MI_ivs_wf segsA _ _ HMI)
                      ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite NV; unfold brk0 in *; lia)
                      ltac:(unfold h'; rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm; reflexivity)
                      ltac:(unfold h'; rewrite (brk_model_next_grow (m_vmmaps m) Ebrk), Evm; reflexivity)) as U.
         rewrite NV in U. lia. }

    pose proof (SPA_unobj segsA (KxA mg (B + 8192)) rho A1 (ss_objs (ax_S E19)) [Ofull] tp [] ms' md' eq_refl (conj Hsm1 HK1) (fun K => K)) as HS2.
    cbn zeta in HS2. set (rho1 := rho_absorb rho [Ofull] (vms md' tp ms')) in HS2.
    exists rho1. split; [exact Hceil|]. split; [exact Hfree3|].
    assert (Hrng : obj_range rho Ofull = (brk0, brk0 + 8192)).
    { unfold obj_range, obj_lo_of, obj_hi_of, Ofull, vBRK. cbn [ob_base ob_lo ob_hi eval]. rewrite HN18, NV.
      rewrite !soff_lit_small by lia. unfold brk0. f_equal; lia. }
    split.
    *   unfold RM19, rho1, rho_absorb. cbn [rw rl rm]. split; [intros; reflexivity|]. split; [intros; reflexivity|]. split.
      -- intros a Ha. destruct (in_ranges_dec rho [Ofull] a) as [Hin|Hnin]; [|reflexivity].
         exfalso. destruct Hin as (o & [<-|[]] & Hr). rewrite Hrng in Hr. cbn [fst snd] in Hr. exact (Ha Hr).
      -- intros a Ha. destruct (in_ranges_dec rho [Ofull] a) as [Hin|Hnin].
         ++ unfold vms, restrict, ms'. cbn [ms_mem]. unfold mrestrict.
            rewrite (hid_ext md md' tp) by reflexivity.
            rewrite (hid_false_of_region_free md tp brk0w n2w a (MI_lazy_in_maps segsA _ _ HMI) (MI_ivs_wf segsA _ _ HMI) Hfreem)
              by (rewrite NV; unfold brk0 in Ha; lia).
            rewrite after_sys_memq, zero_range_at. rewrite (proj2 (in_range_spec brk0w n2w a)) by (rewrite NV; unfold brk0 in Ha; lia). reflexivity.
         ++ exfalso. apply Hnin. exists Ofull. split; [left; reflexivity|]. rewrite Hrng. cbn [fst snd]. exact Ha.
    *
      replace S19g with (ax_setS A1 (set_objs (ax_S A1) (ss_objs (ax_S E19)))); [exact HS2|].
      unfold S19g, cont, A1. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
  - eexists. split; [exact (wstep_brk_grow_intro_failA segsA ms md _ Hh H214 Hsb' Hlt [] Hp Hg)|].
    right.
    split; [| cbn [w_tr w_cfg fst snd cfg_model]; exact HK].
    unfold S19f, cont. cbn [add_facts app].
    change (add_facts [] (S_after (ax_S E19) vBRK (ss_objs (ax_S E19) ++ []) (Pos.succ N18)))
      with (S_after (ax_S E19) vBRK (ss_objs (ax_S E19) ++ []) (Pos.succ N18)).
    rewrite app_nil_r, <- Hnx. rewrite Evm, Ebrk.
    change (S_after (ax_S E19) vBRK (ss_objs (ax_S E19)) (ss_next (ax_S E19))) with (ax_S (A_after E19 vBRK)).
    eapply (smatchA_after_ret_expr segsA rho tp E19 [] ms md [] md brk0w vBRK Hsp Hh (vm_same_refl md));
      [OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc | unfold vBRK; cbn [eval]; exact HN18].
Qed.

Definition pgw : word := Z_to_bv 64 4096.
Definition mg_ok : Model := ltac2:(tb__ "0|0|
S53S7dS6S7dZ1000A2S48S9fS40S7fA1S7cS82A3S7fA2A3").
Definition mg_dead : Model := ltac2:(tb__ "0|0|
S53S7dS6S7dZ1000A2S48S9dS40S7fA1S7cS82A3S7fA2A3").
Definition rho20 (rho : valuation) : valuation := ltac2:(tb__ "0|0|
Sd8Vrho;Sb9S20Vrho;A1S7cS82A3A2").
Definition tp20 (tp : list word) : list word := ltac2:(tb__ "0|0|
Se0S7dS6S7dZ1000A2Vtp;A3").

Lemma objs_clear_E20g : ltac2:(tb__ "0|0|
S0S32SbdS34S31S16S13A2A1S62Sa6A1A2S33A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma facts_M_in_E20g : ltac2:(tb__ "0|0|
S17S69S17R1S90A3S69S17R2S1cS62Sa6A1A1A3F_;Ff;").
Proof. intros f Hf. vm_compute in Hf. vm_compute. tauto. Qed.
Lemma S20g_ok_eq : ltac2:(tb__ "0|0|
S0S64SacSc7Sa6Sb3A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma S20g_ko_eq : ltac2:(tb__ "0|0|
S0S64Sa9Sc7Sa6S1bSdcA1A2A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma alloc_top_mg : ltac2:(tb__ "0|0|
S0S13S4eS40S7fA1A1S7bA3").
Proof using Hlo Hhi. unfold TOP, alloc_top. rewrite mg_vmmaps. reflexivity. Qed.

Lemma band_mg : ltac2:(tb__ "0|2|
Sb5S37S31S10Q40A1M0G0A2S43S40S7fA1M1A1S42G1A1A3Sb4Sb6A3").
Proof using Hlo Hhi Hband. rewrite mg_vmmaps. cbn [vm_reserved vm_maps]. apply band_covered_app_cons. exact Hband. Qed.

Theorem node20g : ltac2:(tb__ "0|6|
S18S2fS10Q40M0A1M1A1S13S0G1S19R3Sa4A2S7cA3S5S6S7bS8fA2SfG0S19R4PaA2A2A2S0S32S47S37S31G1G1A2M2S43S40Vm;A1M3A1S42G3A1A3S7cS85A3S33A3S72S15Vok;S5eS15S6fS7fR4A2Sa6R6R5A5S70S2S5eS15S6fS7fR5A2Sa9R7R6R1A6S2S5eS15S6fS8cR5A2SacS8dR7A1M4R6R1A6S1Sb5S37G2S43S40S88A1M5A1S42G5A1A3Sb4Sb6A3S5eS15S6fS88R5A2Sa9G4S8eR6A1R1A6A2A2A2Lw;A4F_;F_;F_;FB1;Ftp;Frho;").
Proof using OKF OKP Hres Hsb Hal Hlo Hhi HB Htop Hband.
  intros rho tp B1 HN18 HSP Hfree3. pose proof E20g_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & R13 & R14 & R15 & Hnx).
  pose proof TOP_bounds as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB. pose proof alloc_top_mg as ATG. pose proof n3w_val as NV3.
  pose proof (band_clear_of_free _ brk0w n3w Hband Hfree3 ltac:(rewrite NV3; lia)) as HBD. rewrite NV3 in HBD.
  pose proof mg_vmmaps as MG.
  assert (Upg : bv_unsigned pgw = 4096) by reflexivity.
  apply triple1_ecall_detA; [apply OKFx | apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md mg Hem) as (Evm & Elz & _ & _).
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (regs_of_pending rho tp E20g [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5 & Hp).
  rewrite R17 in Hp. rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in Hp, G0, G1, G2, G3, G4, G5. unfold vBRK in G0. cbn [eval] in G0. rewrite HN18 in G0. change (Z_to_bv 64 4096) with pgw in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0) by (rewrite G1; discriminate).
  destruct (mmap_fixed_noaccess_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as (Hshape & Hnnone & Hnrw).
  { rewrite G2. reflexivity. } { rewrite G3. reflexivity. } { rewrite G5. reflexivity. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = 4096) by (rewrite G1; reflexivity).
  assert (HnZ : mmap_n (ms_gpr ms 1) = pgw) by (rewrite G1; reflexivity).
  assert (Hceil : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= alloc_top (m_vmmaps md)) by (rewrite G0, HnZ', Evm, ATG; unfold brk0 in *; lia).
  assert (Halign : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite G0; exact Hal).
  assert (Hpos : 0 < bv_unsigned (ms_gpr ms 0)) by (rewrite G0; unfold brk0 in *; lia).
  assert (Hfreeres : region_free (vm_reserved (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm, MG. cbn [vm_reserved]. rewrite Hres.
    apply region_free_of_forall. intros b s Hin. apply (reserved_A_clear brk0w pgw b s Hin). unfold brk0 in *; lia. }
  assert (Hcont : map_contains (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm, MG. cbn [vm_maps]. unfold map_contains. cbn [existsb fst snd].
    rewrite n2w_val, Upg. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  pose proof (xshadow_clear_of_disj rho E20g brk0w 4096 SHADOW_BAND_LO (SHADOW_BAND_HI - SHADOW_BAND_LO) eq_refl eq_refl
                (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) facts_M_in_E20g
                ltac:(unfold SHADOW_BAND_LO; lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) ltac:(intros x Hx; apply HBD; lia)) as [HXb _].
  assert (Hobjs : forall o, In o (ss_objs (ax_S E20g)) -> ranges_disjoint (obj_range rho o) (bv_unsigned brk0w, bv_unsigned brk0w + 4096)).
  { intros o Ho.
    apply (objs_clear_M_sound rho [] (ax_S E20g) brk0w 4096 TOP (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) objs_clear_E20g);
      [lia | | exact HSP | intros x Hx; unfold brk0 in *; lia | intros i sz [] | exact Ho].
      unfold brk0 in *; lia. }
  split.
  - eapply (OKPx mg B1); [exact HK | exact Hp |].
    apply (fixed_none_only_okA segsA ms md _ H222 Hlen Hshape Hnnone Hnrw Hceil Halign Hpos Hfreeres Hcont).
  - intros w' Hw.
    destruct (wstep_fixed_none_invA segsA ms md _ Hh H222 Hlen Hshape Hnnone Hnrw Hceil Halign Hpos Hfreeres Hcont [] w' Hp Hw)
      as [-> | [-> | ->]].
    +   left. split; [|cbn [w_tr w_cfg fst snd cfg_model]; exact HK].
      rewrite S20g_ko_eq. unfold enomem_ret.
      eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    +   right; left.
      assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = false) by (rewrite G3; apply mmap_noreserve_b_50; reflexivity).
      unfold mmap_fixed_ok_model, with_mmap_replacement. rewrite (with_mmap_backing_plain _ _ _ _ Enr). rewrite HnZ, G0, Upg.
      split.
      * rewrite S20g_ok_eq. unfold A_after.
        eapply (smatchA_after_protnone segsA rho (rho20 rho) tp E20g [] ms md [] (mmap_fixed_ok_vm (m_vmmaps md) brk0w pgw) brk0w pgw brk0w vBRK (ss_next (ax_S E20g)) Hsp).
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- exact Hal.
        -- rewrite Upg. reflexivity.
        -- rewrite Upg. unfold brk0 in *. lia.
        -- rewrite Upg. exact Hobjs.
        -- rewrite Upg. exact HXb.
        -- unfold rho20. apply agree_below_refl.
        -- apply Pos.le_refl.
        -- rewrite Hnx. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
        -- unfold rho20, vBRK. cbn [eval rw set_rm]. exact HN18.
      * cbn [cfg_model w_cfg w_tr fst snd]. split; [reflexivity|]. split.
        -- unfold mg_ok. rewrite <- Evm. unfold brk0. apply erase_mat_cong_forget. exact Hem.
        -- pose proof (MI_ivs_wf segsA _ _ HMI) as Hivs. pose proof Hivs as (W1 & W2 & W3).
           pose proof (used_protnone_le md (mmap_fixed_ok_vm (m_vmmaps md) brk0w pgw) brk0w pgw Hivs ltac:(rewrite Upg; unfold brk0 in *; lia) eq_refl eq_refl) as UP.
           rewrite Upg in UP.
           pose proof (unpaid_forget_le (with_vmmaps (mmap_fixed_ok_vm (m_vmmaps md) brk0w pgw) md) (bv_unsigned brk0w) (bv_unsigned brk0w + 4096) tp
                         ltac:(rewrite m_vm_lazy_with_vmmaps; exact W3) (MI_nodupT segsA _ _ HMI)) as UF.
           rewrite (unpaid_ext md (with_vmmaps _ md)) in UF by reflexivity.
           unfold paid in Hpaid |- *. pose proof page_size_pos. nia.
    +   right; right.
      unfold mmap_fixed_dead_model, with_mmap_destroyed. rewrite HnZ, G0, Upg.
      split.
      {
        unfold mg_dead. rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. unfold mmap_fixed_dead_vm. cbn [vm_reserved vm_maps].
        rewrite <- Evm, ?Upg.
        apply band_covered_subtract; [exact (proj1 (MI_ivs_wf segsA _ _ HMI)) | lia | | rewrite Evm; exact band_mg].
        unfold brk0 in *. unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *. right.
        destruct (Z.le_gt_cases (bv_unsigned brk0w + 4096) 0x7fff7000) as [L|L]; [exact L|]. exfalso.
        destruct (Z.le_gt_cases 0x7fff7000 (bv_unsigned brk0w)).
        * apply (HBD (bv_unsigned brk0w)); lia.
        * apply (HBD 0x7fff7000); lia. }
      split.
      * rewrite S20g_ko_eq. unfold A_after.
        eapply (smatchA_after_destroy segsA rho (rho20 rho) tp E20g [] ms md [] (mmap_fixed_dead_vm (m_vmmaps md) brk0w pgw) brk0w pgw _ (SLit enomem_ret) (ss_next (ax_S E20g)) Hsp).
        -- reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- exact Hal.
        -- rewrite Upg. reflexivity.
        -- rewrite Upg. unfold brk0 in *. lia.
        -- rewrite Upg. exact Hobjs.
        -- rewrite Upg. exact HXb.
        -- unfold rho20. apply agree_below_refl.
        -- apply Pos.le_refl.
        -- reflexivity.
        -- cbn [eval]. unfold enomem_ret. apply Z_to_bv_bv_unsigned.
      * cbn [cfg_model w_cfg w_tr fst snd]. split; [reflexivity|]. split.
        -- unfold mg_dead. rewrite <- Evm. unfold brk0. apply erase_mat_cong_forget. exact Hem.
        -- pose proof (MI_ivs_wf segsA _ _ HMI) as Hivs. pose proof Hivs as (W1 & W2 & W3).
           unfold paid, tp20.
           pose proof (unpaid_forget_le (with_vmmaps (mmap_fixed_dead_vm (m_vmmaps md) brk0w pgw) md) (bv_unsigned brk0w) (bv_unsigned brk0w + 4096)
                         (tp_forget brk0 (brk0 + 4096) tp) ltac:(rewrite m_vm_lazy_with_vmmaps; exact W3)
                         ltac:(unfold tp_forget; apply List.NoDup_filter; exact (MI_nodupT segsA _ _ HMI))) as L.
           rewrite (unpaid_ext md (with_vmmaps _ md)) in L by reflexivity.
           pose proof (used_destroy_le md (mmap_fixed_dead_vm (m_vmmaps md) brk0w pgw) (bv_unsigned brk0w) (bv_unsigned brk0w + 4096) Hivs ltac:(lia)
                         ltac:(cbn; rewrite Upg; reflexivity) ltac:(cbn; rewrite Upg; reflexivity)) as UD.
           assert (LT : (length (unpaid md (tp_forget brk0 (brk0 + 4096) tp)) <= length (unpaid md tp))%nat).
           { unfold unpaid, tp_forget.
             apply List.NoDup_incl_length; [apply List.NoDup_filter; apply List.NoDup_filter; exact (MI_nodupT segsA _ _ HMI)|].
             intros p Hpin. apply List.filter_In in Hpin as [Hp1 Hp2]. apply List.filter_In in Hp1 as [Hp0 Hp1]. apply List.filter_In. split; [exact Hp0|exact Hp2]. }
           unfold paid in Hpaid. unfold brk0 in *. pose proof page_size_pos. nia.
Qed.

Theorem enode20g_ok : forall (rho : valuation) (tp : list word) (B1 : Z),
  rw rho N18 = brk0w -> TOP + D_M <= bv_unsigned (rw rho 10%positive) ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) brk0w n3w = true ->
  etriple segsA (SPA segsA (KxA mg B1) E20g rho tp) (SPA segsA (KxA mg_ok B1) S20g_ok (rho20 rho) tp).
Proof using Hres Hsb Hal Hlo Hhi HB Htop Hband.
  intros rho tp B1 HN18 HSP Hfree3. pose proof E20g_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & R13 & R14 & R15 & Hnx).
  pose proof TOP_bounds as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB. pose proof alloc_top_mg as ATG. pose proof n3w_val as NV3.
  pose proof (band_clear_of_free _ brk0w n3w Hband Hfree3 ltac:(rewrite NV3; lia)) as HBD. rewrite NV3 in HBD.
  pose proof mg_vmmaps as MG.
  assert (Upg : bv_unsigned pgw = 4096) by reflexivity.
  apply etriple_ecall_detA; [apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md mg Hem) as (Evm & Elz & _ & _).
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (regs_of_pending rho tp E20g [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5 & Hp).
  rewrite R17 in Hp. rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in Hp, G0, G1, G2, G3, G4, G5. unfold vBRK in G0. cbn [eval] in G0. rewrite HN18 in G0. change (Z_to_bv 64 4096) with pgw in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0) by (rewrite G1; discriminate).
  destruct (mmap_fixed_noaccess_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as (Hshape & Hnnone & Hnrw).
  { rewrite G2. reflexivity. } { rewrite G3. reflexivity. } { rewrite G5. reflexivity. }
  assert (HnZ' : mmap_nZ (ms_gpr ms 1) = 4096) by (rewrite G1; reflexivity).
  assert (HnZ : mmap_n (ms_gpr ms 1) = pgw) by (rewrite G1; reflexivity).
  assert (Hceil : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) <= alloc_top (m_vmmaps md)) by (rewrite G0, HnZ', Evm, ATG; unfold brk0 in *; lia).
  assert (Halign : bv_unsigned (ms_gpr ms 0) mod page_size = 0) by (rewrite G0; exact Hal).
  assert (Hpos : 0 < bv_unsigned (ms_gpr ms 0)) by (rewrite G0; unfold brk0 in *; lia).
  assert (Hfreeres : region_free (vm_reserved (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm, MG. cbn [vm_reserved]. rewrite Hres.
    apply region_free_of_forall. intros b s Hin. apply (reserved_A_clear brk0w pgw b s Hin). unfold brk0 in *; lia. }
  assert (Hcont : map_contains (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite G0, HnZ, Evm, MG. cbn [vm_maps]. unfold map_contains. cbn [existsb fst snd].
    rewrite n2w_val, Upg. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  pose proof (xshadow_clear_of_disj rho E20g brk0w 4096 SHADOW_BAND_LO (SHADOW_BAND_HI - SHADOW_BAND_LO) eq_refl eq_refl
                (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) facts_M_in_E20g
                ltac:(unfold SHADOW_BAND_LO; lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) ltac:(intros x Hx; apply HBD; lia)) as [HXb _].
  assert (Hobjs : forall o, In o (ss_objs (ax_S E20g)) -> ranges_disjoint (obj_range rho o) (bv_unsigned brk0w, bv_unsigned brk0w + 4096)).
  { intros o Ho.
    apply (objs_clear_M_sound rho [] (ax_S E20g) brk0w 4096 TOP (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) objs_clear_E20g);
      [lia | | exact HSP | intros x Hx; unfold brk0 in *; lia | intros i sz [] | exact Ho].
      unfold brk0 in *; lia. }
  eexists. split; [exact (wstep_fixed_none_intro_okA segsA ms md _ Hh H222 Hlen Hshape Hnnone Hnrw Hceil Halign Hpos Hfreeres Hcont [] Hp)|].
  assert (Enr : mmap_noreserve_b (ms_gpr ms 3) = false) by (rewrite G3; apply mmap_noreserve_b_50; reflexivity).
  unfold mmap_fixed_ok_model, with_mmap_replacement. rewrite (with_mmap_backing_plain _ _ _ _ Enr). rewrite HnZ, G0, Upg.
  split.
  * rewrite S20g_ok_eq. unfold A_after.
    eapply (smatchA_after_protnone segsA rho (rho20 rho) tp E20g [] ms md [] (mmap_fixed_ok_vm (m_vmmaps md) brk0w pgw) brk0w pgw brk0w vBRK (ss_next (ax_S E20g)) Hsp).
    -- reflexivity.
    -- reflexivity.
    -- reflexivity.
    -- exact Hal.
    -- rewrite Upg. reflexivity.
    -- rewrite Upg. unfold brk0 in *. lia.
    -- rewrite Upg. exact Hobjs.
    -- rewrite Upg. exact HXb.
    -- unfold rho20. apply agree_below_refl.
    -- apply Pos.le_refl.
    -- rewrite Hnx. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
    -- unfold rho20, vBRK. cbn [eval rw set_rm]. exact HN18.
  * cbn [cfg_model w_cfg w_tr fst snd]. split; [reflexivity|]. split.
    -- unfold mg_ok. rewrite <- Evm. unfold brk0. apply erase_mat_cong_forget. exact Hem.
    -- pose proof (MI_ivs_wf segsA _ _ HMI) as Hivs. pose proof Hivs as (W1 & W2 & W3).
       pose proof (used_protnone_le md (mmap_fixed_ok_vm (m_vmmaps md) brk0w pgw) brk0w pgw Hivs ltac:(rewrite Upg; unfold brk0 in *; lia) eq_refl eq_refl) as UP.
       rewrite Upg in UP.
       pose proof (unpaid_forget_le (with_vmmaps (mmap_fixed_ok_vm (m_vmmaps md) brk0w pgw) md) (bv_unsigned brk0w) (bv_unsigned brk0w + 4096) tp
                     ltac:(rewrite m_vm_lazy_with_vmmaps; exact W3) (MI_nodupT segsA _ _ HMI)) as UF.
       rewrite (unpaid_ext md (with_vmmaps _ md)) in UF by reflexivity.
       unfold paid in Hpaid |- *. pose proof page_size_pos. nia.
Qed.

Definition mgrant (mx : Model) (a : word) : Model := ltac2:(tb__ "0|0|
S48Sa0S40Vmx;A1S82Va;A3Vmx;A2").
Definition Fgrant (nx : positive) : list sprop := ltac2:(tb__ "0|0|
S38S17S27Vnx;ZcA2S38S17S28S22Vnx;A1S1bSbZ7fffff800000Z1000A2A1A2S34S17A1A3A3").

Section RwNode.
Variables (E : axst) (mx : Model) (Bx : Z) (G : list (sv * Z)).
Hypothesis HXE : ax_X E = X_M.
Hypothesis HbE : ltac2:(tb__ "0|0|
S0S16S63VE;A1S1bSd2A1A3").
Hypothesis HFE : ltac2:(tb__ "0|0|
S17S69S17R1S90A3S69S17R2S1cS62VE;A1A1A3F_;Ff;").
Hypothesis Hecall : ltac2:(tb__ "0|0|
S0S35Sd6A1SddS15S2cS62VE;A1A1A2S36Sd6Sd7A2A3").
Hypothesis R17 : ltac2:(tb__ "0|0|
S0S16S79S16U11S1eS62VE;A1A1S1bZ0A1A4S1bZdeA1A3").
Hypothesis R10 : ltac2:(tb__ "0|1|
S0S16S79S16UaS1eS62VE;A1A1S1bZ0A1M0A4G0A3").
Hypothesis R11 : ltac2:(tb__ "0|0|
S0S16S79S16UbS1eS62VE;A1A1S1bZ0A1A4S1bZ1000A1A3").
Hypothesis R12 : ltac2:(tb__ "0|0|
S0S16S79S16UcS1eS62VE;A1A1S1bZ0A1A4S1bZ3A1A3").
Hypothesis R13 : ltac2:(tb__ "0|0|
S0S16S79S16UdS1eS62VE;A1A1S1bZ0A1A4S1bZ22A1A3").
Hypothesis R14 : ltac2:(tb__ "0|0|
S0S16S79S16UeS1eS62VE;A1A1S1bZ0A1A4S1bSbSaZ2Z40A2Z1A2A1A3").
Hypothesis R15 : ltac2:(tb__ "0|1|
S0S16S79S16UfS1eS62VE;A1A1S1bZ0A1M0A4G0A3").
Hypothesis Hclear : ltac2:(tb__ "0|0|
S0S32SbdVG;S62VE;A1A2S33A3").
Hypothesis Hresx : ltac2:(tb__ "0|1|
S0S2fS31S10Q40A1M0G0A2A1S43S40Vmx;A1A1S6eS15A1A3").
Hypothesis HBx : ltac2:(tb__ "0|0|
S5S6VBx;Z1000A2S4fS40Vmx;A1A1A2").
Hypothesis Htopx : init_sp_ok (m_vmmaps mx).
Hypothesis Hbandx : ltac2:(tb__ "0|2|
Sb5S37S31S10Q40A1M0G0A2S43S40Vmx;A1M1A1S42G1A1A3Sb4Sb6A3").

Theorem node_rw : ltac2:(tb__ "0|8|
S18S2fS10Q40M0A1M1A1S16S13S69S31S16S13A2S30S16S13R2R1A4VG;A3S4G1G1S4G1G1S1S69S31G1G1A2S30G1G1R2R1A4S42S40Vmx;A1M2A1A3S1S5SfG0R2A2M3SfG0S1aR7R5A2A2M4A2S5S6G4R4A2S6G3SfG0R1A2A2A2A2A2Ls;A2Lb;A2F_;Fsz;Fe;S5S6S4eG2A1S8fA2SfG0S19R3PaA2A2A2S72S15Vok;S5eS15S6fVmx;VBx;A2M5VE;R4R3A5S70S2S5eS15G5Sa5VE;A1R5R4R1A6S4G1G1S1S93S11G0Z0A2Vmx;S82R1A4S5eS15S6fS89Vmx;R1A2S6VBx;Z1000M6A2A2SadVE;S22S21S62VE;A1A1M7A1S38S1dSc1G7G6A2S34S1dA1A3S87G7A1SbcG7A1A5Sc0R6G7R1A3R5R2A6A2La;A2A2Lw;A4F_;F_;Ftp;Frho;").
Proof using OKF OKP HXE HbE HFE Hecall R17 R10 R11 R12 R13 R14 R15 Hclear Hresx HBx Htopx Hbandx.
  clear Hres Hsb Hal Hlo Hhi HB Htop Hband.
  intros rho tp HG HSP. pose proof (alloc_top_bounds _ Htopx) as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB.
  assert (Upg : bv_unsigned pgw = 4096) by reflexivity.
  assert (HnZ : mmap_nZ pgw = 4096) by reflexivity. assert (Hn : mmap_n pgw = pgw) by reflexivity.
  eapply triple1_conseq; [intros w Hw; exact Hw | |].
  2:{ apply (triple1_mmap_rw_objA segsA ok (KxA mx Bx) (KxA mx Bx)
        (fun a rho' tp' tr' md' => mmap_place_ok_none (Z_to_bv 64 0) mx pgw a /\ KxA (mgrant mx a) (Bx + 4096) rho' tp' tr' md')
        E rho tp 4096).
      - apply OKFx. - apply OKPx. - apply stableA_KxA. - exact Hecall.
      - unfold reg_sv. exact R17. - unfold reg_sv. exact R11. - reflexivity. - lia.
      - intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
        pose proof (erase_mat_eq_fields md mx Hem) as (Evm & _).
        pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
        destruct (regs_of_pending rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5 & _).
        rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
        cbn [eval] in G0, G1, G2, G3, G4, G5. change (Z_to_bv 64 4096) with pgw in G1.
        split; [rewrite G2, G3, G5; apply mmap_modeled_b_intro; reflexivity|].
        split; [rewrite G3; reflexivity|].
        split; [unfold headroom; rewrite Evm; lia|].
        split; [exact HK|].
        intros a Hpl. rewrite G0, G1, G3 in Hpl.
        pose proof Hpl as (Pal & Ppos & Pceil & Pfree & _).
        rewrite HnZ in Pceil. rewrite Hn in Pfree.
        assert (Hplx : mmap_place_ok_none (Z_to_bv 64 0) mx pgw a).
        { unfold mmap_place_ok_none. rewrite HnZ, Hn, <- Evm. repeat split; assumption. }
        assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a pgw = true) by exact (region_free_app_r _ _ _ _ Pfree).
        pose proof (grant_facts_A _ _ _ _ _ Hpl ltac:(rewrite Evm; exact Hresx)) as (_ & _ & _ & Himg & Hmaps). rewrite HnZ in Himg, Hmaps.
        pose proof (band_clear_of_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) a pgw ltac:(rewrite Evm; exact Hbandx) Pfree ltac:(rewrite Upg; lia)) as HBD.
        rewrite Upg in HBD.
        pose proof (xshadow_clear_of_disj rho E a 4096 SHADOW_BAND_LO (SHADOW_BAND_HI - SHADOW_BAND_LO) HXE HbE
                      (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) HFE
                      ltac:(unfold SHADOW_BAND_LO; lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) ltac:(intros x Hx; apply HBD; lia)) as [HXb _].
        split; [|split; [|split]].
        + intros o Ho.
          apply (objs_clear_M_sound rho G (ax_S E) a 4096 (alloc_top (m_vmmaps mx)) (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear);
            [lia | rewrite <- Evm; exact Pceil | exact HSP | exact Himg | | exact Ho].
          intros i sz Hin x Hx Hblk. destruct (HG i sz Hin) as (b & s0 & Hm & Hb1 & Hb2).
          apply (Hmaps b s0 ltac:(rewrite Evm; exact Hm) x Hx). lia.
        + intros x Hx. apply (grant_no_ro_A a 4096); [exact Himg | exact Hx].
        + exact HXb.
        + split; [exact Hplx|]. rewrite G1. split; [reflexivity|]. split.
          * unfold mgrant, mmap_rw_vm. rewrite Hn, <- Evm. apply erase_mat_cong_vmmaps. exact Hem.
          * rewrite paid_with_vmmaps.
            pose proof (used_maps_cons_le md (mmap_rw_vm (m_vmmaps md) pgw a) a pgw (MI_ivs_wf segsA _ _ HMI)
                         ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite Upg; pose proof (alloc_top_lt (m_vmmaps md)); unfold two_pow_64 in *; lia)
                         ltac:(unfold mmap_rw_vm; rewrite Hn; reflexivity) eq_refl) as U.
            rewrite Upg in U. lia. }
  intros w [Hw | (a & Hsm & Hpl & Hk)]; [left | right; exists a].
  { unfold refuse, enomem_ret. replace (A_after E (SLit (bv_unsigned (errno_ret ENOMEM)))) with (mkAX (S_ret_lit (ax_S E) (errno_ret ENOMEM)) [] (SLit SHB)) || idtac. exact Hw. }
  split; [exact Hpl|].

  unfold cont.
  change (ax_setS E (add_facts (Fgrant (ss_next (ax_S E))) (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) 4096]) (Pos.succ (ss_next (ax_S E))))))
    with (ax_with_facts (ax_setS E (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) 4096]) (Pos.succ (ss_next (ax_S E)))))
            (Fgrant (ss_next (ax_S E)) ++ ss_facts (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) 4096]) (Pos.succ (ss_next (ax_S E)))))).
  apply SPA_refacts; [split; [exact Hsm|exact Hk] | |].
  - cbn [ax_S ax_setS ss_next S_after]. rewrite forallb_app.
    assert (X : (ss_next (ax_S E) <? Pos.succ (ss_next (ax_S E)))%positive = true) by (apply Pos.ltb_lt; lia).
    apply andb_true_intro. split.
    + unfold Fgrant. cbn. rewrite !X. reflexivity.
    + destruct Hsm as ((W & _) & _). cbn [ax_S ax_setS] in W. exact (swf_facts _ W).
  - intros HF. apply Forall_app. split; [|exact HF].
    pose proof Hpl as (Pal & Ppos & Pceil & Pfree). rewrite HnZ in Pceil.
    unfold Fgrant. cbn [ax_S ax_setS ss_next S_after].
    assert (E1 : rw (rho_set_rw rho (ss_next (ax_S E)) a) (ss_next (ax_S E)) = a) by apply rho_set_rw_at.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E1.
    + change (2 ^ 12) with 4096. split; [lia|exact Pal].
    + rewrite u64_of_lit by lia. lia.
Qed.

Theorem enode_rw_any : ltac2:(tb__ "0|8|
S18S2fS10Q40M0A1M1A1S16S13S69S31S16S13A2S30S16S13R2R1A4VG;A3S4G1G1S4G1G1S1S69S31G1G1A2S30G1G1R2R1A4S42S40Vmx;A1M2A1A3S1S5SfG0R2A2M3SfG0S1aR7R5A2A2M4A2S5S6G4R4A2S6G3SfG0R1A2A2A2A2A2Ls;A2Lb;A2F_;Fsz;Fe;S5S6S4eG2A1S8fA2SfG0S19R3PaA2A2A2S73S15S5eS15S6fVmx;VBx;A2M5VE;R4R3A5S70S2S5eS15G5Sa5VE;A1R5R4R1A6S4G1G1S1S93S11G0Z0A2Vmx;S82R1A4S5eS15S6fS89Vmx;R1A2S6VBx;Z1000M6A2A2SadVE;S22S21S62VE;A1A1M7A1S38S1dSc1G7G6A2S34S1dA1A3S87G7A1SbcG7A1A5Sc0R6G7R1A3R5R2A6A2La;A2A2Lw;A3F_;F_;Ftp;Frho;").
Proof using HXE HbE HFE Hecall R17 R10 R11 R12 R13 R14 R15 Hclear Hresx HBx Htopx Hbandx.
  clear Hres Hsb Hal Hlo Hhi HB Htop Hband.
  intros rho tp HG HSP. pose proof (alloc_top_bounds _ Htopx) as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB.
  assert (Upg : bv_unsigned pgw = 4096) by reflexivity.
  assert (HnZ : mmap_nZ pgw = 4096) by reflexivity. assert (Hn : mmap_n pgw = pgw) by reflexivity.
  eapply etriple_conseq; [intros w Hw; exact Hw | |].
  2:{ apply (etriple_mmap_rw_obj_anyA segsA (KxA mx Bx) (KxA mx Bx)
        (fun a rho' tp' tr' md' => mmap_place_ok_none (Z_to_bv 64 0) mx pgw a /\ KxA (mgrant mx a) (Bx + 4096) rho' tp' tr' md')
        E rho tp 4096).
      - apply stableA_KxA. - exact Hecall.
      - unfold reg_sv. exact R17. - unfold reg_sv. exact R11. - reflexivity. - lia.
      - intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
        pose proof (erase_mat_eq_fields md mx Hem) as (Evm & _).
        pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
        destruct (regs_of_pending rho tp E [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5 & _).
        rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
        cbn [eval] in G0, G1, G2, G3, G4, G5. change (Z_to_bv 64 4096) with pgw in G1.
        split; [rewrite G2, G3, G5; apply mmap_modeled_b_intro; reflexivity|].
        split; [rewrite G3; reflexivity|].
        split; [unfold headroom; rewrite Evm; lia|].
        split; [exact HK|].
        intros a Hpl. rewrite G0, G1, G3 in Hpl.
        pose proof Hpl as (Pal & Ppos & Pceil & Pfree & _).
        rewrite HnZ in Pceil. rewrite Hn in Pfree.
        assert (Hplx : mmap_place_ok_none (Z_to_bv 64 0) mx pgw a).
        { unfold mmap_place_ok_none. rewrite HnZ, Hn, <- Evm. repeat split; assumption. }
        assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a pgw = true) by exact (region_free_app_r _ _ _ _ Pfree).
        pose proof (grant_facts_A _ _ _ _ _ Hpl ltac:(rewrite Evm; exact Hresx)) as (_ & _ & _ & Himg & Hmaps). rewrite HnZ in Himg, Hmaps.
        pose proof (band_clear_of_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) a pgw ltac:(rewrite Evm; exact Hbandx) Pfree ltac:(rewrite Upg; lia)) as HBD.
        rewrite Upg in HBD.
        pose proof (xshadow_clear_of_disj rho E a 4096 SHADOW_BAND_LO (SHADOW_BAND_HI - SHADOW_BAND_LO) HXE HbE
                      (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) HFE
                      ltac:(unfold SHADOW_BAND_LO; lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) ltac:(intros x Hx; apply HBD; lia)) as [HXb _].
        split; [|split; [|split]].
        + intros o Ho.
          apply (objs_clear_M_sound rho G (ax_S E) a 4096 (alloc_top (m_vmmaps mx)) (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) Hclear);
            [lia | rewrite <- Evm; exact Pceil | exact HSP | exact Himg | | exact Ho].
          intros i sz Hin x Hx Hblk. destruct (HG i sz Hin) as (b & s0 & Hm & Hb1 & Hb2).
          apply (Hmaps b s0 ltac:(rewrite Evm; exact Hm) x Hx). lia.
        + intros x Hx. apply (grant_no_ro_A a 4096); [exact Himg | exact Hx].
        + exact HXb.
        + split; [exact Hplx|]. rewrite G1. split; [reflexivity|]. split.
          * unfold mgrant, mmap_rw_vm. rewrite Hn, <- Evm. apply erase_mat_cong_vmmaps. exact Hem.
          * rewrite paid_with_vmmaps.
            pose proof (used_maps_cons_le md (mmap_rw_vm (m_vmmaps md) pgw a) a pgw (MI_ivs_wf segsA _ _ HMI)
                         ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite Upg; pose proof (alloc_top_lt (m_vmmaps md)); unfold two_pow_64 in *; lia)
                         ltac:(unfold mmap_rw_vm; rewrite Hn; reflexivity) eq_refl) as U.
            rewrite Upg in U. lia. }
  intros w [Hw | (a & Hsm & Hpl & Hk)]; [left | right; exists a].
  { unfold refuse, enomem_ret. replace (A_after E (SLit (bv_unsigned (errno_ret ENOMEM)))) with (mkAX (S_ret_lit (ax_S E) (errno_ret ENOMEM)) [] (SLit SHB)) || idtac. exact Hw. }
  split; [exact Hpl|].

  unfold cont.
  change (ax_setS E (add_facts (Fgrant (ss_next (ax_S E))) (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) 4096]) (Pos.succ (ss_next (ax_S E))))))
    with (ax_with_facts (ax_setS E (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) 4096]) (Pos.succ (ss_next (ax_S E)))))
            (Fgrant (ss_next (ax_S E)) ++ ss_facts (S_after (ax_S E) (SVar (ss_next (ax_S E))) (ss_objs (ax_S E) ++ [mmap_obj (ss_next (ax_S E)) 4096]) (Pos.succ (ss_next (ax_S E)))))).
  apply SPA_refacts; [split; [exact Hsm|exact Hk] | |].
  - cbn [ax_S ax_setS ss_next S_after]. rewrite forallb_app.
    assert (X : (ss_next (ax_S E) <? Pos.succ (ss_next (ax_S E)))%positive = true) by (apply Pos.ltb_lt; lia).
    apply andb_true_intro. split.
    + unfold Fgrant. cbn. rewrite !X. reflexivity.
    + destruct Hsm as ((W & _) & _). cbn [ax_S ax_setS] in W. exact (swf_facts _ W).
  - intros HF. apply Forall_app. split; [|exact HF].
    pose proof Hpl as (Pal & Ppos & Pceil & Pfree). rewrite HnZ in Pceil.
    unfold Fgrant. cbn [ax_S ax_setS ss_next S_after].
    assert (E1 : rw (rho_set_rw rho (ss_next (ax_S E)) a) (ss_next (ax_S E)) = a) by apply rho_set_rw_at.
    repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E1.
    + change (2 ^ 12) with 4096. split; [lia|exact Pal].
    + rewrite u64_of_lit by lia. lia.
Qed.
End RwNode.

Lemma find_segment_none_A' : ltac2:(tb__ "0|0|
S13S3S1S5Z10000R1A2S7R1Z643000A2A2A1S0S35ScaA1S78S15R2Z1A3S3eScaA1A3F_;Fz;").
Proof.
  clear. intros z Hz. unfold segsA. cbn -[Z.leb Z.ltb Z.add Z.of_N].
  change (Z.of_N 65536%N) with 65536. change (Z.of_N 176128%N) with 176128.
  change (Z.of_N 241664%N) with 241664. change (Z.of_N 679936%N) with 679936.
  change (Z.of_N 921600%N) with 921600. change (Z.of_N 20480%N) with 20480.
  change (Z.of_N 942080%N) with 942080. change (Z.of_N 5623808%N) with 5623808.
  repeat match goal with |- context [if ?c then _ else _] =>
    destruct c eqn:?C; [apply andb_prop in C as [?C1 ?C2]; apply Z.leb_le in C1; apply Z.leb_le in C2; lia | clear C] end.
  reflexivity.
Qed.

Definition n8w : word := Z_to_bv 64 8192.
Definition mf_res (a : word) : Model := ltac2:(tb__ "0|0|
S48S99S40Vm;A1S80Va;A3Vm;A2").

Definition rho20f (rho : valuation) (a : word) : valuation := ltac2:(tb__ "0|0|
Sc0Sd8Vrho;Sb9S20Vrho;A1Va;S80A3A2SbcSa4A1Va;A3").

Lemma objs_clear_E20f : ltac2:(tb__ "0|0|
S0S32SbdS34S31S16S13A2A1S62Sa2A1A2S33A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma facts_M_in_E20f : ltac2:(tb__ "0|0|
S17S69S17R1S90A3S69S17R2S1cS62Sa2A1A1A3F_;Ff;").
Proof. intros f Hf. vm_compute in Hf. vm_compute. tauto. Qed.

Lemma node20f_core : ltac2:(tb__ "0|3|
S18S2fS10Q40M0A1M1A1S5S6S7bS8fA2SfG0S19R2PaA2A2A2S2fS41A1M2S76S44Sc6S15R6R5Sa2S30G2S6bR3S6cR2R1A2A4A5S6fVm;VB;R7R6R4R2A6S1Vok;S30G2S6bR5S6cR4R3A2A4A1S70S71S15S30G2S6bR6S6cR5R4A2A4R1A3S70S2S5eS15S6fVm;VB;A2Sa5Sa2A1RbRaR1A6S4G1G1S1S93S11G0Z0A2Vm;S80R1A4S5eS15S6fS7eR1A1VB;A2Sa8S86RcR1A2RbR2A6A2La;A2A2Lw;R2A1F_;Fw';A2F_;F_;Fmd;Fms;Ftr;F_;Ftp;Frho;").
Proof using OKF OKP Hres HB Htop Hband.
  clear Hsb Hal Hlo Hhi.
  intros rho tp HSP. pose proof E20f_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & R13 & R14 & R15 & Hnx).
  pose proof TOP_bounds as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB.
  assert (Un8 : bv_unsigned n8w = 8192) by reflexivity.
  assert (HnZ : mmap_nZ n8w = 8192) by reflexivity. assert (Hn : mmap_n n8w = n8w) by reflexivity.
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md m Hem) as (Evm & _ & _ & _).
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (regs_of_pending rho tp E20f [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5 & Hp).
  rewrite R17 in Hp. rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R14 in G4. rewrite R15 in G5.
  cbn [eval] in Hp, G0, G1, G2, G3, G4, G5. change (Z_to_bv 64 8192) with n8w in G1.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0) by (rewrite G1; discriminate).
  destruct (mmap_noaccess_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as [Hsh Hnrw].
  { rewrite G2. reflexivity. } { rewrite G3. reflexivity. } { rewrite G5. reflexivity. }
  split.
  - eapply (OKPx m B); [exact HK | exact Hp | exact (mmap_none_only_okA segsA ms md _ Hh H222 Hlen Hsh Hnrw)].
  - intros w' Hw.
    destruct (wstep_mmap_none_invA segsA ms md _ Hh H222 Hlen Hsh Hnrw [] w' Hp Hw) as [-> | (a & Hpl & ->)].
    + left. split; [|cbn [w_tr w_cfg fst snd cfg_model]; exact HK].
      unfold refuse, enomem_ret. eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    + right. exists a. rewrite G0, G1 in Hpl. rewrite ?G1, ?G3.
      pose proof Hpl as (Pal & Ppos & Pceil & Pfree). rewrite HnZ in Pceil. rewrite Hn in Pfree.
      assert (Hplm : mmap_place_ok_none (Z_to_bv 64 0) m n8w a).
      { unfold mmap_place_ok_none. rewrite HnZ, Hn, <- Evm. repeat split; assumption. }
      split; [exact Hplm|].
      assert (Hfree_m : region_free (vm_maps (m_vmmaps md)) a n8w = true) by exact (region_free_app_r _ _ _ _ Pfree).
      pose proof (grant_facts_none_A (Z_to_bv 64 0) md n8w a Hpl ltac:(rewrite Evm; exact Hres)) as [Himg Hmaps]. rewrite HnZ in Himg, Hmaps.
      pose proof (band_clear_of_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) a n8w ltac:(rewrite Evm; exact Hband) Pfree ltac:(rewrite Un8; lia)) as HBD.
      rewrite Un8 in HBD.
      pose proof (xshadow_clear_of_disj rho E20f a 8192 SHADOW_BAND_LO (SHADOW_BAND_HI - SHADOW_BAND_LO) eq_refl eq_refl
                    (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) facts_M_in_E20f
                    ltac:(unfold SHADOW_BAND_LO; lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) ltac:(intros x Hx; apply HBD; lia)) as [HXb _].
      assert (Enr34 : mmap_noreserve_b (Z_to_bv 64 34) = false) by (apply mmap_noreserve_b_34; reflexivity).
      unfold mmap_none_model. rewrite Hn. rewrite (with_mmap_backing_plain (Z_to_bv 64 34) a n8w _ Enr34).
      assert (Hsm1 : smatchA segsA (rho20f rho a) tp (ax_setS E20f (S_after (ax_S E20f) (SVar (Pos.succ N18)) (ss_objs (ax_S E20f)) (Pos.succ (Pos.succ N18))))
                       ([], mkCfg (after_sys_mem ms a (unmap_range (ms_mem ms) a n8w)) (with_vmmaps (mmap_none_vm (m_vmmaps md) n8w a) md))).
      { rewrite <- (with_mmap_backing_plain (Z_to_bv 64 34) a n8w (with_vmmaps (mmap_none_vm (m_vmmaps md) n8w a) md) Enr34).
        eapply (smatchA_after_grant_none segsA rho (rho20f rho a) tp E20f [] ms md [] (mmap_none_vm (m_vmmaps md) n8w a) (Z_to_bv 64 34) a n8w a
                  (SVar (Pos.succ N18)) (Pos.succ (Pos.succ N18)) Hsp).
        -- unfold mmap_none_vm. rewrite Hn. reflexivity.
        -- unfold mmap_none_vm. rewrite Hn. reflexivity.
        -- reflexivity.
        -- exact Pal.
        -- rewrite Un8. reflexivity.
        -- rewrite Un8. lia.
        -- rewrite Un8. rewrite Evm in Pceil. unfold TOP in TB. lia.
        -- exact Hfree_m.
        -- intros z Hz. apply find_segment_none_A'. rewrite Un8 in Hz. exact (Himg z Hz).
        -- rewrite Un8. intros o Ho.
           apply (objs_clear_M_sound rho [] (ax_S E20f) a 8192 TOP (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) objs_clear_E20f);
             [lia | rewrite Evm in Pceil; exact Pceil | exact HSP | exact Himg | intros i sz [] | exact Ho].
        -- rewrite Un8. exact HXb.
        -- unfold rho20f. rewrite Hnx. apply agree_below_set_rw. lia.
        -- rewrite Hnx. lia.
        -- cbn. apply Pos.ltb_lt. lia.
        -- unfold rho20f. cbn [eval]. apply rho_set_rw_at. }
      assert (HSPA : SPA segsA (KxA (mf_res a) B) (ax_setS E20f (S_after (ax_S E20f) (SVar (Pos.succ N18)) (ss_objs (ax_S E20f)) (Pos.succ (Pos.succ N18)))) (rho20f rho a) tp
                      ([], mkCfg (after_sys_mem ms a (unmap_range (ms_mem ms) a n8w)) (with_vmmaps (mmap_none_vm (m_vmmaps md) n8w a) md))).
      { split; [exact Hsm1|]. cbn [w_tr w_cfg fst snd cfg_model]. split; [reflexivity|]. split.
        -- unfold mf_res. rewrite <- Evm. apply erase_mat_cong_vmmaps. exact Hem.
        -- rewrite paid_with_vmmaps.
           pose proof (used_none_cons_le md (mmap_none_vm (m_vmmaps md) n8w a) a n8w (MI_ivs_wf segsA _ _ HMI)
                        ltac:(unfold iv_wf, ivB, ivS; cbn [fst snd]; rewrite Un8; pose proof (alloc_top_lt (m_vmmaps md)); unfold two_pow_64 in *; lia)
                        ltac:(unfold mmap_none_vm; rewrite Hn; reflexivity) ltac:(unfold mmap_none_vm; rewrite Hn; reflexivity)) as U. lia. }

      unfold S20f, cont.
      change (ax_setS E20f (add_facts F20f (S_after (ax_S E20f) vRES (ss_objs (ax_S E20f) ++ []) (Pos.succ (Pos.succ N18)))))
        with (ax_with_facts (ax_setS E20f (S_after (ax_S E20f) vRES (ss_objs (ax_S E20f) ++ []) (Pos.succ (Pos.succ N18))))
                (F20f ++ ss_facts (S_after (ax_S E20f) vRES (ss_objs (ax_S E20f) ++ []) (Pos.succ (Pos.succ N18))))).
      rewrite app_nil_r. unfold vRES.
      apply SPA_refacts; [exact HSPA | |].
      * cbn [ax_S ax_setS ss_next S_after]. rewrite forallb_app.
        assert (X : (Pos.succ N18 <? Pos.succ (Pos.succ N18))%positive = true) by (apply Pos.ltb_lt; lia).
        apply andb_true_intro. split; [unfold F20f; cbn; rewrite !X; reflexivity|].
        destruct HSPA as [[[W _] _] _]. cbn [ax_S ax_setS] in W. exact (swf_facts _ W).
      * intros HF. apply Forall_app. split; [|exact HF].
        unfold F20f, vRES. cbn [ax_S ax_setS ss_next S_after].
        assert (E1 : rw (rho20f rho a) (Pos.succ N18) = a) by (unfold rho20f; apply rho_set_rw_at).
        repeat apply Forall_cons; try apply Forall_nil; cbn [holds eval]; rewrite ?E1.
        -- change (2 ^ 12) with 4096. split; [lia|exact Pal].
        -- rewrite u64_of_lit by lia. rewrite Evm in Pceil. unfold TOP in TB. lia.
Qed.

Theorem node20f : ltac2:(tb__ "0|3|
S18S2fS10Q40M0A1M1A1S5S6S7bS8fA2SfG0S19R2PaA2A2A2S72S15Vok;S5eS15S6fVm;VB;A2M2Sa2R3R2A5S70S2S5eS15G2Sa5Sa2A1R4R3R1A6S4G1G1S1S93S11G0Z0A2Vm;S80R1A4S5eS15S6fS7eR1A1VB;A2Sa8S86R5R1A2R4R2A6A2La;A2A2Lw;A4F_;Ftp;Frho;").
Proof using OKF OKP Hres HB Htop Hband.
  clear Hsb Hal Hlo Hhi.
  intros rho tp HSP. pose proof E20f_at as (_ & Hecall & _).
  apply triple1_ecall_detA; [apply OKFx | apply stableA_KxA | exact Hecall | exact (node20f_core rho tp HSP)].
Qed.

Theorem enode20f_any : ltac2:(tb__ "0|3|
S18S2fS10Q40M0A1M1A1S5S6S7bS8fA2SfG0S19R2PaA2A2A2S73S15S5eS15S6fVm;VB;A2M2Sa2R3R2A5S70S2S5eS15G2Sa5Sa2A1R4R3R1A6S4G1G1S1S93S11G0Z0A2Vm;S80R1A4S5eS15S6fS7eR1A1VB;A2Sa8S86R5R1A2R4R2A6A2La;A2A2Lw;A3F_;Ftp;Frho;").
Proof using OKF OKP Hres HB Htop Hband.
  clear Hsb Hal Hlo Hhi.
  intros rho tp HSP. pose proof E20f_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & R13 & R14 & R15 & Hnx).
  apply etriple_ecall_detA; [apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp HK. destruct (node20f_core rho tp HSP tr ms md Hsp HK) as [_ HQ]. pose proof HK as (Htr & _ & _). subst tr.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  destruct (regs_of_pending rho tp E20f [] ms md Hsp) as (G0 & G1 & G2 & G3 & G4 & G5 & Hp).
  rewrite R17 in Hp. rewrite R11 in G1. rewrite R12 in G2. rewrite R13 in G3. rewrite R15 in G5. cbn [eval] in Hp, G1, G2, G3, G5.
  assert (H222 : bv_unsigned (Z_to_bv 64 222) = 222%Z) by reflexivity.
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0) by (rewrite G1; discriminate).
  destruct (mmap_noaccess_b_intro (ms_gpr ms 2) (ms_gpr ms 3) (ms_gpr ms 5)) as [Hsh Hnrw].
  { rewrite G2. reflexivity. } { rewrite G3. reflexivity. } { rewrite G5. reflexivity. }
  destruct (mmap_reserve_refusable md (mmap_nZ (ms_gpr ms 1))) eqn:Hrf.
  - pose proof (wstep_mmap_none_intro_failA segsA ms md _ Hh H222 Hlen Hsh Hnrw [] Hp Hrf) as W. exists (([] : list event), mkCfg (after_sys ms (errno_ret ENOMEM)) md). exact (conj W (HQ _ W)).
  - destruct (@mmap_none_not_refusable_place (sys_input segsA ms (Z_to_bv 64 222)) md Hrf) as [a Hpl].
    change (mmap_place_ok_none (ms_gpr ms 0) md (ms_gpr ms 1) a) in Hpl.
    pose proof (wstep_mmap_none_intro_okA segsA ms md _ Hh H222 Hlen Hsh Hnrw [] a Hp Hpl) as W. eexists. exact (conj W (HQ _ W)).
Qed.

Hypothesis Hlz : ltac2:(tb__ "0|3|
S31S10Q40M0A1M1G1A2M2S69G2R1S56Vm;A1A3S7Z0SfG0S39G1G1R2A3A2A2F_;Fr;").
Hypothesis Hlim : lazy_in_maps m.

Definition a4 (a : word) : word := Z_to_bv 64 (bv_unsigned a + 4096).
Definition mf_exp (a : word) : Model := ltac2:(tb__ "0|0|
Sc3S7eVa;A1S8bVa;A1S82A3").

Lemma objs_clear_E21f : ltac2:(tb__ "0|0|
S0S32SbdS34S31S16S13A2A1S62Sa3A1A2S33A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma facts_M_in_E21f : ltac2:(tb__ "0|0|
S17S69S17R1S90A3S69S17R2S1cS62Sa3A1A1A3F_;Ff;").
Proof. intros f Hf. vm_compute in Hf. vm_compute. tauto. Qed.
Lemma mf_res_vmmaps : ltac2:(tb__ "0|0|
S10Q40A1S0S4dS40S7eR1A1A1S99S40Vm;A1S80R1A3A3Fa;").
Proof. intros a. unfold mf_res. apply m_vmmaps_with_vmmaps. Qed.

Lemma node21f_core : ltac2:(tb__ "0|3|
S18S2fS10Q40M0A1M1A1G1S0G1S19R3SbcSa4A1A2R1A3S5S6S7bS8fA2SfG0S19R4PaA2A2A2S93S11G0Z0A2Vm;S80R3A4Sd4Vm;R5A2S2fS41A1M2S76S44Sc6S15RaR9Sa3S30G2S6bR3S6cR2R1A2A4A5S6fS7eR9A1VB;RbRaR4R2A6S1Vok;S30G2S6bR5S6cR4R3A2A4A1S70S71S15S30G2S6bR6S6cR5R4A2A4R1A3S70S2S5eS15S6fS7eRdA1VB;A2Sa5Sa3A1RfReR1A6S5eS15S6fS83RdA1S6VB;Z1000A2A2SaaRfReR1A6A2Lw;R2A1F_;Fw';A2F_;F_;Fmd;Fms;Ftr;F_;F_;F_;F_;Fa;Ftp;Frho;").
Proof using OKF OKP Hres HB Htop Hband Hlz Hlim.
  clear Hsb Hal Hlo Hhi.
  intros rho tp a Ha HSP Hpl Htp. pose proof E21f_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & Hnx).
  pose proof TOP_bounds as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi, TOP in TB.
  assert (Un8 : bv_unsigned n8w = 8192) by reflexivity. assert (Upg : bv_unsigned pgw = 4096) by reflexivity.
  assert (HnZ8 : mmap_nZ n8w = 8192) by reflexivity. assert (Hn8 : mmap_n n8w = n8w) by reflexivity.
  assert (HnZ : mmap_nZ pgw = 4096) by reflexivity. assert (Hn : mmap_n pgw = pgw) by reflexivity.
  pose proof Hpl as (Pal & Ppos & Pceil & Pfree). rewrite HnZ8 in Pceil. rewrite Hn8 in Pfree.
  pose proof (grant_facts_none_A (Z_to_bv 64 0) m n8w a Hpl Hres) as [Himg Hmaps]. rewrite HnZ8 in Himg, Hmaps.
  pose proof (band_clear_of_free _ a n8w Hband Pfree ltac:(rewrite Un8; lia)) as HBD. rewrite Un8 in HBD.
  assert (Ua4 : bv_unsigned (a4 a) = bv_unsigned a + 4096) by (unfold a4; apply u64_of_lit; pose proof (urange a); lia).
  intros tr ms md Hsp HK. pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md (mf_res a) Hem) as (Evm & Elz & _ & _). rewrite mf_res_vmmaps in Evm.
  unfold mf_res in Elz. rewrite m_vm_lazy_with_vmmaps in Elz.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  pose proof (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) as HMI.
  destruct (regs_of_pending rho tp E21f [] ms md Hsp) as (G0 & G1 & G2 & _ & _ & _ & Hp).
  rewrite R17 in Hp. rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2.
  cbn [eval] in Hp, G0, G1, G2. unfold vRES in G0. cbn [eval] in G0. rewrite Ha in G0. change (Z_to_bv 64 4096) with pgw in G1.
  assert (Ea4 : ms_gpr ms 0 = a4 a).
  { rewrite G0. apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, (u64_of_lit 4096), Ua4 by lia. apply bv_wrap_small.
    change (bv_modulus 64) with (2 ^ 64). pose proof (urange a). lia. }
  assert (H226 : bv_unsigned (Z_to_bv 64 226) = 226%Z) by reflexivity.
  assert (Hprot : bv_unsigned (ms_gpr ms 2) = 3) by (rewrite G2; reflexivity).
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0) by (rewrite G1; discriminate).
  assert (Halign : bv_unsigned (ms_gpr ms 0) mod page_size = 0).
  { rewrite Ea4, Ua4. unfold page_size in *. replace (bv_unsigned a + 4096) with (bv_unsigned a + 1 * 4096) by lia. rewrite Z_mod_plus_full. exact Pal. }
  assert (Hwrap : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) < two_pow_64) by (rewrite Ea4, Ua4, G1, HnZ; unfold two_pow_64 in *; lia).
  assert (Hna : map_contains (vm_noaccess (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite Ea4, G1, Hn, Evm. unfold mmap_none_vm. rewrite Hn8. cbn [vm_noaccess]. unfold map_contains. cbn [existsb fst snd].
    rewrite Ua4, Un8, Upg. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  assert (Hmp : map_contains (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite Ea4, G1, Hn, Evm. unfold mmap_none_vm. rewrite Hn8. cbn [vm_maps]. unfold map_contains. cbn [existsb fst snd].
    rewrite Ua4, Un8, Upg. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  split.
  - eapply (OKPx (mf_res a) B); [exact HK | exact Hp | exact (mprotect_expose_only_okA segsA ms md _ H226 Hprot Halign Hlen Hwrap Hna Hmp)].
  - intros w' Hw.
    destruct (wstep_mprotect_expose_invA segsA ms md _ Hh H226 Hprot Halign Hlen Hwrap Hna Hmp [] w' Hp Hw) as [-> | ->].
    + left. split; [|cbn [w_tr w_cfg fst snd cfg_model]; exact HK].
      unfold refuse, enomem_ret. eapply smatchA_after_ret_lit; [exact Hsp | exact Hh | apply vm_same_refl].
    + right. rewrite Ea4, G1, Hn.
      pose proof (xshadow_clear_of_disj rho E21f (a4 a) 4096 SHADOW_BAND_LO (SHADOW_BAND_HI - SHADOW_BAND_LO) eq_refl eq_refl
                    (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) facts_M_in_E21f
                    ltac:(unfold SHADOW_BAND_LO; lia) ltac:(unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia) ltac:(intros x Hx; apply HBD; rewrite Ua4 in Hx; lia)) as [HXb _].

      set (h' := m_vmmaps (mprotect_model_next md (a4 a) pgw)).
      assert (Eh' : h' = mkVmMapsFull (vm_reserved (m_vmmaps md)) (vm_maps (m_vmmaps md))
                           (maps_subtract (vm_noaccess (m_vmmaps md)) (bv_unsigned (a4 a)) (bv_unsigned (a4 a) + bv_unsigned pgw))
                           (vm_start_brk (m_vmmaps md)) (vm_brk (m_vmmaps md)) (vm_limit (m_vmmaps md)) (vm_mmap_base (m_vmmaps md)) (vm_init_sp (m_vmmaps md))).
      { unfold h', mprotect_model_next. rewrite m_vmmaps_with_vmmaps. reflexivity. }
      assert (Emodel : mprotect_model_next md (a4 a) pgw = with_vmmaps h' md).
      { unfold h', mprotect_model_next. rewrite m_vmmaps_with_vmmaps. reflexivity. }
      assert (Hforget : vm_forget_range (bv_unsigned (a4 a)) (bv_unsigned (a4 a) + bv_unsigned pgw) (with_vmmaps h' md) = with_vmmaps h' md).
      { apply vm_forget_range_noop.
        - rewrite Upg. lia.
        - rewrite m_vm_lazy_with_vmmaps, Elz. intros r Hr. split; [exact (Hlz r Hr)|].
          destruct r as [lb ls]. cbn [fst snd]. pose proof (Hlz _ Hr) as Hpos. cbn [snd] in Hpos.
          destruct (Hlim lb ls Hr Hpos) as (b & s0 & Hbin & Hb1 & Hb2).
          pose proof (Hmaps b s0 Hbin) as D. rewrite Ua4, Upg.

          destruct (Z.le_gt_cases (bv_unsigned lb + bv_unsigned ls) (bv_unsigned a + 4096)) as [L|L]; [left; exact L|].
          destruct (Z.le_gt_cases (bv_unsigned a + 4096 + 4096) (bv_unsigned lb)) as [R|R]; [right; exact R|].
          exfalso. pose proof (urange ls).
          destruct (Z.le_gt_cases (bv_unsigned lb) (bv_unsigned a + 4096)) as [C|C].
          * apply (D (bv_unsigned a + 4096)); lia.
          * apply (D (bv_unsigned lb)); lia.
        - rewrite m_vm_materialized_with_vmmaps. intros p Hpm Hin.
          pose proof HMI as (_ & _ & _ & Hsub & _). pose proof (Hsub p Hpm) as Htp_p.
          destruct (Htp p Htp_p) as (_ & b & s0 & Hbin & Hb1 & Hb2). rewrite Ua4, Upg in Hin.
          apply (Hmaps b s0 Hbin (bv_unsigned p)); unfold page_size in *; lia. }
      assert (HOV : overlap_sum (vm_maps (m_vmmaps md)) (bv_unsigned (a4 a)) (bv_unsigned (a4 a) + bv_unsigned pgw) <= bv_unsigned pgw).
      { rewrite Evm. unfold mmap_none_vm. rewrite Hn8. cbn [vm_maps].
        match goal with |- overlap_sum (?r :: ?rest) _ _ <= _ => change (r :: rest) with ([] ++ r :: rest) end.
        apply overlap_sum_split_le. cbn [app]. apply (region_free_shrink _ a n8w); [exact (region_free_app_r _ _ _ _ Pfree) | rewrite Ua4; lia | rewrite Ua4, Upg, Un8; lia]. }
      rewrite Emodel, <- Hforget.
      assert (Hsm1 : smatchA segsA rho tp (ax_setS E21f (S_after (ax_S E21f) (SLit 0) (ss_objs (ax_S E21f) ++ [mkObj (SAlu ALU_ADD vRES (SLit 4096)) (SLit 0) (SLit (bv_unsigned pgw)) [] DZero]) (ss_next (ax_S E21f))))
                       ([], mkCfg (after_sys_mem ms (Z_to_bv 64 0) (zero_range (ms_mem ms) (a4 a) pgw))
                                  (vm_forget_range (bv_unsigned (a4 a)) (bv_unsigned (a4 a) + bv_unsigned pgw) (with_vmmaps h' md)))).
      { eapply (smatchA_after_commit_obj segsA rho rho tp E21f [] ms md [] h' (a4 a) pgw (Z_to_bv 64 0) (SLit 0) (SAlu ALU_ADD vRES (SLit 4096)) (ss_next (ax_S E21f)) Hsp).
        -- rewrite Eh'. reflexivity.
        -- rewrite Eh'. reflexivity.
        -- rewrite Eh'. reflexivity.
        -- exact Halign || (rewrite <- Ea4; exact Halign).
        -- rewrite Upg. reflexivity.
        -- rewrite Upg. lia.
        -- rewrite Ua4, Upg. unfold two_pow_64 in *. lia.
        -- exact HOV.
        -- unfold headroom. rewrite Evm, Upg. unfold mmap_none_vm. cbn [vm_limit]. lia.
        -- intros x Hx. apply (grant_no_ro_A (a4 a) 4096); [| rewrite Upg in Hx; exact Hx]. intros z Hz. apply Himg. rewrite Ua4 in Hz. lia.
        -- rewrite Upg. intros o Ho.
           apply (objs_clear_M_sound rho [] (ax_S E21f) (a4 a) 4096 TOP (smatch_pending_facts segsA _ _ _ _ _ (smatch_pendingA_sp segsA _ _ _ _ _ _ Hsp)) objs_clear_E21f);
             [lia | unfold TOP; rewrite Ua4; lia | exact HSP | intros x Hx; apply Himg; rewrite Ua4 in Hx; lia | intros e sz [] | exact Ho].
        -- rewrite Upg. exact HXb.
        -- apply agree_below_refl.
        -- apply Pos.le_refl.
        -- reflexivity.
        -- reflexivity.
        -- rewrite Hnx. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc.
        -- unfold vRES. cbn [eval]. rewrite Ha. symmetry. rewrite <- Ea4. exact G0. }
      split.
      * unfold S21f, cont. rewrite Hforget.
        replace (ax_setS E21f (add_facts [] (S_after (ax_S E21f) (SLit 0) (ss_objs (ax_S E21f) ++ [O_area_f]) (Pos.succ (Pos.succ N18)))))
          with (ax_setS E21f (S_after (ax_S E21f) (SLit 0) (ss_objs (ax_S E21f) ++ [mkObj (SAlu ALU_ADD vRES (SLit 4096)) (SLit 0) (SLit (bv_unsigned pgw)) [] DZero]) (ss_next (ax_S E21f))));
          [rewrite <- Hforget; exact Hsm1|].
        rewrite Hnx, Upg. reflexivity.
      * cbn [cfg_model w_cfg w_tr fst snd]. rewrite Hforget. split; [reflexivity|]. split.
        -- unfold mf_exp. rewrite (Emodel) || idtac.
           unfold mprotect_model_next. unfold h'. unfold mprotect_model_next. rewrite !m_vmmaps_with_vmmaps.
           rewrite mf_res_vmmaps, <- Evm. apply erase_mat_cong_vmmaps. exact Hem.
        -- rewrite paid_with_vmmaps.
           pose proof (MI_ivs_wf segsA _ _ HMI) as Hivs.
           pose proof (used_commit_le md h' (a4 a) pgw Hivs ltac:(rewrite Eh'; reflexivity) ltac:(rewrite Eh'; reflexivity)) as UC.
           rewrite Hforget in UC. rewrite Upg in UC, HOV. lia.
Qed.

Theorem node21f : ltac2:(tb__ "0|2|
S18S2fS10Q40M0A1M1A1G1S0G1S19R3SbcSa4A1A2R1A3S5S6S7bS8fA2SfG0S19R4PaA2A2A2S93S11G0Z0A2Vm;S80R3A4Sd4Vm;R5A2S72S15Vok;S5eS15S6fS7eR5A1VB;A2Sa3R7R6A5S70S2S5eS15S6fS7eR6A1VB;A2Sa5Sa3A1R8R7R1A6S5eS15S6fS83R6A1S6VB;Z1000A2A2SaaR8R7R1A6A2Lw;A4F_;F_;F_;F_;Fa;Ftp;Frho;").
Proof using OKF OKP Hres HB Htop Hband Hlz Hlim.
  clear Hsb Hal Hlo Hhi.
  intros rho tp a Ha HSP Hpl Htp. pose proof E21f_at as (_ & Hecall & _).
  apply triple1_ecall_detA; [apply OKFx | apply stableA_KxA | exact Hecall | exact (node21f_core rho tp a Ha HSP Hpl Htp)].
Qed.

Theorem enode21f_any : ltac2:(tb__ "0|2|
S18S2fS10Q40M0A1M1A1G1S0G1S19R3SbcSa4A1A2R1A3S5S6S7bS8fA2SfG0S19R4PaA2A2A2S93S11G0Z0A2Vm;S80R3A4Sd4Vm;R5A2S73S15S5eS15S6fS7eR5A1VB;A2Sa3R7R6A5S70S2S5eS15S6fS7eR6A1VB;A2Sa5Sa3A1R8R7R1A6S5eS15S6fS83R6A1S6VB;Z1000A2A2SaaR8R7R1A6A2Lw;A3F_;F_;F_;F_;Fa;Ftp;Frho;").
Proof using OKF OKP Hres HB Htop Hband Hlz Hlim.
  clear Hsb Hal Hlo Hhi.
  intros rho tp a Ha HSP Hpl Htp. pose proof E21f_at as (Hpc & Hecall & R17 & R10 & R11 & R12 & Hnx).
  assert (Un8 : bv_unsigned n8w = 8192) by reflexivity. assert (Upg : bv_unsigned pgw = 4096) by reflexivity.
  assert (HnZ8 : mmap_nZ n8w = 8192) by reflexivity. assert (Hn8 : mmap_n n8w = n8w) by reflexivity.
  assert (HnZ : mmap_nZ pgw = 4096) by reflexivity. assert (Hn : mmap_n pgw = pgw) by reflexivity.
  pose proof TOP_bounds as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi, TOP in TB.
  pose proof Hpl as (Pal & Ppos & Pceil & Pfree). rewrite HnZ8 in Pceil. rewrite Hn8 in Pfree.
  assert (Ua4 : bv_unsigned (a4 a) = bv_unsigned a + 4096) by (unfold a4; apply u64_of_lit; pose proof (urange a); lia).
  apply etriple_ecall_detA; [apply stableA_KxA | exact Hecall |].
  intros tr ms md Hsp HK. destruct (node21f_core rho tp a Ha HSP Hpl Htp tr ms md Hsp HK) as [_ HQ].
  pose proof HK as (Htr & Hem & Hpaid). subst tr.
  pose proof (erase_mat_eq_fields md (mf_res a) Hem) as (Evm & _ & _ & _). rewrite mf_res_vmmaps in Evm.
  pose proof (smatch_pendingA_halted segsA _ _ _ _ _ _ Hsp) as Hh.
  destruct (regs_of_pending rho tp E21f [] ms md Hsp) as (G0 & G1 & G2 & _ & _ & _ & Hp).
  rewrite R17 in Hp. rewrite R10 in G0. rewrite R11 in G1. rewrite R12 in G2.
  cbn [eval] in Hp, G0, G1, G2. unfold vRES in G0. cbn [eval] in G0. rewrite Ha in G0. change (Z_to_bv 64 4096) with pgw in G1.
  assert (Ea4 : ms_gpr ms 0 = a4 a).
  { rewrite G0. apply bv_eq. unfold alu64, alu. rewrite bv_add_unsigned, (u64_of_lit 4096), Ua4 by lia. apply bv_wrap_small.
    change (bv_modulus 64) with (2 ^ 64). pose proof (urange a). lia. }
  assert (H226 : bv_unsigned (Z_to_bv 64 226) = 226%Z) by reflexivity.
  assert (Hprot : bv_unsigned (ms_gpr ms 2) = 3) by (rewrite G2; reflexivity).
  assert (Hlen : ms_gpr ms 1 <> Z_to_bv 64 0) by (rewrite G1; discriminate).
  assert (Halign : bv_unsigned (ms_gpr ms 0) mod page_size = 0).
  { rewrite Ea4, Ua4. unfold page_size in *. replace (bv_unsigned a + 4096) with (bv_unsigned a + 1 * 4096) by lia. rewrite Z_mod_plus_full. exact Pal. }
  assert (Hwrap : bv_unsigned (ms_gpr ms 0) + mmap_nZ (ms_gpr ms 1) < two_pow_64).
  { rewrite Ea4, Ua4, G1, HnZ; unfold two_pow_64 in *; lia. }
  assert (Hna : map_contains (vm_noaccess (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite Ea4, G1, Hn, Evm. unfold mmap_none_vm. rewrite Hn8. cbn [vm_noaccess]. unfold map_contains. cbn [existsb fst snd].
    rewrite Ua4, Un8, Upg. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  assert (Hmp : map_contains (vm_maps (m_vmmaps md)) (ms_gpr ms 0) (mmap_n (ms_gpr ms 1)) = true).
  { rewrite Ea4, G1, Hn, Evm. unfold mmap_none_vm. rewrite Hn8. cbn [vm_maps]. unfold map_contains. cbn [existsb fst snd].
    rewrite Ua4, Un8, Upg. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  destruct (mprotect_budget_ok md (ms_gpr ms 0) (mmap_n (ms_gpr ms 1))) eqn:Hb.
  - pose proof (wstep_mprotect_expose_intro_okA segsA ms md _ Hh H226 Hprot Halign Hlen Hwrap Hna Hmp [] Hp Hb) as W. eexists. exact (conj W (HQ _ W)).
  - pose proof (wstep_mprotect_expose_intro_failA segsA ms md _ Hh H226 Hprot Halign Hlen Hwrap Hna Hmp [] Hp Hb) as W. eexists. exact (conj W (HQ _ W)).
Qed.

Lemma xwordsZ_clear_of_disj : ltac2:(tb__ "0|5|
S18S64S13S13S13S13S0S2fS31S16S16A2M0A1S65R5A1S91A3S0S16S63R6A1S1bSd2A1A3S7aS17S1fR8A1S1cS62R7A1A1A3S17S69S17R1S90A3S69S17R2S1cS62RaA1A1A3F_;Ff;S5R6Z10006fdf0000A2S5Z10007fff8000S6R7R6A2A2S13S1S5RbR1A2S7R1RaA2A2S3S1S5RaR2A2S7R2S6RaR9A2A2A2A1F_;Fx;G0S13S13S69G0R3S65RfA1A3S1S5SfQ40M1S1aR11S3aS16S16R4A3A2A2M2R3A2S7R3S6G2SfG1S1aR11S39S16S16R4A3A2A2A2A2A2S1S5Z0R3A2S7R3Z8M3A2A2S3S1S5R11S6SdS8S6SfG1S1aR13S63R12A1A2A2S8R5G3A2A2G3A2G3A2R4A2M4A2S7G4R10A2A2A1F_;F_;F_;Fj;Fy;Frr;F_;F_;F_;F_;F_;F_;F_;FsZ;FbZ;Fhi;Flo;FA;Frho;").
Proof.
  clear. intros rho A lo hi bZ sZ HX Hb HF Hin Hb1 Hb2 Hdisj. rewrite HX, Hb.
  assert (F1 : holds rho (SPUle (SLit 0x7fff7f000000) vXB)) by (apply (proj1 (Forall_forall _ _) HF); apply Hin; unfold facts_M; cbn [In]; tauto).
  assert (F2 : holds rho (SPUle (SAlu ALU_ADD vXB vXL) (SLit (2 ^ 47)))) by (apply (proj1 (Forall_forall _ _) HF); apply Hin; unfold facts_M; cbn [In]; tauto).
  assert (F3 : holds rho (SPUle vXL (SLit (2 ^ 40)))) by (apply (proj1 (Forall_forall _ _) HF); apply Hin; unfold facts_M; cbn [In]; tauto).
  assert (F4 : holds rho (SPUle vXB (SLit (2 ^ 48)))) by (apply (proj1 (Forall_forall _ _) HF); apply Hin; unfold facts_M; cbn [In]; tauto).
  cbn [holds eval] in F1, F2, F3, F4. unfold vXB, vXL in F1, F2, F3, F4. cbn [eval] in F1, F2, F3, F4.
  rewrite (u64_of_lit 0x7fff7f000000) in F1 by lia. rewrite (u64_of_lit (2 ^ 47)) in F2 by lia.
  rewrite (u64_of_lit (2 ^ 40)) in F3 by lia. rewrite (u64_of_lit (2 ^ 48)) in F4 by lia.
  unfold alu64, alu in F2. rewrite bv_add_unsigned in F2.
  rewrite bv_wrap_small in F2 by (change (bv_modulus 64) with (2 ^ 64); pose proof (urange (rw rho 52)); pose proof (urange (rw rho 53)); lia).
  cbn [eval]. unfold SHB. rewrite (u64_of_lit 0x7fff8000) by lia.
  intros rr y j [<-|[]] Hy Hj. cbn [fst snd] in Hy. unfold vXB, vXL in Hy. cbn [eval] in Hy.
  assert (Hy8 : 0x7fff7f000000 / 8 <= y / 8 < 2 ^ 44) by (split; [apply Z.div_le_mono; lia | apply Z.div_lt_upper_bound; lia]).
  change (0x7fff7f000000 / 8) with 17591915511808 in Hy8.
  pose proof (Z.div_mod (2147450880 + y / 8) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (2147450880 + y / 8) 8 ltac:(lia)) as M.
  assert ((2147450880 + y / 8) / 8 <= 17594333495295 / 8) by (apply Z.div_le_mono; lia).
  change (17594333495295 / 8) with 2199291686911 in H.
  intros Hc. apply (Hdisj ((2147450880 + y / 8) / 8 * 8 + j)); lia.
Qed.

Lemma objs_clear_U24 : ltac2:(tb__ "0|0|
S0S32SbdS34S31S16S13A2A1S62SabA1A2S33A3").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma facts_M_in_U24 : ltac2:(tb__ "0|0|
S17S69S17R1S90A3S69S17R2S1cS62SabA1A1A3F_;Ff;").
Proof. intros f Hf. vm_compute in Hf. vm_compute. tauto. Qed.

Theorem carve24 : ltac2:(tb__ "0|7|
S5fS18S2fS10Q40M0A1M1A1S70S0G1S19R3Sa4A2S7cA3S5S6S7dZ2000A2M2S7bA2S5S6S7bS8fA2SfG0S19R5PaA2A2A2S0S32S47S37S31G1G1A2S43S40Vm;A1M3A1S42G3A1A3S7cS85A3S33A3G1S1S5S6S7dZ1000A2SfG0R1A2M4A2S7G4G2A2A2S0S35S10Q8M5A1M6A1S20R9R2A2S36G6S11G5Z0A2A2A3F_;Fa;S5eS15R9SabR8R7R6A6S5eS15RaSb2R9R8R7A6F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;FJ;").
Proof using Hlo Hhi Htop Hband.
  clear Hres Hsb Hal HB Hlz Hlim.
  intros J rho tp [tr [ms md]] HN18 Hceil HSP Hfree3 Hz HS. pose proof TOP_bounds as TB. unfold alloc_ceiling_lo, alloc_ceiling_hi in TB.
  pose proof n3w_val as NV3.
  pose proof (band_clear_of_free _ brk0w n3w Hband Hfree3 ltac:(rewrite NV3; lia)) as HBD. rewrite NV3 in HBD.
  pose proof (SPA_facts_hold segsA J rho U24 tp _ HS) as HF.
  unfold U24c.
  apply (SPA_carve_zero segsA J rho U24 tp tr ms md (SAlu ALU_ADD vBRK (SLit 4096)) 0 4096 (ss_next (ax_S U24)) HS);
    unfold vBRK; cbn [eval]; rewrite ?HN18; unfold alu64, alu; rewrite ?bv_add_unsigned, ?(u64_of_lit 4096) by lia;
    rewrite ?bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); unfold brk0 in *; lia).
  - exact (proj1 U24c_wf).
  - apply Pos.le_refl.
  - lia. - lia. - lia.
  - unfold brk0 in *; lia.
  - unfold brk0 in *; lia.
  - apply Forall_forall. intros o Ho.
    replace (bv_unsigned brk0w + 4096 + 0) with (bv_unsigned (a4 brk0w)) by (unfold a4; rewrite u64_of_lit; unfold brk0 in *; lia).
    replace (bv_unsigned brk0w + 4096 + 4096) with (bv_unsigned (a4 brk0w) + 4096) by (unfold a4; rewrite u64_of_lit; unfold brk0 in *; lia).
    apply (objs_clear_M_sound rho [] (ax_S U24) (a4 brk0w) 4096 TOP HF objs_clear_U24); [lia | | exact HSP | | intros e sz [] | exact Ho];
      unfold a4; rewrite u64_of_lit by (unfold brk0 in *; lia); unfold brk0 in *; [lia|]. intros x Hx. lia.
  - intros z Hzr. apply Hz. rewrite u64_of_lit by (unfold brk0 in *; lia). unfold brk0. lia.
  - apply (xwordsZ_clear_of_disj rho U24 _ _ SHADOW_BAND_LO (SHADOW_BAND_HI - SHADOW_BAND_LO) eq_refl eq_refl HF facts_M_in_U24);
      [unfold SHADOW_BAND_LO; lia | unfold SHADOW_BAND_LO, SHADOW_BAND_HI; lia |].
    intros x Hx. apply HBD. unfold brk0 in *. lia.
Qed.

End Malloc40.
End MuslMalloc40Nodes.

