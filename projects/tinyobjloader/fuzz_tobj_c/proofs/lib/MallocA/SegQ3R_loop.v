(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "qbatch"; "aa_q_global"; "qb_addr"; "qb_size"; "aa_geom"; "topG"; "AA"; "ag_thread"; "ageom"; "@Corelib.Init.Datatypes"; "cons"; "list"; "pair"; "nil"; "app"; "bool"; "true"; "nat"; "prod"; "option"; "length"; "Some"; "None"; "fst"; "snd"; "@Corelib.Init.Logic"; "eq"; "and"; "not"; "ex"; "or"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sobj"; "rw"; "sprop"; "rm"; "SLit"; "SVar"; "ss_facts"; "ss_objs"; "obj_range"; "eval"; "swf"; "cell"; "holds"; "ss_next"; "DUnknown"; "mkObj"; "sprop_below"; "ranges_disjoint"; "rl"; "SAlu"; "SPBranch"; "SPNot"; "mkSS"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_pc"; "ss_regs"; "ss_resv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "pow"; "of_nat"; "sub"; "opp"; "mul"; "modulo"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "ax_base"; "ax_X"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "qsize"; "qb_dflt"; "qhdr_repr"; "qlinks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop.Loop"; "HVH"; "HVC"; "benv"; "HVT"; "JRX"; "@Stdlib.Lists.List"; "In"; "forallb"; "last"; "hd"; "removelast"; "tl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel"; "JRQ"; "FRM"; "HVP"; "RMEM"; "tlinks"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "cell_ok"; "mkACell"; "view"; "bview"; "present"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep"; "last_addr"; "hd_addr"; "bfoot"; "ifoot"; "qlinks_to"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop"; "with_obj"; "O_bh"; "Ck0"; "HVX"; "C0b"; "Ckb"; "XSEL"; "E0x"; "Ekx"; "F_newk"; "RMEM2"; "fixed_ok"; "C0a"; "C0c"; "Cka"; "Ckc"; "M0g"; "MX0"; "MXk"; "Mkg"; "@Corelib.Lists.ListDef"; "Forall"; "firstn"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states"; "vCSZ"; "vCUR"; "Headk"; "Xg"; "PH"; "ZQ"; "Cont0"; "Contk"; "Exit0"; "Exitk"; "Head0"; "O_cur"; "vK"; "F_go"; "F_nz"; "O_gqC"; "O_prv"; "STK"; "s'"; "vCN"; "vLB"; "vN"; "vPSZ"; "FRlo"; "O_cbD"; "PM"; "WLOW"; "vJK"; "vJL"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states"; "add"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "kQuarantineMin"; "HIGH_SHADOW_END"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "kQuarantineMax"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr"; "TR"; "JOK"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM"; "entsM"; "keepsM"; "vmap"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all"; "sv_vars_all"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue"; "notin_vars"; "rho_sets"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states"; "vMIN"; "DEPTH_R"; "QG"; "O_gmax"; "O_gq";
"O_mtx"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2"; "QW"; "batch_mem"; "QRD"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "snorm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.GlueA"; "ax_with_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "apply_axforms"; "axform"; "AXSelect"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "pre_facts"; "A_globals"; "V_DEPTH"; "top_high"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states"; "F_new"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_SUB"; "BC_EQ"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "in_ranges"; "rho_absorb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.Glue"; "carved"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM"; "M0"; "Mk"; "PreR2"; "idm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs"; "qall"; "qitems"; "@stdpp.base"; "NoDup"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma signed_neg_unsigned : ltac2:(tb__ "0|1|
S4eQ40M0A1S1dS18S1dS50G0R2A2R1A3S40R2Z0A2S18S1dS4fG0R4A2S3fR3S41Z2Z40A2A2A3F_;F_;FD;Fx;").
Proof.
  intros x D E HD. pose proof (urange x) as R. rewrite <- E in *. clear E.
  change (bv_signed x) with (soff (mkVal (fun _ => x) (fun _ => []) (fun _ => None)) (SVar 1)) in *. rewrite soff_snorm in *.
  unfold U in *. cbn [eval rw] in *. unfold snorm in *. rewrite (Z.mod_small _ _ R) in *. destruct (bv_unsigned x <? 2 ^ 63) eqn:E; [lia | lia].
Qed.
Lemma signed_of_unsigned : ltac2:(tb__ "0|1|
S4eQ40M0A1S18S1dS50G0R1A2Sc4S4fG0R1A2A1A3Fx;").
Proof. intros x. change (bv_signed x) with (soff (mkVal (fun _ => x) (fun _ => []) (fun _ => None)) (SVar 1)). rewrite soff_snorm. reflexivity. Qed.

Lemma stk_facts : ltac2:(tb__ "0|2|
S6S20SccR2R1A2S88S23S2dR2A1Sc9Sb9A1A3S4fQ40M0S22R3PaA2A2S1dS50G0S22R4ScbA2A2S1dS19S19S3eS44S41Z2M1Z28A2A1R1A2S3eR1N600A2A2S19S3eS5S4R6A1A1S3fR2R1A2A2S40R2S41G1Z40A2A2A2A2TD;Tsp;F_;F_;Frho;FA;").
Proof.
  intros A rho HT HF sp D. unfold pre_facts, F_depth, DEPTH_R in HF. cbn [app] in HF.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HF))) as F1. pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail HF)))) as F2.
  cbn [holds branch_taken eval] in F1, F2. apply negb_true_iff in F1, F2. unfold bv_lts in F1, F2. apply Z.ltb_ge in F1, F2.
  rewrite signed_lit in F1, F2. match type of F1 with _ <= ?x => let y := eval vm_compute in x in change x with y in F1 end.
  match type of F2 with ?x <= _ => let y := eval vm_compute in x in change x with y in F2 end.
  unfold top_high in HT. fold sp D in HT. pose proof (urange (rw rho 10%positive)) as R. fold sp in R. fold D in F1, F2. lia.
Qed.

Lemma stk_ranges : ltac2:(tb__ "0|8|
S20S1dS1dSaS2cA1M0G0S18S1dS4fQ40M1S22R5PaM2A2A2R4A3S18S1dS50G1S22R6ScbA2A2R4A3S3eS41Z2M3Z29A2R6A2S19S3eS44S41G3Z28A2A1R6A2S3eR6N600A2A2S19S18S11S1dS1dA2M4S29R9Sa5A2SbS1dS1dS3fR8R7A2S43R8Zc0A2M5A4A3S19S18G4S29R9Sa2A2SbS1dS1dG5S43R8Zb8A2M6A4A3S19S18G4S29R9Sa3R6A1A2SbS1dS1dG6S43R8Za8A2M7A4A3S18G4S29R9S30S26G2A1S25Na8A1S25Z0A1R5S2fA5A2SbS1dS1dG7R8A4A3A2A2A2F_;F_;F_;F_;Fswc;Fcb;FD;Fsp;Frho;").
Proof.
  intros rho sp D cb swc E10 E15 Hsp HD. pose proof (urange (rw rho 10%positive)) as R10. rewrite E10 in R10.
  pose proof (signed_neg_unsigned _ D E15 ltac:(lia)) as U15.
  assert (ESPD : forall k, - 4096 <= k < 0 -> bv_unsigned (eval rho (add (SVar 10) (SLit k))) = sp + k).
  { intros k Hk. unfold add. cbn [eval]. rewrite add_val, E10. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    replace (k mod 2 ^ 64) with (2 ^ 64 + k) by (apply Z.mod_unique with (q := -1); lia).
    replace (sp + (2 ^ 64 + k)) with ((sp + k) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  split; [|split; [|split]].
  - unfold WLOW, spD, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi]. rewrite (ESPD (-192)) by lia. rewrite soff_lit. change (snorm 0) with 0.
    unfold soff, add. cbn [eval]. rewrite signed_of_unsigned, add_val, U15, u64_lit by lia.
    replace ((D + 2 ^ 64 + 192) mod 2 ^ 64) with (D + 192 + 2 ^ 64) by (symmetry; replace (D + 2 ^ 64 + 192) with ((D + 192 + 2 ^ 64) + 0 * 2 ^ 64) by lia; rewrite Z.mod_add by lia; apply Z.mod_small; lia).
    unfold snorm. rewrite Z.mod_small by lia. destruct (D + 192 + 2 ^ 64 <? 2 ^ 63) eqn:E; [apply Z.ltb_lt in E; lia|]. f_equal; lia.
  - unfold FRlo. rewrite obj_range_mk by lia. cbn [eval]. rewrite E10. f_equal; lia.
  - unfold O_cbD. rewrite obj_range_mk by lia. rewrite (ESPD (-184)) by lia. f_equal; lia.
  - rewrite obj_range_mk by lia. cbn [eval]. rewrite E10. f_equal; lia.
Qed.

Definition fixed_ok (rho : valuation) (T : Z) (o : sobj) : Prop := ltac2:(tb__ "0|1|
S1cS3eS17S1dS1dS29Vrho;Vo;A2M0A3Z646000A2S3eVT;S16S1dS1dG0A3A2A2").
Lemma fixed_clear : ltac2:(tb__ "0|0|
S20S1dS21S1dS1dS7fR5R4R3A3S3eZ646000R3A2S3eR3R6A2S32S29R8R6A2SbS1dS1dR5R4A4A2F_;F_;F_;Fhi;Flo;Fo;FT;Frho;").
Proof. intros rho T o lo hi [H|H] H1 H2; unfold ranges_disjoint; cbn [fst snd]; lia. Qed.

Lemma OH_fixed : ltac2:(tb__ "0|2|
S6S20SaS2cA1M0G0S1fS1fS1fS1fS1fSccR9R8A2S88S23S2dR9A1Sc9Sb9A1A3S88S21S7fRaS5S4RbA1A1A2SdS21SdS21S9cR9S30S26PaA1S25Na8A1S25Z0A1R8S2fA5A2S9S21SbdR7A1S9S21SbbScS21A1M1A3A3A3SdS21ScaS9S21SbcR6R5R4R3A4G1A3A3A3A3F_;F_;Fg4;Fg3;Fg2;Fg1;Fw;Fswc;Fcb;Frho;FA;").
Proof.
  intros A rho cb swc w g1 g2 g3 g4 HT HF. destruct (stk_facts A rho HT HF) as (HD & HTOP & Hsp). pose proof (topG_range (aa_geom A)) as TG.
  destruct (stk_ranges rho _ _ cb swc eq_refl eq_refl ltac:(lia) HD) as (R1 & R2 & R3 & R4).
  unfold STK. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; unfold fixed_ok.
  - right. rewrite R1. cbn [fst]. lia.
  - right. rewrite R2. cbn [fst]. lia.
  - right. rewrite R3. cbn [fst]. lia.
  - right. rewrite R4. cbn [fst]. lia.
  - left. unfold O_mtx, carved. rewrite obj_range_mk by (unfold QG; lia). cbn [snd eval]. rewrite u64_lit by lia. unfold QG. lia.
  - left. unfold O_gmax, carved. rewrite obj_range_mk by (unfold QG; lia). cbn [snd eval]. rewrite u64_lit by lia. unfold QG. lia.
  - left. unfold O_got. rewrite obj_range_mk by (unfold GOT_LO, GOT_HI; lia). cbn [snd eval]. rewrite u64_lit by lia. unfold GOT_HI. lia.
  - left. unfold O_rtc. rewrite obj_range_mk by (unfold RTC_LO, RTC_HI; lia). cbn [snd eval]. rewrite u64_lit by lia. unfold RTC_HI. lia.
  - left. unfold O_gq, carved. rewrite obj_range_mk by (unfold QG; lia). cbn [snd eval]. rewrite u64_lit by lia. unfold QG. lia.
Qed.

Definition with_obj (S : sstate) (o : sobj) : sstate := ltac2:(tb__ "0|0|
S37S3bVS;A1S3cVS;A1S39VS;A1S38VS;A1S3dVS;A1SdS21S28VS;A1S9S21Vo;ScS21A1A3A3S27VS;A1S2eVS;A1S3aVS;A1A9").
Definition O_bh (vb vn vs : positive) : sobj := ltac2:(tb__ "0|4|
Sd3S26Vvb;A1Z0M0Z10S9S11S11S1dS10A2M1S1fA2M2SbG1S1fSbS1dS10G0U8M3A4S26Vvn;A1A4S9G2SbG1S1fSbS1dS10Z8G3A4S26Vvs;A1A4ScG2A1A3A3A4").

Lemma carve_bhdr : ltac2:(tb__ "0|6|
S56S49S20SaS4eQ40M0A1M1A1S72S1eS1eS1eS1dS1dS1dS55S47RbRaR9R8R7A6S18SaS11S1fS1fA2M2A1S4cRbA1ScG2A1A3S18SeS2bS74S48RcA1S75R8R7R6A3A2A1SfA3S18G1S22RcR9A2S4dG0R6A2M3A3S18G1S22RdR9A2G3A3S18G1S22ReR9A2G3A3S3eZ646000R9A2S3eS3fRaZ10M4A2S41Z2Z3eA2A2S68S6aS47S24R11A1A2S69RbU8M5RaA3A2S68S6aS47S24R12A1A2S69S3fRcZ8A2G5RaA3A2S88S21S21S32S29R14R1A2SbS1dS1dReS3fReG4A2A4A2Lo';S28S48R14A1A1A3S55S47R16S4aR15S74S48R15A1S75R11R10RfA3A2A2R14R13R12A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fsz;Fnxt;Fa;Fvs;Fvn;Fvb;Fw;Ftp;Frho;FS;FJ;").
Proof.
  intros J S rho tp w vb vn vs a nxt sz H HX Hswf Eb En Es Ha1 Ha2 Cn Cs HD.
  pose proof (SPA_carve_list segsA J rho S tp w [(SVar vb, 0, 16, [(0, 8%nat, SVar vn); (8, 8%nat, SVar vs)])] (ss_next (ax_S S)) H) as X.
  cbn zeta in X. cbn [map carve_obj] in X. apply X; clear X.
  - exact Hswf.
  - apply Pos.le_refl.
  - apply Forall_cons; [|apply Forall_nil]. cbn [eval]. rewrite Eb, u64_lit by lia.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
    split; [|split].
    + intros off Hoff. destruct (Z_lt_dec off 8).
      * eapply (cell_wok_rd _ _ _ _ _ Cn); cbn [Z.of_nat]; lia.
      * eapply (cell_wok_rd _ _ _ _ _ Cs); cbn [Z.of_nat]; lia.
    + unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
      * eapply (civ_cell rho (rm rho) a 0); [rewrite Z.add_0_r; exact Cn | cbn [eval]; exact En | lia | lia].
      * eapply (civ_cell rho (rm rho) a 8); [exact Cs | cbn [eval]; exact Es | lia | lia].
    + intros rr y j Hin. rewrite HX in Hin. destruct Hin.
  - apply Forall_cons; [|apply Forall_nil]. unfold O_bh, carved in *.
    assert (ER : forall cs, obj_range rho (mkObj (SVar vb) (SLit 0) (SLit 16) cs DUnknown) = (a, a + 16)).
    { intros cs. rewrite obj_range_mk by lia. cbn [eval]. rewrite Eb, u64_lit by lia. f_equal; lia. }
    rewrite ER. exact HD.
  - cbn [pairwise_disjoint]. split; [apply Forall_nil | exact I].
Qed.

Lemma PH_vars : ltac2:(tb__ "0|1|
S19S18SeSb4Sb6S9S1ePa4S9S1ePa5ScS1eA1A3A3A1M0S48S8fA1A2SfA3S18SeSb5G0S4bS8fA1A2SfA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma Head0_swf : ltac2:(tb__ "0|0|
S18SeS2bS74S48S8fA1S75Pa1Pa4Pa5A3A2A1SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Head0_eq : ltac2:(tb__ "0|0|
S18S49S4aS8fS74S48S8fA1S75Pa1Pa4Pa5A3A2A2S95A3"). Proof. reflexivity. Qed.

Definition C0a : axst := ltac2:(tb__ "0|1|
S4aS91SfA1M0S74S48G0A1S75Pa4Pc6Pc7A3A2A2").
Definition XSEL : list axform := ltac2:(tb__ "0|0|
S9Sc7Sc8S9S10U0S9S10U1S9S10U2S9S10U3S9S10U4S9S10U5S9S10U6S9S10U7S9S10U8S9S10UaS9S10U9ScS10A1A3A3A3A3A3A3A3A3A3A3A3A1ScSc7A1A3").
Definition C0b : axst := Eval vm_compute in (match apply_axforms C0a XSEL with Some X => X | None => C0a end).
Lemma C0b_eq : ltac2:(tb__ "0|0|
S18S12S49A1Sc6S80S7aA2S14S49S78A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition C0c : axst := ltac2:(tb__ "0|0|
Sc5S78SdS23S27S48S78A1A1ScdA3A2").
Definition M0g : vmap := ltac2:(tb__ "0|1|
S9S11S1eS1fA2M0SbS1eS1fPa0Sa8Sa0S25N1A1A2A4S9G0SbS1eS1fPa1S9eA4S9G0SbS1eS1fPa2S9fA4S9G0SbS1eS1fPa3S9dA4S9G0SbS1eS1fPa4S26Pc6A1A4S9G0SbS1eS1fPa5S26Pc7A1A4S9G0SbS1eS1fPa6S8cA4S9G0SbS1eS1fPa7S8bA4S9G0SbS1eS1fPa8S25Z1A1A4S9G0SbS1eS1fPa9S8cA4S9G0SbS1eS1fPaaS8bA4S9G0SbS1eS1fPc0S90A4S9G0SbS1eS1fPc1S90A4S9G0SbS1eS1fPd0Sb8A4ScG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma C0c_ent : ltac2:(tb__ "0|0|
S18SeSb1S81S8dS84A3SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C0_vars : ltac2:(tb__ "0|2|
S19S18SeSb4Sb6S9S1ePc6S9S1ePc7ScS1eA1A3A3A1M0S48S91SfA1M1A1A2SfA3S18SeSb5G0S4bG1A1A2SfA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma C0a_swf : ltac2:(tb__ "0|0|
S18SeS2bS74S48S91SfA1A1S75Pa4Pc6Pc7A3A2A1SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma C0c_below : ltac2:(tb__ "0|1|
S18SeS5eS23S31S2eS48S78A1M0A1A1SdS23S27G0A1ScdA3A3SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition Ck0 : axst := ltac2:(tb__ "0|2|
S4aS92SfA1M0Sc3S48G0A1M1S89S21UaS28G1A1A3A2A2").
Definition Cka : axst := ltac2:(tb__ "0|0|
S4aS76S74S48S76A1S75Pa4Pc6Pc7A3A2A2").
Definition Ckb : axst := Eval vm_compute in (match apply_axforms Cka XSEL with Some X => X | None => Cka end).
Lemma Ckb_eq : ltac2:(tb__ "0|0|
S18S12S49A1Sc6S82S7aA2S14S49S79A2A3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition F_newk : list sprop := ltac2:(tb__ "0|0|
SdS23ScdS9S23S36S35Sd0Sa8S97S25Z1A1A2S25Z0A1A3A1ScS23A1A3A3").
Definition Ckc : axst := ltac2:(tb__ "0|0|
Sc5S79SdS23S27S48S79A1A1S7dA3A2").
Definition Mkg : vmap := ltac2:(tb__ "0|3|
S9S11S1eS1fA2M0SbS1eS1fPa0Sa8Sa0S25N1A1A2A4S9G0SbS1eS1fPa1S9eA4S9G0SbS1eS1fPa2S9fA4S9G0SbS1eS1fPa3S9dA4S9G0SbS1eS1fPa4S26Pc6A1A4S9G0SbS1eS1fPa5S26Pc7A1A4S9G0SbS1eS1fPa6S8cA4S9G0SbS1eS1fPa7S8bA4S9G0SbS1eS1fPa8Sa8S97S25Z1A1A2A4S9G0SbS1eS1fPa9M1S26G1A1A4S9G0SbS1eS1fPaaM2Sa8S26G2A1S8bA2A4S9G0SbS1eS1fPc0Sa6A4S9G0SbS1eS1fPc1Sa7A4S9G0SbS1eS1fPd0Sb8A4ScG0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3").
Lemma Ckc_ent : ltac2:(tb__ "0|0|
S18SeSb1S83S8dS87A3SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Ck_vars : ltac2:(tb__ "0|1|
S19S18SeSb4Sb6S9S1ePc6S9S1ePc7ScS1eA1A3A3A1M0S48S76A1A2SfA3S18SeSb5G0S4bS76A1A2SfA3A2").
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast2.conj_vmc2. Qed.
Lemma Cka_swf : ltac2:(tb__ "0|0|
S18SeS2bS74S48S76A1S75Pa4Pc6Pc7A3A2A1SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Ckc_below : ltac2:(tb__ "0|1|
S18SeS5eS23S31S2eS48S79A1M0A1A1SdS23S27G0A1S7dA3A3SfA3"). Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Ck_objs : ltac2:(tb__ "0|0|
S18SaS21A1S28S48S92SfA1A1A1SdS21S28S48S76A1A1S9S21S9bS8cSa1A2ScS21A1A3A3A3"). Proof. reflexivity. Qed.

Definition E0x (nz : bool) : axst := ltac2:(tb__ "0|2|
S4aS93Vnz;A1M0Sc3S48G0A1M1S89S21U8S28G1A1A3A2A2").
Definition Ekx (nz : bool) : axst := ltac2:(tb__ "0|2|
S4aS94Vnz;A1M0Sc3S48G0A1M1S89S21U8S28G1A1A3A2A2").
Definition MX0 : vmap := ltac2:(tb__ "0|1|
S9S11S1eS1fA2M0SbS1eS1fPb8S25Z1A1A4S9G0SbS1eS1fPb9S8cA4S9G0SbS1eS1fPbaS8cA4S9G0SbS1eS1fPbbS8bA4S9G0SbS1eS1fPd0Sb8A4ScG0A1A3A3A3A3A3").
Definition MXk : vmap := ltac2:(tb__ "0|1|
S9S11S1eS1fA2M0SbS1eS1fPb8Sa8S97S25Z1A1A2A4S9G0SbS1eS1fPb9S26Pa9A1A4S9G0SbS1eS1fPbaS8cA4S9G0SbS1eS1fPbbSa8S26PaaA1S8bA2A4S9G0SbS1eS1fPd0Sb8A4ScG0A1A3A3A3A3A3").
Lemma E0x_ent : ltac2:(tb__ "0|0|
SeS18SeSb1S7bR1A1S8eS85A3SfA3Fnz;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Ekx_ent : ltac2:(tb__ "0|0|
SeS18SeSb1S7cR1A1S8eS86A3SfA3Fnz;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma E0_objs : ltac2:(tb__ "0|0|
SeS18SaS21A1S28S48S93R1A1A1A1SdS21S28S48S7bR1A1A1A1S9S21S9aR1A1S9S21S96S90S8bA2ScS21A1A3A3A3A3Fnz;"). Proof. intros [|]; reflexivity. Qed.
Lemma Ek_objs : ltac2:(tb__ "0|0|
SeS18SaS21A1S28S48S94R1A1A1A1SdS21S28S48S7cR1A1A1A1S9S21S9aR1A1S9S21S96S90S8bA2S9S21S9bS8cSa1A2ScS21A1A3A3A3A3A3Fnz;"). Proof. intros [|]; reflexivity. Qed.

Definition RMEM2 (m : bview) (G : ageom) (tmp rest : list qbatch) : Prop := ltac2:(tb__ "0|0|
S19S88S0SbfVm;A1SdS0Vtmp;Vrest;A3A3S19S54Vm;Vtmp;A2S19S54Vm;Vrest;A2S19S53Vm;S3fS7VG;A1Z50A2ScS0A1A3S53Vm;S3fSbaZa0A2Vrest;A3A2A2A2A2").

Definition HVX (rho : valuation) (tmp : list qbatch) : Prop := ltac2:(tb__ "0|2|
S19S18S4eQ40M0A1M1S22Vrho;Pb8A2S4dG0S42S13S0Vtmp;A2A1A2A3S19S18G1S22Vrho;Pb9A2S4dG0S6eVtmp;A1A2A3S19S18G1S22Vrho;PbaA2S4dG0S6dVtmp;A1A2A3S19S18G1S22Vrho;PbbA2S4dG0S51Vtmp;A1A2A3S18G1S22Vrho;Pd0A2S4dG0SaaA2A3A2A2A2A2").

Section Loop.
Variable K : AA -> jpredA.
Hypothesis HL : KQ_laws segsA K.
Variables (A0 : AA) (rho0 : valuation) (A1 : AA).
Hypothesis HTH : aa_q_thread A1 = [].
Hypothesis HCI : aa_cache_inited A1 = true.
Hypothesis HGEO : ltac2:(tb__ "0|0|
S18S8S4VA1;A1S4VA0;A1A3").
Hypothesis HQW : ltac2:(tb__ "0|0|
S1dSbeVA1;R1A2SbeVA0;R2A2F_;Fz;").
Let G := aa_geom A1.
Let T := ag_thread (aa_geom A1).

Record benv (rho : valuation) : Prop := mkBE {
  be_geom : geom_ok (aa_geom A1);
  be_top : top_high A1 rho;
  be_qp : q_pure A1;
  be_au : forall c, 1 <= c <= 30 -> 0 <= cs_allocated_user (cls_of A1 c) <= kUserSpaceSize;
  be_ids : forall c, 1 <= c <= 30 -> NoDup (cs_free_array (cls_of A1 c) ++ cs_cache (cls_of A1 c) ++ live_ids (aa_geom A1) A1 c ++ q_ids (aa_geom A1) (qall A1) c);
  be_sep : forall z, q_foot A1 z -> ~ (ag_thread (aa_geom A1) <= z < ag_thread (aa_geom A1) + 0x1000);
  be_secq : forall it, In it (qitems (qall A1)) -> is_primary (snd it) = false ->
      (fst it <= ag_spacebeg (aa_geom A1) \/ ag_spacebeg (aa_geom A1) + kSpaceSize + 4096 <= fst it - rz (snd it)) /\ fst it + snd it + 8 <= 140737479966720
}.
Lemma benv_of_K : ltac2:(tb__ "0|0|
S20SaS4eQ40A1A1SaSc2A1Sc1VK;VA1;R4R3R2R1A5S5aR5A1F_;Fmd;Ftr;Ftp;Frho;").
Proof.
  intros rho tp tr md HK. destruct (kq_facts segsA K HL A1 rho tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQP HIDS HSEP HSEP3 HKTOP HKSECQ].
  split; try assumption. intros c Hc. pose proof (cv_bounds _ _ _ _ _ (HCLS HCI c Hc)) as (B1 & B2 & B3 & _). unfold kUserMapSize in *. lia.
Qed.
Lemma qall_A1 : ltac2:(tb__ "0|0|
S18SaS0A1Sd8VA1;A1S1VA1;A1A3"). Proof. unfold qall. rewrite HTH. reflexivity. Qed.

Lemma batch_addr_facts : ltac2:(tb__ "0|3|
S20S0S5aR2A1S5dS0R2S1VA1;A1A3S19S3eZ646000S2R3A1M0A2S19S3eS3fG0Z2000M1A2M2S5S4VA1;A1A1A2S19S3eG2S41Z2Z3eA2A2S19S3eSabG0A2S18S1dS46G0G1A2Z0A3A2A2A2A2F_;F_;Fb;Frho;").
Proof.
  intros rho b [HG _ HQP HAU _ _ _] Hb. rewrite <- qall_A1 in Hb.
  destruct (batch_slot A1 HQP HAU HG b Hb) as (y & E & Y0 & Yal & Y1 & B5 & B6 & B7 & _).
  pose proof (geom_old _ HG) as HG'. rewrite kSpaceSize_val in HG'. destruct HG' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & _).
  pose proof (topG_range (aa_geom A1)) as TG. unfold HIGH_SHADOW_END in *. repeat split; lia.
Qed.
Lemma batches_apart1 : ltac2:(tb__ "0|4|
S20S0S0S5aR3A1S5dS0R3S1VA1;A1A3M0G0S1aS18S1dS2R5A1M1S2R4A1A3A1S1cS3eS3fS2R6A1M2Z2000M3A2G1A2S3eS3fG1G3A2G2A2A2F_;F_;F_;F_;Fb2;Fb1;Frho;").
Proof. intros rho b1 b2 [HG _ HQP HAU _ _ _] H1 H2 NE. rewrite <- qall_A1 in H1, H2. exact (batches_apart A1 HQP HAU HG b1 b2 H1 H2 NE). Qed.
Lemma batch_addr_inj : ltac2:(tb__ "0|1|
S20S0S0S5aR3A1S5dS0R3S1VA1;A1A3M0G0S18S1dS2R5A1S2R4A1A3S18S0R6R5A3F_;F_;F_;F_;Fb2;Fb1;Frho;").
Proof.
  intros rho b1 b2 [_ _ [_ HND] _ _ _ _] H1 H2 E. rewrite qall_A1 in HND. exact (NoDup_map_In_inj qb_addr _ b1 b2 HND H1 H2 E).
Qed.

Definition HVH (rho : valuation) (rest : list qbatch) (lb : Z) : Prop := ltac2:(tb__ "0|2|
S19S18S4eQ40M0A1M1S22Vrho;Pa0A2S4dG0S42S13S0Vrest;A2A1A2A3S19S18G1S22Vrho;Pa1A2S4dG0S6eVrest;A1A2A3S19S18G1S22Vrho;Pa2A2S4dG0Vlb;A2A3S19S18G1S22Vrho;Pa3A2S4dG0S51Vrest;A1A2A3S18G1S22Vrho;Pd0A2S4dG0SaaA2A3A2A2A2A2").
Definition HVC (rho : valuation) (rest : list qbatch) : Prop := ltac2:(tb__ "0|2|
S19S18S4eQ40M0A1M1S22Vrho;Pa4A2S4dG0S6eS62S0Vrest;A2A1A2A3S18G1S22Vrho;Pa5A2S4dG0S3S60S0S52Vrest;A3A1A2A3A2").
Definition HVT (rho : valuation) (pre : list qbatch) : Prop := ltac2:(tb__ "0|2|
S19S18S4eQ40M0A1M1S22Vrho;Pa6A2S4dG0S6dVpre;A1A2A3S19S18G1S22Vrho;Pa7A2S4dG0S3S5fS0Vpre;S52A3A1A2A3S19S18G1S22Vrho;Pa8A2S4dG0S42S13S0Vpre;A2A1A2A3S19S18G1S22Vrho;Pa9A2S4dG0S6eVpre;A1A2A3S18G1S22Vrho;PaaA2S4dG0S51Vpre;A1A2A3A2A2A2A2").

Lemma head0_carve : ltac2:(tb__ "0|6|
S0SaS0A1M0S1dS20SaS4eQ40M1A1M2A1S72S18G0S1VA1;A1S9S0R6R5A3A3S55S47S63VK;VA0;Vrho0;VA1;ScS0A1M3S9S0R7R6A3A6S8fR4R3R2A6S58R5S9S0R8R7A3R6A3Sb7R6S9S11S1eG2A2M4SbS1eG2Pa4S4dG1S6eR8A1A2A4S9G4SbS1eG2Pa5S4dG1S3R9A1A2A4ScG4A1A3A3A2S20S19S55S47S63VK;VA0;Vrho0;VA1;G3S9S0RaR9A3M5A6S95R1R6R5A6S19S58R1G5R8A3S59R1G5A2A2A2Trho1;F_;F_;F_;Fw;Ftp;Frho;Flb;Frest';Fcur;").
Proof.
  intros cur rest' lb rho tp w HGL H (E160 & E161 & E162 & E163 & E208) rho1.
  pose proof (JRQ_stable K HL A0 rho0 A1 [] (cur :: rest')) as HST.
  assert (H1 : SPA segsA (JRQ K A0 rho0 A1 [] (cur :: rest')) PH rho1 tp w).
  { apply (SPA_bindV segsA _ NPRE PH rho tp w _ eq_refl HST); [| exact (proj1 PH_vars) | exact (proj2 PH_vars) | exact H].
    intros v Hv. cbn in Hv. destruct Hv as [<-|[<-|[]]]; unfold NPRE, Pos.le; cbn; discriminate. }
  assert (OTH : forall i, i <> 164%positive -> i <> 165%positive -> rw rho1 i = rw rho i).
  { intros i N1 N2. unfold rho1. apply rho_sets_other. cbn. intros [X|[X|[]]]; congruence. }
  assert (E164 : rw rho1 164%positive = Z_to_bv 64 (hd_addr rest')) by reflexivity.
  assert (E165 : rw rho1 165%positive = Z_to_bv 64 (qb_size cur)) by reflexivity.
  split; [|split; [unfold HVH; rewrite !OTH by discriminate; tauto | split; [exact E164 | exact E165]]].
  destruct w as [tr [ms md]]. destruct (proj2 H1) as (HK & (HBM & _ & HLK & _) & _). cbn [w_tr w_cfg cfg_model fst snd] in HK, HBM, HLK.
  pose proof (benv_of_K _ _ _ _ HK) as BE.
  assert (INC : In cur (aa_q_global A1)) by (rewrite HGL; left; reflexivity).
  destruct (batch_addr_facts _ cur BE INC) as (BA1 & BA2 & BA3 & BA4 & BA5).
  cbn [app] in HBM. pose proof (Forall_inv HBM) as (CSZ & _). cbn [qlinks] in HLK. destruct HLK as [CNX _].
  assert (CNX' : cell_ok (view segsA (rm rho1)) (mkACell (qb_addr cur) 8 (hd_addr rest'))) by (destruct rest'; exact CNX).
  rewrite <- Head0_eq. apply (carve_bhdr _ PH rho1 tp _ 161 164 165 (qb_addr cur) (hd_addr rest') (qb_size cur) H1 eq_refl Head0_swf); try assumption.
  - lia.
  - pose proof (SPA_facts_hold segsA _ rho1 PH tp _ H1) as HF.
    assert (HF' : Forall (holds rho1) (pre_facts DEPTH_R)) by (unfold PH, mkR, F_H, F_H0 in HF; cbn [ax_S mkA ss_facts] in HF; apply Forall_app in HF as [HF _]; apply Forall_app in HF as [HF _]; exact HF).
    pose proof (OH_fixed A1 rho1 [] (sw_cells ZQ ZQ ZQ ZQ) (SLit 257) vN vCUR vLB vS (be_top _ BE) HF') as FX.
    eapply Forall_impl; [|exact FX]. intros o Ho. apply (fixed_clear rho1 (topG (aa_geom A1)) o _ _ Ho); lia.
Qed.

Lemma absorb_out : ltac2:(tb__ "0|4|
S20SaS21A1SceS1dOF_;S4eQ40M0A1M1Sd1R5R4R1A3R3S4fG0R2A2A1F_;Fa;S19S1dS1aR3R1A1A1S18S12S4eQ8A1A1M2S6aS47S24Sd2R7R6R5A3M3A1R2A3S6aS47S24R7A1R2A3A3F_;Fz;G1S1aR3S4fG0R1A2A1A1S18G2S24G3R2A2S24R7R2A2A3F_;Fa;A2F_;FP;Fms;FR;Frho;").
Proof.
  intros rho R ms P HP. split.
  - intros z Hz. apply view_agree. intros Hr. apply rm_absorb_out. intros Hin. apply Hz. pose proof (HP _ Hin) as X. rewrite u64_lit in X by exact Hr. exact X.
  - intros a Hz. apply rm_absorb_out. intros Hin. exact (Hz (HP _ Hin)).
Qed.

Lemma K_FRM_absorb : ltac2:(tb__ "0|a|
S20S20SaS4eQ40M0A1M1A1SaSc2A1Sc1S1dOF_;S1dS1cR2R1A1M2S1aG2A1A2Fz;S1eS18G1S22R7R1A2S22R8R1A2A3Fi;S1eS18SaS4eQ8A1M3A1S33R8R1A2S33R9R1A2A3Fl;S1dR5R1A1S1cS19SbeVA1;R2A2S1aS19S3eSadR2A2S40R2SacA2A2A1A2S19S19Sc0VA0;R2A2G1S18S1dS4fG0R1A2M4R3A3S1aS18S12G3A1M5S24RdR2A2M6S15G3A1M7A3A1S1aS18G5S24RdR3A2G7A3A1F_;F_;Fa;A2S18G5S6aS47S24RaA1R2A3S6aS47S24RbA1R2A3M8A3A2A2F_;Fz;S1dS1aR6R1A1A1S18G5G8S6aS47S24RcA1R2A3A3F_;Fz;G1S1aR7G4A1A1S18G5S24RcR2A2G6A3F_;Fa;S1dR8R1A1S1aS18G5S6aS47S24RdA1R2A3G7A3A1F_;Fz;VK;VA1;RdRbRaR9A5S64VA0;Vrho0;ReA3M9S19VK;VA1;ReRdRcRbA5G9A2F_;F_;F_;F_;F_;F_;F_;F_;F_;FP;Fmd;Ftr;Ftp;Frho3;Frho;").
Proof.
  intros rho rho3 tp tr md P PD Hrw Hrl HP FR FRrm PPR HK ((F1 & F1') & F2 & F3 & F4). split.
  - apply (kq_view segsA K HL A1 rho rho3 tp tr md Hrw Hrl); [| | exact HK].
    + intros z NQ. destruct (PD z) as [Hp|Np]; [|exact (FR z Np)]. destruct (HP z Hp) as [[HQ _]|[_ HE]]; [exfalso; exact (NQ HQ) | exact HE].
    + intros z _ Hd. destruct (PD z) as [Hp|Np]; [exact (PPR z Hp) | rewrite (FR z Np); exact Hd].
  - split; [split; [intros i Hi; rewrite Hrw; exact (F1 i Hi) | intros l; rewrite Hrl; exact (F1' l)]|]. split; [|split].
    + intros a NQ. rewrite FRrm; [exact (F2 a NQ)|]. intros Hp. apply NQ. destruct (HP _ Hp) as [[HQ _]|[[HQ _] _]]; [left; left; exact (HQW _ HQ) | exact HQ].
    + intros z NQ. rewrite <- (F3 z NQ). destruct (PD z) as [Hp|Np]; [|exact (FR z Np)]. destruct (HP z Hp) as [[HQ _]|[_ HE]]; [exfalso; apply NQ; left; exact (HQW _ HQ) | exact HE].
    + intros a HB Hdef. pose proof (F4 a HB Hdef) as X. destruct (PD (bv_unsigned a)) as [Hp|Np]; [|rewrite (FRrm a Np); exact X].
      destruct (HP _ Hp) as [[_ HNB]|[[_ HD] _]]; [exfalso; exact (HNB HB) | exact (HD a eq_refl X)].
Qed.

Lemma eval_add_lit : ltac2:(tb__ "0|7|
S20S1fS1dS1dS18S4eQ40M0A1M1S2aR4R3A2S4dG0R2A2A3S19S3eZ0M2R3A2S40R3S41Z2M3Z40A2M4A2A2S19S3eS44S41G3Z3fA2M5A1R3A2S40R3G5A2A2S19S3eG2S3fR5R4A2M6A2S40G6G4A2A2S18G1S2aR8Sa8R7S25R5A1A2A2S4dG0S3fR6R5A2A2A3F_;F_;F_;F_;Fk;Fx;Fa;Frho;").
Proof.
  intros rho a x k Ea Hx Hk Hs. apply bv_eq. unfold add. cbn [eval]. rewrite add_val, Ea, (u64_lit x), (u64_lit (x + k)) by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia.
Qed.
Lemma eval_sub_z : ltac2:(tb__ "0|3|
S20S1fS1fS1dS1dS18S4eQ40M0A1M1S2aR5R4A2S4dG0R2A2M2A3S18G1S2aR6R4A2G2A3S19S3eZ0R3A2S3eR3R4A2A2S40R5S41Z2Z40A2A2S18G1S2aR9S34ScfR8R7A3A2S4dG0S43R6R5A2A2A3F_;F_;F_;F_;Fy;Fx;Fb;Fa;Frho;").
Proof.
  intros rho a b x y Ea Eb Hy Hx. apply bv_eq. cbn [eval]. rewrite sub_val, Ea, Eb, !u64_lit by lia. apply Z.mod_small. lia.
Qed.
Lemma hd_addr_cons : ltac2:(tb__ "0|0|
S0SaS0A1S18S1dS6eS9S0R2R1A3A1S2R2A1A3Fl;Fb;"). Proof. reflexivity. Qed.
Lemma qsize_cons : ltac2:(tb__ "0|0|
S0SaS0A1S18S1dS51S9S0R2R1A3A1S3fS3R2A1S51R1A1A2A3Fl;Fb;"). Proof. reflexivity. Qed.

Lemma new_glue : ltac2:(tb__ "0|f|
S56S49S49SaS23A1Sb3SaS2cA1S1fS1fS1fS1fS0S0S1dS20SaS4eQ40M0A1M1A1S72S57S47Sa9R10A3S18SeSb4Sb6S9S1ePc6M2S9S1ePc7M3ScS1eA1A3A3A1M4S48R10A1A2SfA3S18SeSb5G4S4bR11A1A2SfA3S18SaS11S1fS1fA2M5A1S4cR12A1ScG5A1A3S18SeS2bS74S48R13A1S75Pa4M6G2G3A3M7A2A1SfA3S18S12S49A1Sc6S4aR14S74S48R14A1M8G7A2A2S7aA2S14S49R13A2A3S18SeS5eS23S31S2eG8A1A1SdS23S27G8A1R13A3A3SfA3S18SeSb1Sc5R15SdS23S27S48R15A1A1R14A3A2S8dR13A3SfA3S18SaS21A1S28S48R17A1A1SdS21SdS21S9cScS2cA1S30S26PaA1S25Na8A1S25Z0A1R13S2fA5A2S9S21SbdS25Z101A1A1S9S21SbbScS21A1M9A3A3A3SdS21ScaS9S21SbcR12R11R10RfA4S9S21S96S90S8bA2G9A3A3A3A3A3S20S88S23S2dR1A1MaS27S48R19A1A1A3S88S23S2dR2A1Sc9Sb9A1A3F_;Fr;S55S47R1aR19RdRcRbA6S5aReA1S5dS0R12S1VA1;A1A3MbGbS1aS18S1dS2R14A1S2R13A1A3A1S18G1S22R12Pa1A2S4dG0S2R15A1A2McA3S18G1S22R13G6A2GcA3S68S6aS47S24R14A1A2S69S2R16A1U8MdR15A3A2S68S6aS47S24R15A1A2S69S3fS2R17A1Z8A2GdS3R17A1A3A2Sb7R16S9S11S1eG1A2MeSbS1eG1G2S4dG0R17A2A4S9GeSbS1eG1G3S4dG0S3R18A1A2A4ScGeA1A3A3A2S20S88S23GaR21A3S1bS20S20S19S55S47R26S8dR1R18R17A6S19S1eS1fS5dS11S1eS1fA2SbS1eS1fR2R1A4R24A3S18G1S22R4R3A2S2aR6R2A2A3F_;Fe;Fv;S18G1S12S4eQ8A1A1F_;S24R1A1S24R19A1A3A2A2Lrho2;A2F_;Trho1;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Fnn;Fnxt;Fcur;Fg4;Fg3;Fg2;Fg1;Fswc;FM;FFnew;FCb;FC;FJ;").
Proof.
  intros J C Cb Fnew M swc g1 g2 g3 g4 cur nxt nn rho tp w HST HV1 HV2 HX Hswf HAX HBEL HENT HOBJ HPF H BE INC INN NE E161 E164 CN CS rho1 HFN.
  assert (H1 : SPA segsA J C rho1 tp w).
  { apply (SPA_bindV segsA _ NPRE C rho tp w _ HX HST); [| exact HV1 | exact HV2 | exact H].
    intros v Hv. cbn in Hv. destruct Hv as [<-|[<-|[]]]; unfold NPRE, Pos.le; cbn; discriminate. }
  assert (OTH : forall i, i <> 198%positive -> i <> 199%positive -> rw rho1 i = rw rho i).
  { intros i N1 N2. unfold rho1. apply rho_sets_other. cbn. intros [X|[X|[]]]; congruence. }
  assert (ERM : rm rho1 = rm rho) by (unfold rho1; apply rm_rho_sets).
  destruct (batch_addr_facts _ cur BE INC) as (CA1 & CA2 & CA3 & CA4 & CA5). destruct (batch_addr_facts _ nxt BE INN) as (BA1 & BA2 & BA3 & BA4 & BA5).
  pose proof (batches_apart1 _ cur nxt BE INC INN NE) as AP.
  pose proof (HPF rho1 (SPA_facts_hold segsA _ rho1 C tp _ H1)) as HF1.
  assert (HTOP1 : top_high A1 rho1) by (pose proof (be_top _ BE) as X; unfold top_high in *; rewrite !OTH by (unfold V_DEPTH; discriminate); exact X).

  assert (H2 : SPA segsA J (ax_setS C (with_obj (ax_S C) (O_bh 164 198 199))) rho1 tp w).
  { apply (carve_bhdr J C rho1 tp w 164 198 199 (qb_addr nxt) nn (qb_size nxt) H1 HX Hswf); try reflexivity; try lia.
    - rewrite OTH by discriminate. exact E164.
    - rewrite ERM. exact CN.
    - rewrite ERM. exact CS.
    - rewrite HOBJ. pose proof (OH_fixed A1 rho1 [] swc (SLit 257) g1 g2 g3 g4 HTOP1 HF1) as FX.
      replace ((STK [] (mkObj (SVar 10) (SLit (-168)) (SLit 0) swc DUnknown) ++ [O_mtx (SLit 257); O_gmax]) ++ A_globals ++ [O_gq g1 g2 g3 g4; O_cur ZQ vCSZ])
        with (((STK [] (mkObj (SVar 10) (SLit (-168)) (SLit 0) swc DUnknown) ++ [O_mtx (SLit 257); O_gmax]) ++ A_globals ++ [O_gq g1 g2 g3 g4]) ++ [O_cur ZQ vCSZ]) by (rewrite <- !app_assoc; reflexivity).
      apply Forall_app. split.
      + eapply Forall_impl; [|exact FX]. intros o Ho. apply (fixed_clear rho1 (topG (aa_geom A1)) o _ _ Ho); lia.
      + apply Forall_cons; [|apply Forall_nil]. unfold O_cur, carved, vCUR. rewrite obj_range_mk by lia. cbn [eval]. rewrite OTH by discriminate. rewrite E161, u64_lit by lia.
        unfold ranges_disjoint. cbn [fst snd]. lia. }
  pose proof (SPA_axforms segsA J _ rho1 _ Cb tp _ HAX H2) as H3.
  assert (H4 : SPA segsA J (ax_with_facts Cb (ss_facts (ax_S Cb) ++ Fnew)) rho1 tp w).
  { apply SPA_refacts; [exact H3 | exact HBEL |]. intros HF. apply Forall_app. split; [exact HF | exact HFN]. }
  destruct (entM_SPA J _ Headk M rho1 tp w HENT HST H4) as (H5 & AG5 & V5 & RM5).
  eexists. split; [exact H5|]. split; [exact V5|]. rewrite RM5. exact ERM.
Qed.

Lemma qsz_ge : ltac2:(tb__ "0|5|
S20S6bSaS0A1M0G0S5aR4A1S88S0SbfR4A1SdS0R3R2A3A3S18G0S1VA1;A1M1SdS0R4R3A3A3S19S3eS45Z2000M2S42S13S0R5A2A1A2S51R5A1M3A2S19S3eS45G2S42S13S0R4A2A1A2S51R4A1M4A2S18S1dS51G1A1S3fG3G4A2A3A2A2F_;F_;F_;Fl2;Fl1;Fm;Frho;").
Proof.
  intros rho m l1 l2 BE HBM E. pose proof (proj1 (be_qp _ BE)) as HBP. rewrite qall_A1, E in HBP.
  apply Forall_app in HBP as [P1 P2]. apply Forall_app in HBM as [M1 M2].
  pose proof (qsize_ge A1 m l1 P1 M1). pose proof (qsize_ge A1 m l2 P2 M2). unfold kQuarantineBatchSize in *. rewrite E, qsize_app. lia.
Qed.
Lemma NoDup_addr_all : ltac2:(tb__ "0|0|
S20S5aR1A1SdaS1dS8aS0S1dS2S1VA1;A1A4A2F_;Frho;").
Proof. intros rho BE. pose proof (proj2 (be_qp _ BE)) as X. rewrite qall_A1 in X. exact X. Qed.

Lemma cont0_glue : ltac2:(tb__ "0|5|
S0S0SaS0A1M0S1dS20SaS4eQ40A1A1S72S18G0S1VA1;A1M1S9S0R7S9S0R6R5A3A3A3S40S51G1A1S41Z2Z3eA2A2S55S47S63VK;VA0;Vrho0;VA1;ScS0A1M2S9S0R9S9S0R8R7A3A3A6S91SfA1R5R4R3A6S58R6S9S0RaS9S0R9R8A3A3R7A3S59R7S9S0RbS9S0RaR9A3A3A2S1bS20S20S19S55S47S63VK;VA0;Vrho0;VA1;S9S0RdG2A3M3S9S0RcRbA3M4A6S8dR1R8R7A6S19S58R1G4RaA3S19S59R1G4A2S5bR1G3A2A2A2A2Lrho2;A2F_;F_;F_;F_;F_;Fw;Ftp;Frho;Flb;Frest'';Fnxt;Fcur;").
Proof.
  intros cur nxt rest'' lb rho tp w HGL HSZ H (E160 & E161 & E162 & E163 & E208) (E164 & E165).
  cbn [List.tl hd] in E164, E165. rewrite hd_addr_cons in E161, E164.
  destruct w as [tr [ms md]]. destruct (proj2 H) as (HK & (HBM & _ & HLK & HTHD) & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HBM, HLK, HTHD, HFRM.
  pose proof (benv_of_K _ _ _ _ HK) as BE. cbn [app] in HBM.
  assert (INC : In cur (aa_q_global A1)) by (rewrite HGL; left; reflexivity).
  assert (INN : In nxt (aa_q_global A1)) by (rewrite HGL; right; left; reflexivity).
  assert (NE : qb_addr cur <> qb_addr nxt).
  { pose proof (NoDup_addr_all _ BE) as ND. rewrite HGL in ND. cbn [map] in ND. inversion ND as [|x l Hn Hd]; subst. intros E. apply Hn. rewrite E. left. }
  destruct (qsz_ge rho _ [cur] (nxt :: rest'') BE HBM HGL) as (S1 & S2 & S3). rewrite S3 in HSZ.
  assert (Q1 : qsize [cur] = qb_size cur) by (unfold qsize; cbn [fold_right]; lia). rewrite Q1 in *. clear Q1. cbn [length] in S1.
  destruct HLK as (CNc & CNn & HLK').
  assert (CNn' : cell_ok (view segsA (rm rho)) (mkACell (qb_addr nxt) 8 (hd_addr rest''))) by (destruct rest''; exact CNn).
  pose proof (proj1 (Forall_inv (Forall_inv_tail HBM))) as CSn.
  assert (H' : SPA segsA (JRQ K A0 rho0 A1 [cur] (nxt :: rest'')) (Cont0 true) rho tp (tr, mkCfg ms md)).
  { split; [exact (proj1 H)|]. split; [exact HK|]. split; [|exact HFRM]. split; [exact HBM|]. split; [exact I|]. split; [exact (conj CNn HLK') | exact HTHD]. }
  destruct (batch_addr_facts _ nxt BE INN) as (BA1 & BA2 & BA3 & BA4 & BA5).
  set (rho1 := rho_sets rho [(198%positive, Z_to_bv 64 (hd_addr rest'')); (199%positive, Z_to_bv 64 (qb_size nxt))]).
  assert (OTH : forall i, i <> 198%positive -> i <> 199%positive -> rw rho1 i = rw rho i).
  { intros i N1 N2. unfold rho1. apply rho_sets_other. cbn. intros [X|[X|[]]]; congruence. }
  assert (LEN : 2 <= Z.of_nat (length (cur :: nxt :: rest'')) < 2 ^ 60) by (cbn [length] in S2 |- *; lia).
  assert (EN1 : eval rho1 (add vN (SLit (-1))) = Z_to_bv 64 (Z.of_nat (length (nxt :: rest'')))).
  { replace (Z.of_nat (length (nxt :: rest''))) with (Z.of_nat (length (cur :: nxt :: rest'')) + -1) by (cbn [length]; lia).
    apply eval_add_lit; [unfold vN; cbn [eval]; rewrite OTH by discriminate; exact E160 | lia | lia | lia]. }
  assert (ES' : eval rho1 s' = Z_to_bv 64 (qsize (nxt :: rest''))).
  { replace (qsize (nxt :: rest'')) with (qsize (cur :: nxt :: rest'') - qb_size cur) by (rewrite (qsize_cons cur); lia).
    apply eval_sub_z; [unfold vS; cbn [eval]; rewrite OTH by discriminate; exact E163 | unfold vCSZ; cbn [eval]; rewrite OTH by discriminate; exact E165 | rewrite (qsize_cons cur); lia | rewrite (qsize_cons cur); lia]. }
  destruct (new_glue _ (Cont0 true) C0b F_new M0g (sw_cells ZQ vCUR ZQ vCSZ) _ _ _ _ cur nxt (hd_addr rest'') rho tp _
              (JRQ_stable K HL A0 rho0 A1 [cur] (nxt :: rest'')) (proj1 C0_vars) (proj2 C0_vars) eq_refl C0a_swf C0b_eq C0c_below C0c_ent eq_refl
              ltac:(intros r HF; unfold Cont0, mkR, F_H, F_H0 in HF; cbn [ax_S mkA ss_facts] in HF; apply Forall_app in HF as [HF _]; apply Forall_app in HF as [HF _]; apply Forall_app in HF as [HF _]; exact HF)
              H' BE INC INN NE E161 E164 CNn' CSn) as (rho2 & H2 & V2 & RM2).
  { fold rho1. unfold F_new. repeat apply Forall_cons; try apply Forall_nil.
    - cbn [holds branch_taken]. rewrite EN1. cbn [eval]. unfold bv_eqb. rewrite !u64_lit by (cbn [length] in *; lia). intros E. apply Z.eqb_eq in E. cbn [length] in E. lia.
    - unfold vCN. cbn [holds eval]. rewrite OTH by discriminate. rewrite E164, !u64_lit by (unfold HIGH_SHADOW_END in *; lia). exact BA4.
    - cbn [holds]. split; [lia|]. rewrite OTH by discriminate. rewrite E164, u64_lit by lia.
      clear -BA5. pose proof (Z.div_mod (qb_addr nxt) 8192 ltac:(lia)) as D. rewrite BA5, Z.add_0_r in D. rewrite D. replace (8192 * (qb_addr nxt / 8192)) with (1024 * (qb_addr nxt / 8192) * 2 ^ 3) by lia. apply Z.mod_mul. lia. }
  fold rho1 in V2. exists rho2. split; [exact H2|].
  assert (VV : forall v e, In (v, e) M0g -> rw rho2 v = eval rho1 e) by exact V2. clear V2.
  split; [|split].
  - unfold HVH. split; [rewrite (VV 160%positive _ ltac:(cbn; tauto)); exact EN1|].
    split; [rewrite (VV 161%positive _ ltac:(cbn; tauto)); unfold vCN; cbn [eval]; rewrite OTH by discriminate; exact E164|].
    split; [rewrite (VV 162%positive _ ltac:(cbn; tauto)); unfold vLB; cbn [eval]; rewrite OTH by discriminate; exact E162|].
    split; [rewrite (VV 163%positive _ ltac:(cbn; tauto)); exact ES'|].
    rewrite (VV 208%positive _ ltac:(cbn; tauto)). unfold vMIN. cbn [eval]. rewrite OTH by discriminate. exact E208.
  - unfold HVC. cbn [List.tl hd]. split; [rewrite (VV 164%positive _ ltac:(cbn; tauto)); reflexivity | rewrite (VV 165%positive _ ltac:(cbn; tauto)); reflexivity].
  - unfold HVT. cbn [last length]. unfold last_addr. cbn [last]. rewrite hd_addr_cons. rewrite qsize_cons. change (qsize []) with 0. rewrite Z.add_0_r.
    split; [rewrite (VV 166%positive _ ltac:(cbn; tauto)); unfold vCUR; cbn [eval]; rewrite OTH by discriminate; exact E161|].
    split; [rewrite (VV 167%positive _ ltac:(cbn; tauto)); unfold vCSZ; cbn [eval]; rewrite OTH by discriminate; exact E165|].
    split; [rewrite (VV 168%positive _ ltac:(cbn; tauto)); reflexivity|].
    split; [rewrite (VV 169%positive _ ltac:(cbn; tauto)); unfold vCUR; cbn [eval]; rewrite OTH by discriminate; exact E161|].
    rewrite (VV 170%positive _ ltac:(cbn; tauto)). unfold vCSZ. cbn [eval]. rewrite OTH by discriminate. exact E165.
Qed.

Lemma ifoot_not_batch : ltac2:(tb__ "0|3|
S20S11S1dS1dA2M0S0S5aR3A1S5dG0R3Sd9S1VA1;A1M1A1A3S5dS0R3G1A3S1dS70R6R1A2S1aS19S3eS2R6A1M2R2A2S40R2S3fG2Z2000A2A2A2A1F_;Fz;F_;F_;F_;Fb;Fit;Frho;").
Proof.
  intros rho it b BE Hit Hb z Hz HP. pose proof BE as [HG _ HQP HAU HIDS _ HSECQ]. rewrite <- qall_A1 in Hit, Hb.
  destruct (batch_slot A1 HQP HAU HG b Hb) as (y & E & Y0 & Yal & Y1 & B5 & B6 & B7 & _).
  pose proof (geom_old _ HG) as HG'. rewrite kSpaceSize_val in HG'. destruct HG' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H1 & H2 & H3 & _).
  destruct (qitems_In A1 it Hit) as (b0 & Hb0 & Hib).
  pose proof (proj1 (Forall_forall _ _) (proj1 HQP) b0 Hb0) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hib) as (IP1 & IP2 & IP3 & IP4).
  pose proof (rz_facts (snd it)) as [RZ1 RZ2]. unfold IMG_HI in IP1. unfold ifoot, it_ab in Hz.
  destruct (is_primary (snd it)) eqn:EP.
  - pose proof (item_batch_apart A1 HQP HIDS HAU HG it b Hit EP Hb) as AP.
    pose proof (item_zones A1 HQP HAU HG it Hit EP) as IZ. cbv zeta in IZ. destruct IZ as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & _). unfold it_ab, HIGH_SHADOW_END in *.
    destruct Hz as [Hz|Hz]; lia.
  - pose proof (HSECQ it Hit EP) as [SQ SQ2]. rewrite kSpaceSize_val in SQ.
    assert (SHhi : Sh (fst it) + (snd it + 7) / 8 <= 0x10007fff8000).
    { unfold Sh, SHADOW_OFF. pose proof (Z.div_mod (fst it) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (fst it) 8 ltac:(lia)).
      pose proof (Z.div_mod (snd it + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (snd it + 7) 8 ltac:(lia)). lia. }
    unfold HIGH_SHADOW_END in *. destruct Hz as [Hz|Hz]; lia.
Qed.
Lemma bfoot_not_link : ltac2:(tb__ "0|2|
S20S0S0S5aR3A1S5dS0R3S1VA1;A1A3M0G0S1dS6fR6R1A2S1aS19S3eS2R6A1M1R2A2S40R2S3fG1Z8A2A2A2A1F_;Fz;F_;F_;F_;Fb';Fb;Frho;").
Proof.
  intros rho b b' BE Hb Hb' z [Hz|Hz] HP.
  - unfold kQuarantineBatchSize in Hz. destruct (Z.eq_dec (qb_addr b) (qb_addr b')) as [E|NE]; [lia|].
    pose proof (batches_apart1 _ b b' BE Hb Hb' NE). lia.
  - apply Exists_exists in Hz as (it & Hit & Hz).
    assert (Hin : In it (qitems (aa_q_global A1))) by (unfold qitems; apply in_flat_map; exists b; exact (conj Hb Hit)).
    exact (ifoot_not_batch rho it b' BE Hin Hb' z Hz ltac:(lia)).
Qed.
Lemma bfoot_size_own : ltac2:(tb__ "0|2|
S20S0S0S5aR3A1S5dS0R3S1VA1;A1A3M0G0S1dS6fR6R1A2S19S3eS3fS2R6A1M1Z8A2R2A2S40R2S3fG1Z10A2A2A2S18S0R8R7A3F_;F_;Fz;F_;F_;F_;Fb';Fb;Frho;").
Proof.
  intros rho b b' BE Hb Hb' z [Hz|Hz] HP.
  - unfold kQuarantineBatchSize in Hz. destruct (Z.eq_dec (qb_addr b) (qb_addr b')) as [E|NE]; [exact (batch_addr_inj _ b b' BE Hb Hb' E)|].
    pose proof (batches_apart1 _ b b' BE Hb Hb' NE). lia.
  - exfalso. apply Exists_exists in Hz as (it & Hit & Hz).
    assert (Hin : In it (qitems (aa_q_global A1))) by (unfold qitems; apply in_flat_map; exists b; exact (conj Hb Hit)).
    exact (ifoot_not_batch rho it b' BE Hin Hb' z Hz ltac:(lia)).
Qed.
Lemma batch_in_QW : ltac2:(tb__ "0|1|
S20S0S1dS5aR3A1S5dS0R3S1VA1;A1A3S19S3eS2R4A1M0R3A2S40R3S3fG0Z2000A2A2A2S19SbeVA1;R4A2S1aS19S3eSadR4A2S40R4SacA2A2A1A2F_;F_;F_;Fz;Fb;Frho;").
Proof.
  intros rho b z BE Hb Hz. destruct (batch_addr_facts _ b BE Hb) as (_ & _ & _ & B4 & _). split.
  - left. unfold qzone. apply Exists_exists. exists b. split; [rewrite qall_A1; exact Hb|]. left. unfold kQuarantineBatchSize. exact Hz.
  - unfold SHADOW_BAND_HI. lia.
Qed.

Lemma last_snoc : ltac2:(tb__ "0|0|
SaS0A1S0S0S18S0S5fS0SdS0R3S9S0R2ScS0A1A3A3R1A3R2A3Fd;Fc;Fl;").
Proof. intros l c d. apply last_last. Qed.
Lemma hd_addr_app : ltac2:(tb__ "0|1|
SaS0A1M0G0S1aS18G0R2ScS0A1A3A1S18S1dS6eSdS0R3R2A3A1S6eR3A1A3F_;Fl2;Fl1;").
Proof. intros [|b l1] l2 H; [congruence | reflexivity]. Qed.
Lemma tlinks_snoc : ltac2:(tb__ "0|4|
S6bS6bSaS0A1M0S0S1dS0S1dS5dS0R2S61S0R5A2A3S19S3eS2R3A1M1R2A2S40R2S3fG1Z8A2A2A2S18S12S4eQ8A1A1R8R3A1R9R3A1A3F_;F_;Fz;Fb;S1aS18G0R4ScS0A1M2A3A1S68R6S69S6dR5A1U8M3S2R4A1A3A2F_;S67R7R5A2S68R7S69S2R5A1G3R4A3A2S71R8SdS0R7S9S0R6G2A3A3R5A3F_;F_;F_;F_;Ft;Fc;Fpre;Fm';Fm;").
Proof.
  intros m m' pre c t HF HC HT Hc. destruct pre as [|p0 pre'] eqn:EP; [cbn; split; [exact Hc | exact I]|]. rewrite <- EP in *.
  assert (NE : pre <> []) by (rewrite EP; discriminate). unfold tlinks in HT. rewrite EP in HT. rewrite <- EP in HT.
  rewrite (app_removelast_last qb_dflt NE) at 1. rewrite <- app_assoc. apply qlinks_to_app; [discriminate | |].
  - change (hd_addr ([last pre qb_dflt] ++ [c])) with (last_addr pre). apply (qlinks_to_frame m m'); [exact HF | exact HT].
  - cbn. split; [exact (HC NE) | split; [exact Hc | exact I]].
Qed.

Lemma contk_glue : ltac2:(tb__ "0|5|
SaS0A1M0S0S0G0S1dS20SaS4eQ40A1A1S72S1aS18G0R8ScS0A1M1A3A1S18G0S1VA1;A1M2SdS0R9S9S0R8S9S0R7R6A3A3A3A3S40S51G2A1S41Z2Z3eA2A2S55S47S63VK;VA0;Vrho0;VA1;RbS9S0RaS9S0R9R8A3A3A6S92SfA1R6R5R4A6S58R7S9S0RbS9S0RaR9A3A3R8A3S59R8S9S0RcS9S0RbRaA3A3A2S5bR9ReA2S1bS20S20S19S55S47S63VK;VA0;Vrho0;VA1;SdS0R10S9S0RfG1A3A3M3S9S0ReRdA3M4A6S8dR1RaR9A6S19S58R1G4RcA3S19S59R1G4A2S5bR1G3A2A2A2A2Lrho2;A2F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Flb;Frest'';Fnxt;Fcur;Fpre;").
Proof.
  intros pre cur nxt rest'' lb rho tp w HPRE HGL HSZ H (E160 & E161 & E162 & E163 & E208) (E164 & E165) (E166 & E167 & E168 & E169 & E170).
  cbn [List.tl hd] in E164, E165. rewrite hd_addr_cons in E161, E164.
  destruct w as [tr [ms md]]. destruct (proj2 H) as (HK & (HBM & HTL & HLK & HTHD) & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HBM, HTL, HLK, HTHD, HFRM.
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  pose proof (benv_of_K _ _ _ _ HK) as BE.
  assert (HTL' : qlinks_to (view segsA (rm rho)) (removelast pre) (last_addr pre)) by (unfold tlinks in HTL; destruct pre; [congruence | exact HTL]).
  set (prv := last pre qb_dflt) in *. change (last_addr pre) with (qb_addr prv) in E166.
  assert (INP : forall b, In b pre -> In b (aa_q_global A1)) by (intros b Hb; rewrite HGL; apply in_or_app; left; exact Hb).
  assert (INR : forall b, In b (cur :: nxt :: rest'') -> In b (aa_q_global A1)) by (intros b Hb; rewrite HGL; apply in_or_app; right; exact Hb).
  assert (INPRV : In prv (aa_q_global A1)) by (apply INP; apply In_last; exact HPRE).
  assert (INC : In cur (aa_q_global A1)) by (apply INR; left; reflexivity).
  assert (INN : In nxt (aa_q_global A1)) by (apply INR; right; left; reflexivity).
  pose proof (NoDup_addr_all _ BE) as ND. rewrite HGL, map_app in ND.
  assert (NE : qb_addr cur <> qb_addr nxt).
  { pose proof (NoDup_app_r _ _ ND) as ND2. cbn [map] in ND2. inversion ND2 as [|x l Hn Hd]; subst. intros E. apply Hn. rewrite E. left. }
  assert (NPR : forall b, In b (cur :: nxt :: rest'') -> qb_addr b <> qb_addr prv).
  { intros b Hb E. apply (NoDup_app_disj _ _ (qb_addr prv) ND); [apply in_map; apply In_last; exact HPRE | rewrite <- E; apply in_map; exact Hb]. }
  destruct (batch_addr_facts _ prv BE INPRV) as (PA1 & PA2 & PA3 & PA4 & PA5). unfold HIGH_SHADOW_END in PA4.
  destruct (qsz_ge rho _ pre (cur :: nxt :: rest'') BE HBM HGL) as (S1 & S2 & S3). rewrite S3 in HSZ.
  assert (S2' : 8192 <= qb_size cur /\ 8192 * Z.of_nat (length (nxt :: rest'')) <= qsize (nxt :: rest'')).
  { pose proof HBM as HBM0. apply Forall_app in HBM as [_ HBM2]. destruct (qsz_ge rho (view segsA (rm rho)) (pre ++ [cur]) (nxt :: rest'') BE) as (_ & X2 & _).
    - rewrite <- app_assoc. cbn [app]. exact HBM0.
    - rewrite <- app_assoc. exact HGL.
    - split; [|exact X2]. pose proof (qsize_ge A1 (view segsA (rm rho)) [cur]) as Y. unfold qsize at 1 in Y. cbn [fold_right length] in Y. unfold kQuarantineBatchSize in Y.
      pose proof (proj1 (be_qp _ BE)) as HBP. rewrite qall_A1 in HBP.
      assert (P1 : Forall (batch_pure A1) [cur]) by (constructor; [exact (proj1 (Forall_forall _ _) HBP cur INC) | constructor]).
      assert (M1 : Forall (batch_mem (view segsA (rm rho))) [cur]) by (constructor; [exact (Forall_inv HBM2) | constructor]).
      specialize (Y P1 M1). lia. }
  rewrite (qsize_cons cur) in S2, HSZ, E163. destruct S2' as [SC SN].

  set (rho3 := rho_absorb rho [O_prv vCUR vPSZ] (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)).
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) _ [O_prv vCUR vPSZ] vPRV 0 16 _ Hsm Ck_objs ltac:(cbn; tauto) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
                ltac:(unfold vPRV; cbn [eval]; rewrite E166, u64_lit by lia; lia) ltac:(unfold vPRV; cbn [eval]; rewrite E166, u64_lit by lia; lia)) as [AV PR].
  fold rho3 v3 in AV, PR. unfold vPRV in AV, PR. cbn [eval] in AV, PR. rewrite E166, u64_lit in AV, PR by lia.
  assert (C_lnk : cell_ok v3 (mkACell (qb_addr prv) 8 (qb_addr cur))) by (replace (qb_addr prv) with (qb_addr prv + 0) at 1 by lia; exact (av_cell v3 (qb_addr prv) 0 8 _ _ rho (fun j => AV _ _ _ j (or_introl eq_refl)) E161)).
  assert (C_sz : cell_ok v3 (mkACell (qb_addr prv + 8) 8 (qb_size prv))) by exact (av_cell v3 (qb_addr prv) 8 8 _ _ rho (fun j => AV _ _ _ j (or_intror (or_introl eq_refl))) E167).
  clear AV.
  set (P := fun z : Z => qb_addr prv <= z < qb_addr prv + 16).
  assert (INRG : forall a, in_ranges rho [O_prv vCUR vPSZ] a -> P (bv_unsigned a)).
  { intros a (o & Ho & Hz). unfold P. destruct Ho as [<-|[]]. unfold O_prv, carved, vPRV in Hz. rewrite obj_range_mk in Hz by lia. cbn [fst snd eval] in Hz. rewrite E166, u64_lit in Hz by lia. lia. }
  destruct (absorb_out rho [O_prv vCUR vPSZ] (vms md tp ms) P INRG) as [FR FRrm]. fold rho3 v3 v in FR, FRrm.
  assert (HBMprv : batch_mem v prv) by (apply (proj1 (Forall_forall _ _) HBM); apply in_or_app; left; apply In_last; exact HPRE).
  assert (FR8 : forall z, ~ (qb_addr prv <= z < qb_addr prv + 8) -> v3 z = v z).
  { intros z Hz. destruct (Z_lt_dec z (qb_addr prv + 8)) as [|]; [apply FR; unfold P; lia|]. destruct (Z_lt_dec z (qb_addr prv + 16)) as [|]; [|apply FR; unfold P; lia].
    apply (cell_ok_same v v3 _ (proj1 HBMprv) C_sz). cbn [c_addr c_w]. lia. }
  destruct (K_FRM_absorb rho rho3 tp tr md P ltac:(intros z; unfold P; lia) ltac:(intros i; reflexivity) ltac:(intros l; reflexivity)) as [HK3 HF3]; try assumption.
  { intros z Hz. left. apply (batch_in_QW rho prv z BE INPRV). unfold P in Hz. lia. }
  { intros z Hz. destruct (PR z ltac:(unfold P in Hz; lia)) as [x Hx]. fold v3. rewrite Hx. discriminate. }
  assert (HR3 : RMEM v3 (aa_geom A1) (pre ++ [cur]) (nxt :: rest'')).
  { split; [|split; [|split]].
    - rewrite <- app_assoc. cbn [app]. apply Forall_forall. intros b Hb.
      assert (Hb' : In b (aa_q_global A1)) by (rewrite HGL; exact Hb).
      pose proof (proj1 (be_qp _ BE)) as HBP. rewrite qall_A1 in HBP.
      apply (batch_mem_frame A1 v v3 b (proj1 (Forall_forall _ _) HBP b Hb')); [|exact (proj1 (Forall_forall _ _) HBM b Hb)].
      intros z Hz. apply FR8. exact (bfoot_not_link rho b prv BE Hb' INPRV z Hz).
    - unfold tlinks. destruct (pre ++ [cur]) eqn:EPC; [destruct pre; discriminate|]. rewrite <- EPC. rewrite removelast_last. unfold last_addr. rewrite last_snoc.
      rewrite (app_removelast_last qb_dflt HPRE). fold prv. apply qlinks_to_app; [discriminate | | cbn; split; [exact C_lnk | exact I]].
      change (hd_addr [prv]) with (qb_addr prv).
      apply (qlinks_to_frame v v3); [|exact HTL']. intros b z Hb Hz. apply FR8. intros Hp.
      assert (Hb' : In b (aa_q_global A1)) by (apply INP; apply in_removelast_q; exact Hb).
      destruct (Z.eq_dec (qb_addr b) (qb_addr prv)) as [E|NEb]; [|pose proof (batches_apart1 _ b prv BE Hb' INPRV NEb); lia].
      pose proof (NoDup_app_l _ _ ND) as NDp. apply (removelast_not_last pre HPRE NDp). assert (EB : prv = b) by exact (batch_addr_inj _ _ _ BE INPRV Hb' (eq_sym E)). unfold prv in EB. rewrite EB. exact Hb.
    - apply qlinks_to_0. apply (qlinks_to_frame v v3 (nxt :: rest'') 0); [|apply qlinks_to_0; exact (proj2 HLK)].
      intros b z Hb Hz. apply FR8. intros Hp. apply (NPR b ltac:(right; exact Hb)).
      destruct (Z.eq_dec (qb_addr b) (qb_addr prv)) as [E|NEb]; [exact E|]. pose proof (batches_apart1 _ b prv BE (INR b ltac:(right; exact Hb)) INPRV NEb). lia.
    - destruct HTHD as (T0 & T1 & T2 & T3). assert (QF : forall z, ag_thread (aa_geom A1) + 80 <= z < ag_thread (aa_geom A1) + 112 -> v3 z = v z).
      { intros z Hz. apply FR8. intros Hp. apply (be_sep _ BE z); [|lia]. unfold q_foot. apply Exists_exists. exists prv. split; [rewrite HTH; exact INPRV|]. left. unfold kQuarantineBatchSize. lia. }
      split; [eapply cell_ok_frame1; [|exact T0]; cbn; intros z Hz; apply QF; lia|]. split; [intros X; exfalso; exact (X eq_refl)|].
      split; [eapply present_frame; [|exact T2]; intros z Hz; apply QF; lia | eapply cell_ok_frame1; [|exact T3]; cbn; intros z Hz; apply QF; lia]. }
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ (Contk true) rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ rho (Contk true) _ [O_prv vCUR vPSZ] tp tr ms md Ck_objs HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU.
  assert (H' : SPA segsA (JRQ K A0 rho0 A1 (pre ++ [cur]) (nxt :: rest'')) Ck0 rho3 tp (tr, mkCfg ms md)) by (split; [exact (proj1 HU) | exact (conj HK3 (conj HR3 HF3))]).
  pose proof (benv_of_K _ _ _ _ HK3) as BE3.
  destruct HLK as (CNc & CNn & HLK').
  assert (NNP : qb_addr nxt <> qb_addr prv) by (apply NPR; right; left; reflexivity).
  pose proof (batches_apart1 _ nxt prv BE INN INPRV NNP) as APn.
  assert (CNn' : cell_ok v3 (mkACell (qb_addr nxt) 8 (hd_addr rest''))).
  { eapply cell_ok_frame1; [|destruct rest''; exact CNn]. cbn. intros z Hz. apply FR8. lia. }
  assert (CSn : cell_ok v3 (mkACell (qb_addr nxt + 8) 8 (qb_size nxt))).
  { eapply cell_ok_frame1; [|exact (proj1 (proj1 (Forall_forall _ _) HBM nxt ltac:(apply in_or_app; right; right; left; reflexivity)))]. cbn. intros z Hz. apply FR8. lia. }
  destruct (batch_addr_facts _ nxt BE INN) as (BA1 & BA2 & BA3 & BA4 & BA5).
  set (rho1 := rho_sets rho3 [(198%positive, Z_to_bv 64 (hd_addr rest'')); (199%positive, Z_to_bv 64 (qb_size nxt))]).
  assert (OTH : forall i, i <> 198%positive -> i <> 199%positive -> rw rho1 i = rw rho i).
  { intros i N1 N2. unfold rho1. rewrite rho_sets_other by (cbn; intros [X|[X|[]]]; congruence). reflexivity. }
  assert (LEN : 2 <= Z.of_nat (length (cur :: nxt :: rest'')) < 2 ^ 60 /\ 1 <= Z.of_nat (length pre) < 2 ^ 60).
  { cbn [length] in S2, SN |- *. destruct pre; [congruence|]. cbn [length] in S1 |- *. lia. }
  assert (EN1 : eval rho1 (add vN (SLit (-1))) = Z_to_bv 64 (Z.of_nat (length (nxt :: rest'')))).
  { replace (Z.of_nat (length (nxt :: rest''))) with (Z.of_nat (length (cur :: nxt :: rest'')) + -1) by (cbn [length]; lia).
    apply eval_add_lit; [unfold vN; cbn [eval]; rewrite OTH by discriminate; exact E160 | lia | lia | lia]. }
  assert (ES' : eval rho1 s' = Z_to_bv 64 (qsize (nxt :: rest''))).
  { replace (qsize (nxt :: rest'')) with (qb_size cur + qsize (nxt :: rest'') - qb_size cur) by lia.
    apply eval_sub_z; [unfold vS; cbn [eval]; rewrite OTH by discriminate; exact E163 | unfold vCSZ; cbn [eval]; rewrite OTH by discriminate; exact E165 | lia | lia]. }
  assert (EK1 : eval rho1 (add vK (SLit 1)) = Z_to_bv 64 (Z.of_nat (length (pre ++ [cur])))).
  { rewrite length_app, Nat2Z.inj_add. cbn [length]. apply eval_add_lit; [unfold vK; cbn [eval]; rewrite OTH by discriminate; exact E168 | lia | lia | lia]. }
  assert (ETS : eval rho1 (add (SVar 170) vCSZ) = Z_to_bv 64 (qsize (pre ++ [cur]))).
  { rewrite qsize_app. replace (qsize [cur]) with (qb_size cur) by (unfold qsize; cbn [fold_right]; lia).
    apply eval_add_z; [cbn [eval]; rewrite OTH by discriminate; exact E170 | unfold vCSZ; cbn [eval]; rewrite OTH by discriminate; exact E165 | lia | lia | lia]. }
  destruct (new_glue _ Ck0 Ckb F_newk Mkg (sw_cells vJK (SVar 169) vJL (add (SVar 170) vCSZ)) _ _ _ _ cur nxt (hd_addr rest'') rho3 tp _
              (JRQ_stable K HL A0 rho0 A1 (pre ++ [cur]) (nxt :: rest'')) (proj1 Ck_vars) (proj2 Ck_vars) eq_refl Cka_swf Ckb_eq Ckc_below Ckc_ent eq_refl
              ltac:(intros r HF; unfold Ck0, Contk, mkR, F_Hk, F_H, F_H0 in HF; cbn [ax_S ax_setS mkA ss_facts set_objs] in HF; apply Forall_app in HF as [HF _]; apply Forall_app in HF as [HF _]; apply Forall_app in HF as [HF _]; apply Forall_app in HF as [HF _]; exact HF)
              H' BE3 INC INN NE E161 E164 CNn' CSn) as (rho2 & H2 & V2 & RM2).
  { fold rho1. unfold F_newk, F_new. repeat apply Forall_cons; try apply Forall_nil.
    - cbn [holds branch_taken]. rewrite EN1. cbn [eval]. unfold bv_eqb. rewrite !u64_lit by (cbn [length] in *; lia). intros E. apply Z.eqb_eq in E. cbn [length] in E. lia.
    - unfold vCN. cbn [holds eval]. rewrite OTH by discriminate. rewrite E164, !u64_lit by (unfold HIGH_SHADOW_END in *; lia). exact BA4.
    - cbn [holds]. split; [lia|]. rewrite OTH by discriminate. rewrite E164, u64_lit by lia.
      clear -BA5. pose proof (Z.div_mod (qb_addr nxt) 8192 ltac:(lia)) as D. rewrite BA5, Z.add_0_r in D. rewrite D. replace (8192 * (qb_addr nxt / 8192)) with (1024 * (qb_addr nxt / 8192) * 2 ^ 3) by lia. apply Z.mod_mul. lia.
    - cbn [holds branch_taken]. rewrite EK1. cbn [eval]. unfold bv_eqb. rewrite length_app, Nat2Z.inj_add. cbn [length]. rewrite !u64_lit by lia. intros E. apply Z.eqb_eq in E. lia. }
  fold rho1 in V2. exists rho2. split; [exact H2|].
  assert (VV : forall v e, In (v, e) Mkg -> rw rho2 v = eval rho1 e) by exact V2. clear V2.
  split; [|split].
  - unfold HVH. split; [rewrite (VV 160%positive _ ltac:(cbn; tauto)); exact EN1|].
    split; [rewrite (VV 161%positive _ ltac:(cbn; tauto)); unfold vCN; cbn [eval]; rewrite OTH by discriminate; exact E164|].
    split; [rewrite (VV 162%positive _ ltac:(cbn; tauto)); unfold vLB; cbn [eval]; rewrite OTH by discriminate; exact E162|].
    split; [rewrite (VV 163%positive _ ltac:(cbn; tauto)); exact ES'|].
    rewrite (VV 208%positive _ ltac:(cbn; tauto)). unfold vMIN. cbn [eval]. rewrite OTH by discriminate. exact E208.
  - unfold HVC. cbn [List.tl hd]. split; [rewrite (VV 164%positive _ ltac:(cbn; tauto)); reflexivity | rewrite (VV 165%positive _ ltac:(cbn; tauto)); reflexivity].
  - unfold HVT. unfold last_addr. rewrite last_snoc. rewrite (hd_addr_app pre [cur] HPRE).
    split; [rewrite (VV 166%positive _ ltac:(cbn; tauto)); unfold vCUR; cbn [eval]; rewrite OTH by discriminate; exact E161|].
    split; [rewrite (VV 167%positive _ ltac:(cbn; tauto)); unfold vCSZ; cbn [eval]; rewrite OTH by discriminate; exact E165|].
    split; [rewrite (VV 168%positive _ ltac:(cbn; tauto)); exact EK1|].
    split; [rewrite (VV 169%positive _ ltac:(cbn; tauto)); cbn [eval]; rewrite OTH by discriminate; exact E169|].
    rewrite (VV 170%positive _ ltac:(cbn; tauto)). exact ETS.
Qed.

Definition JRX (tmp rest : list qbatch) : jpredA := ltac2:(tb__ "0|0|
S20SaS4eQ40A1A1SaSc2A1Sc1S19VK;VA1;R4R3R2R1A5S19S7eS6aS47S24R4A1A2S4VA1;A1Vtmp;Vrest;A4S64VA0;Vrho0;R4A3A2A2Lmd;Ltr;Ltp;Lrho;").
Lemma JRX_stable : ltac2:(tb__ "0|1|
SaS0A1M0G0S57S47Sa9S5cR2R1A2A3Frest;Ftmp;").
Proof.
  intros tmp rest rho rho' tp tr md md' Hag Hme (HK & HR & HF).
  assert (Erm : rm rho' = rm rho) by (apply functional_extensionality; intros a; symmetry; apply (proj2 (proj2 Hag))).
  split; [eapply (kq_stable segsA K HL A1); eauto|]. split; [rewrite Erm; exact HR|].
  destruct HF as ((F1 & F1') & F2 & F3 & F4). split; [|rewrite Erm; auto].
  split; [intros i Hi; rewrite (F1 i Hi); apply (proj1 Hag); exact Hi | intros l; rewrite (F1' l); apply (proj1 (proj2 Hag))].
Qed.

Lemma bfoot_high : ltac2:(tb__ "0|0|
S20S0S1dS5aR3A1S5dS0R3S1VA1;A1A3S6fR4R3A2S3eZ646000R4A2F_;F_;F_;Fz;Fb;Frho;").
Proof.
  intros rho b z BE Hb Hz. destruct (batch_addr_facts _ b BE Hb) as (B1 & _). destruct Hz as [Hz|Hz]; [lia|].
  apply Exists_exists in Hz as (it & Hit & Hz). pose proof (proj1 (be_qp _ BE)) as HBP. rewrite qall_A1 in HBP.
  pose proof (proj1 (Forall_forall _ _) HBP b Hb) as (_ & _ & _ & HIP). pose proof (proj1 (Forall_forall _ _) HIP it Hit) as (IP1 & IP2 & _).
  pose proof (rz_facts (snd it)) as [RZ1 RZ2]. unfold IMG_HI in IP1. unfold ifoot, it_ab in Hz.
  assert (SHlo : 0x7fff8000 <= Sh (fst it)) by (unfold Sh, SHADOW_OFF; pose proof (Z.div_pos (fst it) 8 ltac:(lia) ltac:(lia)); lia).
  destruct Hz; lia.
Qed.

Lemma rmem2_of_exit : ltac2:(tb__ "0|9|
S20S6bS6bSaS0A1M0S0G0S1dS5aR7A1S18G0S1VA1;A1SdS0R5S9S0R4R3A3A3A3S66R8S4VA1;A1M1R6S9S0R5R4A3A4S1dS1aS1cS19S3eS3fSbaZa0A2M2R1A2S40R1S3fSbaZc0A2M3A2A2S1cS19S3eS2R7A1M4R1A2S40R1S3fG4Z8M5A2A2A2S19S1aS18G0R8ScS0A1M6A3A1S19S3eS6dR8A1M7R1A2S40R1S3fG7G5A2A2A2A2A2A2A1S18S12S4eQ8A1A1RaR2A1RbR2A1A3F_;Fz;S68R9S69G2U8M8S42S13S0R6A2A1A3A2S68RaS69S3fG2G5A2G8S6eR7A1A3A2S68RbS69S3fG2Z10A2G8R7A3A2S68RcS69S3fG2Z18A2G8S51R9A1A3A2S6cRdG2G3A3S1aS18G0RbG6A3A1S18S1dRbS6dRcA1A3F_;S68RfS69S2RdA1G8Z0A3A2S1aS18G0RfG6A3A1S68R11S69S6dR10A1G8S2RfA1A3A2F_;S7eR11G1SdS0R10S9S0RfG6A3A3ReA4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Flastv;Frest';Fcur;Fpre;Fv3;Fv;Frho;").
Proof.
  intros rho v v3 pre cur rest' lastv BE HGL (HBM & HTL & HLK & HTHD) FR C0 C1 C2 C3 PRH HLAST CC CP.
  assert (INA : forall b, In b (pre ++ cur :: rest') -> In b (aa_q_global A1)) by (intros b Hb; rewrite HGL; exact Hb).
  assert (INC : In cur (aa_q_global A1)) by (apply INA; apply in_or_app; right; left; reflexivity).
  pose proof (NoDup_addr_all _ BE) as ND. rewrite HGL, map_app in ND.
  assert (LNK : forall b, In b (aa_q_global A1) -> b <> cur -> (pre <> [] -> b <> last pre qb_dflt) -> forall z, qb_addr b <= z < qb_addr b + 8 -> v3 z = v z).
  { intros b Hb N1 N2 z Hz. apply FR. destruct (batch_addr_facts _ b BE Hb) as (B1 & _). unfold QG. intros [HP|[HP|[HPRE HP]]]; [lia | |].
    - destruct (Z.eq_dec (qb_addr b) (qb_addr cur)) as [E|NE]; [exact (N1 (batch_addr_inj _ _ _ BE Hb INC E)) | pose proof (batches_apart1 _ b cur BE Hb INC NE); lia].
    - assert (INPRV : In (last pre qb_dflt) (aa_q_global A1)) by (apply INA; apply in_or_app; left; apply In_last; exact HPRE).
      change (last_addr pre) with (qb_addr (last pre qb_dflt)) in HP.
      destruct (Z.eq_dec (qb_addr b) (qb_addr (last pre qb_dflt))) as [E|NE]; [exact (N2 HPRE (batch_addr_inj _ _ _ BE Hb INPRV E)) | pose proof (batches_apart1 _ b _ BE Hb INPRV NE); lia]. }
  split; [|split; [|split; [|split]]].
  - rewrite <- app_assoc. cbn [app]. apply Forall_forall. intros b Hb. pose proof (INA b Hb) as Hb'.
    pose proof (proj1 (be_qp _ BE)) as HBP. rewrite qall_A1 in HBP.
    apply (batch_mem_frame A1 v v3 b (proj1 (Forall_forall _ _) HBP b Hb')); [|exact (proj1 (Forall_forall _ _) HBM b Hb)].
    intros z Hz. apply FR. pose proof (bfoot_high rho b z BE Hb' Hz) as ZH. unfold QG. intros [HP|[HP|[HPRE HP]]]; [lia | exact (bfoot_not_link rho b cur BE Hb' INC z Hz HP) |].
    assert (INPRV : In (last pre qb_dflt) (aa_q_global A1)) by (apply INA; apply in_or_app; left; apply In_last; exact HPRE).
    exact (bfoot_not_link rho b _ BE Hb' INPRV z Hz HP).
  - apply qlinks_to_0. apply (tlinks_snoc v v3 pre cur 0); [| exact CP | exact HTL | exact CC].
    intros b z Hb Hz. assert (Hb' : In b pre) by (apply in_removelast_q; exact Hb). apply (LNK b (INA b (in_or_app _ _ _ (or_introl Hb')))); [| | exact Hz].
    + intros E. subst b. apply (NoDup_app_disj _ _ (qb_addr cur) ND); [apply in_map; exact Hb' | left; reflexivity].
    + intros HPRE E. subst b. exact (removelast_not_last pre HPRE (NoDup_app_l _ _ ND) Hb).
  - apply qlinks_to_0. apply (qlinks_to_frame v v3 rest' 0); [|apply qlinks_to_0; cbn [qlinks] in HLK; exact (proj2 HLK)].
    intros b z Hb Hz. apply (LNK b (INA b (in_or_app pre (cur :: rest') b (or_intror (or_intror Hb))))); [| | exact Hz].
    + intros E. subst b. pose proof (NoDup_app_r _ _ ND) as ND2. cbn [map] in ND2. inversion ND2 as [|x l Hn Hd]; subst. apply Hn. apply list_elem_of_In. apply in_map. exact Hb.
    + intros HPRE E. subst b. apply (NoDup_app_disj _ _ (qb_addr (last pre qb_dflt)) ND); [apply in_map; apply In_last; exact HPRE | right; apply in_map; exact Hb].
  - destruct HTHD as (T0 & T1 & T2 & T3). assert (QF : forall z, ag_thread (aa_geom A1) + 80 <= z < ag_thread (aa_geom A1) + 112 -> v3 z = v z).
    { intros z Hz. apply FR. pose proof (geom_bands _ (be_geom _ BE)) as (_ & _ & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI. pose proof (geom_old _ (be_geom _ BE)) as (_ & _ & _ & _ & G5 & _).
      unfold QG. intros [HP|[HP|[HPRE HP]]]; [lia | |].
      - apply (be_sep _ BE z); [|lia]. unfold q_foot. apply Exists_exists. exists cur. split; [rewrite HTH; exact INC|]. left. unfold kQuarantineBatchSize. lia.
      - apply (be_sep _ BE z); [|lia]. unfold q_foot. apply Exists_exists. exists (last pre qb_dflt). split; [rewrite HTH; apply INA; apply in_or_app; left; apply In_last; exact HPRE|].
        left. unfold kQuarantineBatchSize. change (last_addr pre) with (qb_addr (last pre qb_dflt)) in HP. lia. }
    split; [eapply cell_ok_frame1; [|exact T0]; cbn; intros z Hz; apply QF; lia|]. split; [intros X; exfalso; exact (X eq_refl)|].
    split; [eapply present_frame; [|exact T2]; intros z Hz; apply QF; lia | eapply cell_ok_frame1; [|exact T3]; cbn; intros z Hz; apply QF; lia].
  - unfold qhdr_repr. split; [exact C0|]. split; [|split; [intros z Hz; apply PRH; lia | exact C3]].
    intros NE. split; [exact C1|]. change (qb_addr (last rest' qb_dflt)) with (last_addr rest'). rewrite <- (HLAST NE). exact C2.
Qed.

Lemma exitk_glue : ltac2:(tb__ "0|4|
SeSaS0A1M0S0G0S1dS20SaS4eQ40A1A1S72S1aS18G0R7ScS0A1M1A3A1S18G0S1VA1;A1M2SdS0R8S9S0R7R6A3A3A3S40S51G2A1S41Z2Z3eA2A2S18S1dR7S6dG2A1A3S55S47S63VK;VA0;Vrho0;VA1;RbS9S0RaR9A3A6S94RcA1R7R6R5A6S58R8S9S0RbRaA3R9A3S59R9S9S0RcRbA3A2S5bRaReA2S1bS20S20S19S55S47S5cSdS0R10S9S0RfG1A3A3M3ReA2S8eR1RbRaA6S19S77R1G3A2S3eS51ReA1SaaA2A2A2Lrho2;A2F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Flb;Frest';Fcur;Fpre;Fnz;").
Proof.
  intros nz pre cur rest' lb rho tp w HPRE HGL HSZ HLB H (E160 & E161 & E162 & E163 & E208) (E164 & E165) (E166 & E167 & E168 & E169 & E170).
  cbn [List.tl hd] in E164, E165. rewrite hd_addr_cons in E161.
  destruct w as [tr [ms md]]. destruct (proj2 H) as (HK & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HRM, HFRM. pose proof HRM as (HBM & HTL & HLK & HTHD).
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  pose proof (benv_of_K _ _ _ _ HK) as BE.
  set (prv := last pre qb_dflt) in *. change (last_addr pre) with (qb_addr prv) in E166.
  assert (INA : forall b, In b (pre ++ cur :: rest') -> In b (aa_q_global A1)) by (intros b Hb; rewrite HGL; exact Hb).
  assert (INPRV : In prv (aa_q_global A1)) by (apply INA; apply in_or_app; left; apply In_last; exact HPRE).
  assert (INC : In cur (aa_q_global A1)) by (apply INA; apply in_or_app; right; left; reflexivity).
  destruct (batch_addr_facts _ prv BE INPRV) as (PA1 & PA2 & PA3 & PA4 & PA5). destruct (batch_addr_facts _ cur BE INC) as (CA1 & CA2 & CA3 & CA4 & CA5). unfold HIGH_SHADOW_END in PA4, CA4.
  destruct (qsz_ge rho _ pre (cur :: rest') BE HBM HGL) as (S1 & S2 & S3). rewrite S3 in HSZ.
  assert (SC : 8192 <= qb_size cur /\ 0 <= qsize rest').
  { destruct (qsz_ge rho (view segsA (rm rho)) (pre ++ [cur]) rest' BE) as (_ & X2 & _); [rewrite <- app_assoc; exact HBM | rewrite <- app_assoc; exact HGL |].
    split; [|lia]. pose proof (qsize_ge A1 (view segsA (rm rho)) [cur]) as Y. unfold qsize at 1 in Y. cbn [fold_right length] in Y. unfold kQuarantineBatchSize in Y.
    pose proof (proj1 (be_qp _ BE)) as HBP. rewrite qall_A1 in HBP.
    assert (P1 : Forall (batch_pure A1) [cur]) by (constructor; [exact (proj1 (Forall_forall _ _) HBP cur INC) | constructor]).
    assert (M1 : Forall (batch_mem (view segsA (rm rho))) [cur]) by (constructor; [exact (proj1 (Forall_forall _ _) HBM cur ltac:(apply in_or_app; right; left; reflexivity)) | constructor]).
    specialize (Y P1 M1). lia. }
  rewrite (qsize_cons cur) in S2, HSZ, E163. destruct SC as [SC SR].
  assert (LEN : 1 <= Z.of_nat (length (cur :: rest')) < 2 ^ 60 /\ 1 <= Z.of_nat (length pre) < 2 ^ 60).
  { cbn [length] in S2 |- *. destruct pre; [congruence|]. cbn [length] in S1 |- *. lia. }

  pose proof (SPA_facts_hold segsA _ rho (Exitk nz) tp _ H) as HFa.
  assert (ES' : eval rho s' = Z_to_bv 64 (qsize rest')).
  { replace (qsize rest') with (qb_size cur + qsize rest' - qb_size cur) by lia. apply eval_sub_z; [exact E163 | exact E165 | lia | lia]. }
  assert (FSTOP : qsize rest' <= kQuarantineMin).
  { assert (X : holds rho F_stop) by (apply (proj1 (Forall_forall _ _) HFa); unfold Exitk, mkR; cbn [ax_S mkA ss_facts]; apply in_or_app; right; left; reflexivity).
    unfold F_stop in X. cbn [holds branch_taken] in X. rewrite ES' in X. unfold vMIN in X. cbn [eval] in X. rewrite E208 in X.
    apply negb_true_iff in X. unfold bv_ltu in X. apply Z.ltb_ge in X. rewrite !u64_lit in X by (unfold kQuarantineMin; lia). exact X. }
  assert (FNZ : holds rho (F_nz nz)) by (apply (proj1 (Forall_forall _ _) HFa); unfold Exitk, mkR; cbn [ax_S mkA ss_facts]; apply in_or_app; right; right; left; reflexivity).
  assert (HLASTV : rest' <> [] -> (if nz then lb else 0) = last_addr rest').
  { intros NE. destruct rest' as [|r0 rest'']; [congruence|]. cbn [List.tl] in E164. rewrite hd_addr_cons in E164.
    destruct (batch_addr_facts _ r0 BE ltac:(apply INA; apply in_or_app; right; right; left; reflexivity)) as (RA1 & _ & RA3 & _).
    destruct nz.
    - rewrite HLB, HGL. unfold last_addr. rewrite last_app_ne by discriminate. reflexivity.
    - exfalso. unfold F_nz in FNZ. cbn [holds branch_taken] in FNZ. apply FNZ. unfold vCN. cbn [eval]. rewrite E164. apply negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. rewrite !u64_lit by lia. lia. }

  set (REST := [O_gqC nz; O_cur ZQ vCSZ; O_prv vCUR vPSZ]).
  set (rho3 := rho_absorb rho REST (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)).
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) _ REST (SLit 0) (QG + 160) (QG + 192) _ Hsm (Ek_objs nz) ltac:(left; reflexivity) ltac:(unfold QG; lia) ltac:(lia) ltac:(unfold QG; lia)
                ltac:(unfold cells_inside, QG; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia)) as [AVg PRg].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) _ REST vCUR 0 16 _ Hsm (Ek_objs nz) ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
                ltac:(unfold vCUR; cbn [eval]; rewrite E161, u64_lit by lia; lia) ltac:(unfold vCUR; cbn [eval]; rewrite E161, u64_lit by lia; lia)) as [AVc PRc].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) _ REST vPRV 0 16 _ Hsm (Ek_objs nz) ltac:(right; right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
                ltac:(unfold vPRV; cbn [eval]; rewrite E166, u64_lit by lia; lia) ltac:(unfold vPRV; cbn [eval]; rewrite E166, u64_lit by lia; lia)) as [AVp PRp].
  fold rho3 v3 in AVg, PRg, AVc, PRc, AVp, PRp. cbn [eval] in AVg, PRg. rewrite u64_lit in AVg, PRg by lia.
  unfold vCUR in AVc, PRc. unfold vPRV in AVp, PRp. cbn [eval] in AVc, PRc, AVp, PRp. rewrite E161, u64_lit in AVc, PRc by lia. rewrite E166, u64_lit in AVp, PRp by lia.
  assert (EN1 : eval rho (add vN (SLit (-1))) = Z_to_bv 64 (Z.of_nat (length rest'))).
  { replace (Z.of_nat (length rest')) with (Z.of_nat (length (cur :: rest')) + -1) by (cbn [length]; lia). apply eval_add_lit; [exact E160 | lia | lia | lia]. }
  assert (ELV : eval rho (if nz then vLB else ZQ) = Z_to_bv 64 (if nz then lb else 0)) by (destruct nz; [exact E162 | reflexivity]).
  assert (C_g0 : cell_ok v3 (mkACell (QG + 160) 8 (Z.of_nat (length rest')))) by (replace (QG + 160) with (0 + (QG + 160)) by lia; exact (av_cell v3 0 (QG + 160) 8 _ _ rho (fun j => AVg _ _ _ j (or_introl eq_refl)) EN1)).
  assert (C_g1 : cell_ok v3 (mkACell (QG + 160 + 8) 8 (hd_addr rest'))) by (replace (QG + 160 + 8) with (0 + (QG + 168)) by lia; exact (av_cell v3 0 (QG + 168) 8 _ _ rho (fun j => AVg _ _ _ j (or_intror (or_introl eq_refl))) E164)).
  assert (C_g2 : cell_ok v3 (mkACell (QG + 160 + 16) 8 (if nz then lb else 0))) by (replace (QG + 160 + 16) with (0 + (QG + 176)) by lia; exact (av_cell v3 0 (QG + 176) 8 _ _ rho (fun j => AVg _ _ _ j (or_intror (or_intror (or_introl eq_refl)))) ELV)).
  assert (C_g3 : cell_ok v3 (mkACell (QG + 160 + 24) 8 (qsize rest'))) by (replace (QG + 160 + 24) with (0 + (QG + 184)) by lia; exact (av_cell v3 0 (QG + 184) 8 _ _ rho (fun j => AVg _ _ _ j (or_intror (or_intror (or_intror (or_introl eq_refl))))) ES')).
  assert (C_c0 : cell_ok v3 (mkACell (qb_addr cur) 8 0)) by (replace (qb_addr cur) with (qb_addr cur + 0) at 1 by lia; exact (av_cell v3 (qb_addr cur) 0 8 ZQ 0 rho (fun j => AVc _ _ _ j (or_introl eq_refl)) eq_refl)).
  assert (C_c1 : cell_ok v3 (mkACell (qb_addr cur + 8) 8 (qb_size cur))) by exact (av_cell v3 (qb_addr cur) 8 8 _ _ rho (fun j => AVc _ _ _ j (or_intror (or_introl eq_refl))) E165).
  assert (C_p0 : cell_ok v3 (mkACell (qb_addr prv) 8 (qb_addr cur))) by (replace (qb_addr prv) with (qb_addr prv + 0) at 1 by lia; exact (av_cell v3 (qb_addr prv) 0 8 _ _ rho (fun j => AVp _ _ _ j (or_introl eq_refl)) E161)).
  assert (C_p1 : cell_ok v3 (mkACell (qb_addr prv + 8) 8 (qb_size prv))) by exact (av_cell v3 (qb_addr prv) 8 8 _ _ rho (fun j => AVp _ _ _ j (or_intror (or_introl eq_refl))) E167).
  clear AVg AVc AVp.
  set (P := fun z : Z => QG + 160 <= z < QG + 192 \/ qb_addr cur <= z < qb_addr cur + 16 \/ qb_addr prv <= z < qb_addr prv + 16).
  assert (INRG : forall a, in_ranges rho REST a -> P (bv_unsigned a)).
  { intros a (o & Ho & Hz). unfold P. destruct Ho as [<-|[<-|[<-|[]]]]; unfold O_gqC, O_gq, O_cur, O_prv, carved, vCUR, vPRV in Hz; rewrite obj_range_mk in Hz by (unfold QG; lia);
      cbn [fst snd eval] in Hz; rewrite ?E161, ?E166, ?u64_lit in Hz by lia; lia. }
  destruct (absorb_out rho REST (vms md tp ms) P INRG) as [FR FRrm]. fold rho3 v3 v in FR, FRrm.
  assert (FRL : forall z, ~ (QG + 160 <= z < QG + 192 \/ qb_addr cur <= z < qb_addr cur + 8 \/ (pre <> [] /\ last_addr pre <= z < last_addr pre + 8)) -> v3 z = v z).
  { intros z Hz. change (last_addr pre) with (qb_addr prv) in Hz.
    destruct (Z_le_dec (qb_addr cur + 8) z) as [L1|]; [destruct (Z_lt_dec z (qb_addr cur + 16)) as [L2|]|].
    - apply (cell_ok_same v v3 _ (proj1 (proj1 (Forall_forall _ _) HBM cur ltac:(apply in_or_app; right; left; reflexivity))) C_c1). cbn [c_addr c_w]. lia.
    - destruct (Z_le_dec (qb_addr prv + 8) z) as [L3|]; [destruct (Z_lt_dec z (qb_addr prv + 16)) as [L4|]|].
      + apply (cell_ok_same v v3 _ (proj1 (proj1 (Forall_forall _ _) HBM prv ltac:(apply in_or_app; left; apply In_last; exact HPRE))) C_p1). cbn [c_addr c_w]. lia.
      + apply FR. unfold P. intros [X|[X|X]]; [apply Hz; left; exact X | lia | lia].
      + apply FR. unfold P. intros [X|[X|X]]; [apply Hz; left; exact X | lia | apply Hz; right; right; split; [exact HPRE | lia]].
    - destruct (Z_le_dec (qb_addr prv + 8) z) as [L3|]; [destruct (Z_lt_dec z (qb_addr prv + 16)) as [L4|]|].
      + apply (cell_ok_same v v3 _ (proj1 (proj1 (Forall_forall _ _) HBM prv ltac:(apply in_or_app; left; apply In_last; exact HPRE))) C_p1). cbn [c_addr c_w]. lia.
      + apply FR. unfold P. intros [X|[X|X]]; [apply Hz; left; exact X | apply Hz; right; left; lia | lia].
      + apply FR. unfold P. intros [X|[X|X]]; [apply Hz; left; exact X | apply Hz; right; left; lia | apply Hz; right; right; split; [exact HPRE | lia]]. }
  destruct (K_FRM_absorb rho rho3 tp tr md P ltac:(intros z; unfold P; lia) ltac:(intros i; reflexivity) ltac:(intros l; reflexivity)) as [HK3 HF3]; try assumption.
  { intros z Hz. left. unfold P in Hz. destruct Hz as [Hz|[Hz|Hz]].
    - split; [right; left; right; right; exact Hz | unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, QG in *; lia].
    - apply (batch_in_QW rho cur z BE INC). lia.
    - apply (batch_in_QW rho prv z BE INPRV). lia. }
  { intros z Hz. unfold P in Hz. fold v3. destruct Hz as [Hz|[Hz|Hz]]; [destruct (PRg z ltac:(lia)) as [x Hx] | destruct (PRc z ltac:(lia)) as [x Hx] | destruct (PRp z ltac:(lia)) as [x Hx]]; rewrite Hx; discriminate. }
  pose proof (rmem2_of_exit rho v v3 pre cur rest' (if nz then lb else 0) BE HGL HRM FRL C_g0 C_g1 C_g2 C_g3 ltac:(intros z Hz; apply PRg; lia) HLASTV C_c0 ltac:(intros _; exact C_p0)) as HR3.
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ (Exitk nz) rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ rho (Exitk nz) _ REST tp tr ms md (Ek_objs nz) HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU.
  assert (H' : SPA segsA (JRX (pre ++ [cur]) rest') (Ekx nz) rho3 tp (tr, mkCfg ms md)) by (split; [exact (proj1 HU) | exact (conj HK3 (conj HR3 HF3))]).
  destruct (entM_SPA _ (Ekx nz) Xg MXk rho3 tp _ (Ekx_ent nz) (JRX_stable _ _) H') as (H5 & AG5 & V5 & RM5).
  eexists. split; [exact H5|]. split; [|exact FSTOP].
  unfold HVX. unfold last_addr. rewrite last_snoc. rewrite (hd_addr_app pre [cur] HPRE).
  split; [rewrite (V5 184%positive _ ltac:(cbn; tauto)); rewrite length_app, Nat2Z.inj_add; cbn [length]; apply eval_add_lit; [exact E168 | lia | lia | lia]|].
  split; [rewrite (V5 185%positive _ ltac:(cbn; tauto)); exact E169|].
  split; [rewrite (V5 186%positive _ ltac:(cbn; tauto)); exact E161|].
  split; [rewrite (V5 187%positive _ ltac:(cbn; tauto)); rewrite qsize_app; replace (qsize [cur]) with (qb_size cur) by (unfold qsize; cbn [fold_right]; lia); apply eval_add_z; [exact E170 | exact E165 | lia | lia | lia]|].
  rewrite (V5 208%positive _ ltac:(cbn; tauto)). exact E208.
Qed.

Lemma exit0_glue : ltac2:(tb__ "0|4|
SeS0SaS0A1M0S1dS20SaS4eQ40A1A1S72S18G0S1VA1;A1M1S9S0R6R5A3A3S40S51G1A1S41Z2Z3eA2A2S18S1dR6S6dG1A1A3S55S47S63VK;VA0;Vrho0;VA1;ScS0A1M2S9S0R9R8A3A6S93RaA1R6R5R4A6S58R7S9S0RaR9A3R8A3S59R8S9S0RbRaA3A2S1bS20S20S19S55S47S5cS9S0RdG2A3M3RcA2S8eR1R9R8A6S19S77R1G3A2S3eS51RcA1SaaA2A2A2Lrho2;A2F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Flb;Frest';Fcur;Fnz;").
Proof.
  intros nz cur rest' lb rho tp w HGL HSZ HLB H (E160 & E161 & E162 & E163 & E208) (E164 & E165).
  cbn [List.tl hd] in E164, E165. rewrite hd_addr_cons in E161.
  destruct w as [tr [ms md]]. destruct (proj2 H) as (HK & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HRM, HFRM. pose proof HRM as (HBM & HTL & HLK & HTHD).
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  pose proof (benv_of_K _ _ _ _ HK) as BE. cbn [app] in HBM.
  assert (INA : forall b, In b (cur :: rest') -> In b (aa_q_global A1)) by (intros b Hb; rewrite HGL; exact Hb).
  assert (INC : In cur (aa_q_global A1)) by (apply INA; left; reflexivity).
  destruct (batch_addr_facts _ cur BE INC) as (CA1 & CA2 & CA3 & CA4 & CA5). unfold HIGH_SHADOW_END in CA4.
  destruct (qsz_ge rho _ [cur] rest' BE HBM HGL) as (S1 & S2 & S3). rewrite S3 in HSZ.
  assert (Q1 : qsize [cur] = qb_size cur) by (unfold qsize; cbn [fold_right]; lia). rewrite Q1 in *. clear Q1. cbn [length] in S1.
  rewrite (qsize_cons cur) in E163.
  assert (LEN : 1 <= Z.of_nat (length (cur :: rest')) < 2 ^ 60) by (cbn [length] in *; lia).
  pose proof (SPA_facts_hold segsA _ rho (Exit0 nz) tp _ H) as HFa.
  assert (ES' : eval rho s' = Z_to_bv 64 (qsize rest')).
  { replace (qsize rest') with (qb_size cur + qsize rest' - qb_size cur) by lia. apply eval_sub_z; [exact E163 | exact E165 | lia | lia]. }
  assert (FSTOP : qsize rest' <= kQuarantineMin).
  { assert (X : holds rho F_stop) by (apply (proj1 (Forall_forall _ _) HFa); unfold Exit0, mkR; cbn [ax_S mkA ss_facts]; apply in_or_app; right; left; reflexivity).
    unfold F_stop in X. cbn [holds branch_taken] in X. rewrite ES' in X. unfold vMIN in X. cbn [eval] in X. rewrite E208 in X.
    apply negb_true_iff in X. unfold bv_ltu in X. apply Z.ltb_ge in X. rewrite !u64_lit in X by (unfold kQuarantineMin; lia). exact X. }
  assert (FNZ : holds rho (F_nz nz)) by (apply (proj1 (Forall_forall _ _) HFa); unfold Exit0, mkR; cbn [ax_S mkA ss_facts]; apply in_or_app; right; right; left; reflexivity).
  assert (HLASTV : rest' <> [] -> (if nz then lb else 0) = last_addr rest').
  { intros NE. destruct rest' as [|r0 rest'']; [congruence|]. cbn [List.tl] in E164. rewrite hd_addr_cons in E164.
    destruct (batch_addr_facts _ r0 BE ltac:(apply INA; right; left; reflexivity)) as (RA1 & _ & RA3 & _).
    destruct nz.
    - rewrite HLB, HGL. unfold last_addr. reflexivity.
    - exfalso. unfold F_nz in FNZ. cbn [holds branch_taken] in FNZ. apply FNZ. unfold vCN. cbn [eval]. rewrite E164. apply negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. rewrite !u64_lit by lia. lia. }
  set (REST := [O_gqC nz; O_cur ZQ vCSZ]).
  set (rho3 := rho_absorb rho REST (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)).
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) _ REST (SLit 0) (QG + 160) (QG + 192) _ Hsm (E0_objs nz) ltac:(left; reflexivity) ltac:(unfold QG; lia) ltac:(lia) ltac:(unfold QG; lia)
                ltac:(unfold cells_inside, QG; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia) ltac:(cbn [eval]; rewrite u64_lit by lia; unfold QG; lia)) as [AVg PRg].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) _ REST vCUR 0 16 _ Hsm (E0_objs nz) ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia)
                ltac:(unfold vCUR; cbn [eval]; rewrite E161, u64_lit by lia; lia) ltac:(unfold vCUR; cbn [eval]; rewrite E161, u64_lit by lia; lia)) as [AVc PRc].
  fold rho3 v3 in AVg, PRg, AVc, PRc. cbn [eval] in AVg, PRg. rewrite u64_lit in AVg, PRg by lia.
  unfold vCUR in AVc, PRc. cbn [eval] in AVc, PRc. rewrite E161, u64_lit in AVc, PRc by lia.
  assert (EN1 : eval rho (add vN (SLit (-1))) = Z_to_bv 64 (Z.of_nat (length rest'))).
  { replace (Z.of_nat (length rest')) with (Z.of_nat (length (cur :: rest')) + -1) by (cbn [length]; lia). apply eval_add_lit; [exact E160 | lia | lia | lia]. }
  assert (ELV : eval rho (if nz then vLB else ZQ) = Z_to_bv 64 (if nz then lb else 0)) by (destruct nz; [exact E162 | reflexivity]).
  assert (C_g0 : cell_ok v3 (mkACell (QG + 160) 8 (Z.of_nat (length rest')))) by (replace (QG + 160) with (0 + (QG + 160)) by lia; exact (av_cell v3 0 (QG + 160) 8 _ _ rho (fun j => AVg _ _ _ j (or_introl eq_refl)) EN1)).
  assert (C_g1 : cell_ok v3 (mkACell (QG + 160 + 8) 8 (hd_addr rest'))) by (replace (QG + 160 + 8) with (0 + (QG + 168)) by lia; exact (av_cell v3 0 (QG + 168) 8 _ _ rho (fun j => AVg _ _ _ j (or_intror (or_introl eq_refl))) E164)).
  assert (C_g2 : cell_ok v3 (mkACell (QG + 160 + 16) 8 (if nz then lb else 0))) by (replace (QG + 160 + 16) with (0 + (QG + 176)) by lia; exact (av_cell v3 0 (QG + 176) 8 _ _ rho (fun j => AVg _ _ _ j (or_intror (or_intror (or_introl eq_refl)))) ELV)).
  assert (C_g3 : cell_ok v3 (mkACell (QG + 160 + 24) 8 (qsize rest'))) by (replace (QG + 160 + 24) with (0 + (QG + 184)) by lia; exact (av_cell v3 0 (QG + 184) 8 _ _ rho (fun j => AVg _ _ _ j (or_intror (or_intror (or_intror (or_introl eq_refl))))) ES')).
  assert (C_c0 : cell_ok v3 (mkACell (qb_addr cur) 8 0)) by (replace (qb_addr cur) with (qb_addr cur + 0) at 1 by lia; exact (av_cell v3 (qb_addr cur) 0 8 ZQ 0 rho (fun j => AVc _ _ _ j (or_introl eq_refl)) eq_refl)).
  assert (C_c1 : cell_ok v3 (mkACell (qb_addr cur + 8) 8 (qb_size cur))) by exact (av_cell v3 (qb_addr cur) 8 8 _ _ rho (fun j => AVc _ _ _ j (or_intror (or_introl eq_refl))) E165).
  clear AVg AVc.
  set (P := fun z : Z => QG + 160 <= z < QG + 192 \/ qb_addr cur <= z < qb_addr cur + 16).
  assert (INRG : forall a, in_ranges rho REST a -> P (bv_unsigned a)).
  { intros a (o & Ho & Hz). unfold P. destruct Ho as [<-|[<-|[]]]; unfold O_gqC, O_gq, O_cur, carved, vCUR in Hz; rewrite obj_range_mk in Hz by (unfold QG; lia);
      cbn [fst snd eval] in Hz; rewrite ?E161, ?u64_lit in Hz by lia; lia. }
  destruct (absorb_out rho REST (vms md tp ms) P INRG) as [FR FRrm]. fold rho3 v3 v in FR, FRrm.
  assert (FRL : forall z, ~ (QG + 160 <= z < QG + 192 \/ qb_addr cur <= z < qb_addr cur + 8 \/ (@nil qbatch <> [] /\ last_addr [] <= z < last_addr [] + 8)) -> v3 z = v z).
  { intros z Hz. destruct (Z_le_dec (qb_addr cur + 8) z) as [L1|]; [destruct (Z_lt_dec z (qb_addr cur + 16)) as [L2|]|].
    - apply (cell_ok_same v v3 _ (proj1 (Forall_inv HBM)) C_c1). cbn [c_addr c_w]. lia.
    - apply FR. unfold P. intros [X|X]; [apply Hz; left; exact X | lia].
    - apply FR. unfold P. intros [X|X]; [apply Hz; left; exact X | apply Hz; right; left; lia]. }
  destruct (K_FRM_absorb rho rho3 tp tr md P ltac:(intros z; unfold P; lia) ltac:(intros i; reflexivity) ltac:(intros l; reflexivity)) as [HK3 HF3]; try assumption.
  { intros z Hz. left. unfold P in Hz. destruct Hz as [Hz|Hz].
    - split; [right; left; right; right; exact Hz | unfold SHADOW_BAND_LO, LOW_SHADOW_BEG, QG in *; lia].
    - apply (batch_in_QW rho cur z BE INC). lia. }
  { intros z Hz. unfold P in Hz. fold v3. destruct Hz as [Hz|Hz]; [destruct (PRg z ltac:(lia)) as [x Hx] | destruct (PRc z ltac:(lia)) as [x Hx]]; rewrite Hx; discriminate. }
  pose proof (rmem2_of_exit rho v v3 [] cur rest' (if nz then lb else 0) BE HGL HRM FRL C_g0 C_g1 C_g2 C_g3 ltac:(intros z Hz; apply PRg; lia) HLASTV C_c0 ltac:(intros X; congruence)) as HR3.
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ (Exit0 nz) rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ rho (Exit0 nz) _ REST tp tr ms md (E0_objs nz) HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU.
  assert (H' : SPA segsA (JRX [cur] rest') (E0x nz) rho3 tp (tr, mkCfg ms md)) by (split; [exact (proj1 HU) | exact (conj HK3 (conj HR3 HF3))]).
  destruct (entM_SPA _ (E0x nz) Xg MX0 rho3 tp _ (E0x_ent nz) (JRX_stable _ _) H') as (H5 & AG5 & V5 & RM5).
  eexists. split; [exact H5|]. split; [|exact FSTOP].
  unfold HVX. unfold last_addr. cbn [last length]. rewrite hd_addr_cons.
  split; [rewrite (V5 184%positive _ ltac:(cbn; tauto)); reflexivity|].
  split; [rewrite (V5 185%positive _ ltac:(cbn; tauto)); exact E161|].
  split; [rewrite (V5 186%positive _ ltac:(cbn; tauto)); exact E161|].
  split; [rewrite (V5 187%positive _ ltac:(cbn; tauto)); replace (qsize [cur]) with (qb_size cur) by (unfold qsize; cbn [fold_right]; lia); exact E165|].
  rewrite (V5 208%positive _ ltac:(cbn; tauto)). exact E208.
Qed.

Lemma keepsM_id : ltac2:(tb__ "0|0|
SaS1eA1S20S20S1eSb2Sd7R4A1R3R2A3S5dS1eR2R5A3S18S4eQ40A1S22R4R3A2S22R5R3A2A3F_;F_;Fv;Frho';Frho;Fl;").
Proof. intros l rho rho' v [_ HV] Hin. rewrite (HV v (SVar v)); [reflexivity|]. unfold idm. apply in_map_iff. exists v. split; [reflexivity | exact Hin]. Qed.
Lemma HV_keep_k : ltac2:(tb__ "0|1|
S20S20SaS0A1M0G0S1dSb2Sd5R5R4A3S58R6R3R2A3S59R7R4A2S5bR8R6A2S19S58R8R6R5A3S19S59R8R6A2S5bR8R7A2A2A2F_;F_;F_;F_;Flb;Frest;Fpre;Frho';Frho;").
Proof.
  intros rho rho' pre rest lb HKp (E160 & E161 & E162 & E163 & E208) (E164 & E165) (E166 & E167 & E168 & E169 & E170).
  unfold HVH, HVC, HVT. rewrite !(keepsM_id _ rho rho' _ HKp) by (cbn; tauto). tauto.
Qed.
Lemma HV_keep_0 : ltac2:(tb__ "0|0|
S20S20SaS0A1S1dSb2Sd4R4R3A3S58R5R3R2A3S59R6R4A2S19S58R6R5R4A3S59R6R5A2A2F_;F_;F_;Flb;Frest;Frho';Frho;").
Proof.
  intros rho rho' rest lb HKp (E160 & E161 & E162 & E163 & E208) (E164 & E165).
  unfold HVH, HVC. rewrite !(keepsM_id _ rho rho' _ HKp) by (cbn; tauto). tauto.
Qed.

Lemma cont_nz : ltac2:(tb__ "0|3|
S56S49SeS20SaS4eQ40A1A1S72S0SaS0A1M0S55S47R8R7R5R4R3A6S5dS23S98S27S48R8A1A1A3S5dS23S99R8A1S27S48R9A1A1A3S58R8S9S0R5R4A3S6dS1VA1;A1A1A3S59R9S9S0R6R5A3A2S3eZ2000S3R7A1A2S3eZ0S51R7A1A2S40S3fS3R9A1S51R8A1A2S41Z2Z3eA2M1A2S0G0S18G0RbS9S0R2R1A3A3S19S3eSabS2R3A1M2A2S40G2G1A2A2F_;Fr;Fr0;S19S18SeRfSfA3S1aS18G0RaScS0A1A3A1A2F_;F_;F_;F_;F_;F_;F_;F_;F_;Frest';Fcur;Fw;Ftp;Frho;Fnz;FS;FJ;").
Proof.
  intros J S nz rho tp w cur rest' H HGO HNZ (E160 & E161 & E162 & E163 & E208) (E164 & E165) SC SR SS HR0.
  pose proof (SPA_facts_hold segsA _ rho S tp w H) as HFa.
  pose proof (proj1 (Forall_forall _ _) HFa _ HGO) as FGO. pose proof (proj1 (Forall_forall _ _) HFa _ HNZ) as FNZ.
  cbn [List.tl hd] in E164, E165. rewrite (qsize_cons cur) in E163.
  assert (ES' : eval rho s' = Z_to_bv 64 (qsize rest')).
  { replace (qsize rest') with (qb_size cur + qsize rest' - qb_size cur) by lia. apply eval_sub_z; [exact E163 | exact E165 | lia | lia]. }
  destruct rest' as [|r0 r].
  - exfalso. unfold F_go in FGO. cbn [holds branch_taken] in FGO. apply FGO. rewrite ES'. change (qsize []) with 0. unfold vMIN. cbn [eval]. rewrite E208.
    apply negb_true_iff. unfold bv_ltu. apply Z.ltb_ge. rewrite !u64_lit by (unfold kQuarantineMin; lia). unfold kQuarantineMin. lia.
  - split; [|discriminate]. destruct nz; [reflexivity|]. exfalso. unfold F_nz in FNZ. cbn [holds branch_taken] in FNZ. apply FNZ.
    cbn [List.tl] in E164. rewrite hd_addr_cons in E164. unfold vCN. cbn [eval]. rewrite E164. destruct (HR0 r0 r eq_refl) as [R1 R2]. unfold HIGH_SHADOW_END in R1.
    apply negb_true_iff. unfold bv_eqb. apply Z.eqb_neq. rewrite !u64_lit by lia. lia.
Qed.

Lemma cont_nz_J : ltac2:(tb__ "0|2|
S49SeSaS0A1M0S0G0S20SaS4eQ40A1A1S72S18G0S1VA1;A1M1SdS0R6S9S0R5R4A3A3A3S40S51G1A1S41Z2Z3eA2A2S55S47S63VK;VA0;Vrho0;VA1;R8S9S0R7R6A3A6RaR5R4R3A6S5dS23S98S27S48RbA1A1A3S5dS23S99RbA1S27S48RcA1A1A3S58R8S9S0RaR9A3S6dG1A1A3S59R9S9S0RbRaA3A2S19S18SeReSfA3S1aS18G0RbScS0A1A3A1A2F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest';Fcur;Fpre;Fnz;FS;").
Proof.
  intros S nz pre cur rest' rho tp w HGL HSZ H HGO HNZ HV1 HV2. destruct w as [tr [ms md]].
  destruct (proj2 H) as (HK & (HBM & _) & _). cbn [w_tr w_cfg cfg_model fst snd] in HK, HBM. pose proof (benv_of_K _ _ _ _ HK) as BE.
  destruct (qsz_ge rho _ pre (cur :: rest') BE HBM HGL) as (S1 & S2 & S3). rewrite S3 in HSZ.
  assert (INC : In cur (aa_q_global A1)) by (rewrite HGL; apply in_or_app; right; left; reflexivity).
  assert (SC : 8192 <= qb_size cur /\ 0 <= qsize rest').
  { destruct (qsz_ge rho (view segsA (rm rho)) (pre ++ [cur]) rest' BE) as (_ & X2 & _); [rewrite <- app_assoc; exact HBM | rewrite <- app_assoc; exact HGL |].
    split; [|lia]. pose proof (qsize_ge A1 (view segsA (rm rho)) [cur]) as Y. unfold qsize at 1 in Y. cbn [fold_right length] in Y. unfold kQuarantineBatchSize in Y.
    pose proof (proj1 (be_qp _ BE)) as HBP. rewrite qall_A1 in HBP.
    assert (P1 : Forall (batch_pure A1) [cur]) by (constructor; [exact (proj1 (Forall_forall _ _) HBP cur INC) | constructor]).
    assert (M1 : Forall (batch_mem (view segsA (rm rho))) [cur]) by (constructor; [exact (proj1 (Forall_forall _ _) HBM cur ltac:(apply in_or_app; right; left; reflexivity)) | constructor]).
    specialize (Y P1 M1). lia. }
  rewrite (qsize_cons cur) in HSZ. destruct SC as [SC SR].
  apply (cont_nz _ S nz rho tp _ cur rest' H HGO HNZ HV1 HV2 SC SR ltac:(lia)).
  intros r0 r E. subst rest'. destruct (batch_addr_facts _ r0 BE ltac:(rewrite HGL; apply in_or_app; right; right; left; reflexivity)) as (_ & _ & R3 & R4 & _). lia.
Qed.

Section TRLoop.
Context {Q : assn} (X : trk Q).
Hypothesis HJQ : ltac2:(tb__ "0|1|
SaS0A1M0G0Sb0VQ;VX;S63VK;VA0;Vrho0;VA1;R2R1A6A3Frest;Fpre;").
Variable tp : list word.
Hypothesis HSZ : ltac2:(tb__ "0|0|
S40S51S1VA1;A1A1S41Z2Z3eA2A2").

Hypothesis CONT : ltac2:(tb__ "0|1|
SaS0A1M0G0S20S1aS18G0R3ScS0A1A3A1S18G0S1VA1;A1SdS0R4R3A3A3S3eS51R4A1SaaA2S77R4R6A2SafVQ;VX;S55S47S5cR7R6A2S8eR5Vtp;A5A3F_;F_;F_;F_;Frho';Frest';Ftmp;").

Lemma xg_of_exists : ltac2:(tb__ "0|1|
S73SaS0A1M0G0S1aS18G0R2ScS0A1A3A1S18G0S1VA1;A1SdS0R3R2A3A3S72R6R1A1S1bS20S20S19S55S47S5cR7R6A2S8eR1Vtp;R3A6S19S77R1R7A2S3eS51R6A1SaaA2A2A2Lrho2;A2F_;Fw;SafVQ;VX;R6A3F_;F_;F_;Frest';Ftmp;FP0;").
Proof.
  intros P0 tmp rest' HT HG H.
  apply (tr_ex X valuation (fun rho2 w => SPA segsA (JRX tmp rest') Xg rho2 tp w /\ HVX rho2 tmp /\ qsize rest' <= kQuarantineMin) P0 H). intros rho2.
  apply (tr_pure X _ (HVX rho2 tmp /\ qsize rest' <= kQuarantineMin)); [intros w (_ & a & b); exact (conj a b)|]. intros [HV HS].
  eapply (tr_conseq X); [|exact (CONT tmp rest' rho2 HT HG HS HV)]. intros w (Hs & _). exact Hs.
Qed.

Theorem deq_loop_k : ltac2:(tb__ "0|3|
SaS0A1M0G0S20S1aS18G0R2ScS0A1M1A3A1S1aS18G0R4G1A3A1S18G0S1VA1;A1M2SdS0R4R5A3A3S58R4R6S6dG2A1A3S59R5R7A2S5bR6R7A2SafVQ;VX;S55S47S63VK;VA0;Vrho0;VA1;R8R9A6S8dR7Vtp;A5A3F_;F_;F_;F_;F_;F_;Frho;Fpre;Frest;").
Proof.
  induction rest as [|cur rest' IH]; intros pre rho HPRE HREST HGL HV1 HV2 HV3; [congruence|].
  apply (seg_R_IkM X _ rho tp (HJQ _ _)). intros Tx M rho' HIN HKp.
  unfold TskM, Tsk in HIN. cbn [map In] in HIN.
  destruct HIN as [E|[E|[E|[E|[]]]]]; injection E as <- <-; destruct (HV_keep_k rho rho' pre (cur :: rest') _ HKp HV1 HV2 HV3) as (V1 & V2 & V3).
  - apply (xg_of_exists _ (pre ++ [cur]) rest'); [destruct pre; discriminate | rewrite <- app_assoc; exact HGL |].
    intros w Hw. exact (exitk_glue true pre cur rest' _ rho' tp w HPRE HGL HSZ eq_refl Hw V1 V2 V3).
  - apply (tr_pure X _ (true = true /\ rest' <> [])).
    { intros w Hw. apply (cont_nz_J (Contk true) true pre cur rest' rho' tp w HGL HSZ Hw); [| | exact V1 | exact V2];
        unfold Contk, mkR; cbn [ax_S mkA ss_facts]; apply in_or_app; right; cbn; tauto. }
    intros [_ NE]. destruct rest' as [|nxt rest'']; [congruence|].
    apply (tr_ex X valuation (fun rho2 w => SPA segsA (JRQ K A0 rho0 A1 (pre ++ [cur]) (nxt :: rest'')) Headk rho2 tp w
                                /\ HVH rho2 (nxt :: rest'') (last_addr (aa_q_global A1)) /\ HVC rho2 (nxt :: rest'') /\ HVT rho2 (pre ++ [cur])) _
             (fun w Hw => contk_glue pre cur nxt rest'' _ rho' tp w HPRE HGL HSZ Hw V1 V2 V3)).
    intros rho2. apply (tr_pure X _ (HVH rho2 (nxt :: rest'') (last_addr (aa_q_global A1)) /\ HVC rho2 (nxt :: rest'') /\ HVT rho2 (pre ++ [cur]))); [intros w (_ & a); exact a|].
    intros (W1 & W2 & W3). eapply (tr_conseq X); [|exact (IH (pre ++ [cur]) rho2 ltac:(destruct pre; discriminate) ltac:(discriminate) ltac:(rewrite <- app_assoc; exact HGL) W1 W2 W3)].
    intros w (Hs & _). exact Hs.
  - apply (xg_of_exists _ (pre ++ [cur]) rest'); [destruct pre; discriminate | rewrite <- app_assoc; exact HGL |].
    intros w Hw. exact (exitk_glue false pre cur rest' _ rho' tp w HPRE HGL HSZ eq_refl Hw V1 V2 V3).
  - apply (tr_pure X _ (false = true /\ rest' <> [])); [|intros [E _]; discriminate E].
    intros w Hw. apply (cont_nz_J (Contk false) false pre cur rest' rho' tp w HGL HSZ Hw); [| | exact V1 | exact V2];
      unfold Contk, mkR; cbn [ax_S mkA ss_facts]; apply in_or_app; right; cbn; tauto.
Qed.
End TRLoop.

Lemma head0_vals : ltac2:(tb__ "0|4|
S0SaS0A1S1dS20S58R1S9S0R4R3A3R2A3Sb7R2S9S11S1eS4eQ40M0A1M1A2M2SbS1eG1Pa4S4dG0S6eR4A1A2A4S9G2SbS1eG1Pa5S4dG0S3R5A1A2A4ScG2A1A3A3A2S20S19S58R1S9S0R6R5A3M3R4A3S59R1G3A2A2Trho1;F_;Frho;Flb;Frest';Fcur;").
Proof.
  intros cur rest' lb rho (E160 & E161 & E162 & E163 & E208) rho1.
  assert (OTH : forall i, i <> 164%positive -> i <> 165%positive -> rw rho1 i = rw rho i).
  { intros i N1 N2. unfold rho1. apply rho_sets_other. cbn. intros [X|[X|[]]]; congruence. }
  split; [unfold HVH; rewrite !OTH by discriminate; tauto | split; reflexivity].
Qed.

Section TRLoop0.
Context {Q : assn} (X : trk Q).
Hypothesis HJQ : ltac2:(tb__ "0|1|
SaS0A1M0G0Sb0VQ;VX;S63VK;VA0;Vrho0;VA1;R2R1A6A3Frest;Fpre;").
Variable tp : list word.
Hypothesis HSZ : ltac2:(tb__ "0|0|
S40S51S1VA1;A1A1S41Z2Z3eA2A2").
Hypothesis CONT : ltac2:(tb__ "0|1|
SaS0A1M0G0S20S1aS18G0R3ScS0A1A3A1S18G0S1VA1;A1SdS0R4R3A3A3S3eS51R4A1SaaA2S77R4R6A2SafVQ;VX;S55S47S5cR7R6A2S8eR5Vtp;A5A3F_;F_;F_;F_;Frho';Frest';Ftmp;").

Theorem deq_loop_0 : ltac2:(tb__ "0|2|
S0SaS0A1M0S20S18G0S1VA1;A1M1S9S0R3R2A3A3S58R2S9S0R4R3A3S6dG1A1A3S59R3S9S0R5R4A3A2SafVQ;VX;S55S47S63VK;VA0;Vrho0;VA1;ScS0A1S9S0R6R5A3A6S95R4Vtp;A5A3F_;F_;F_;Frho;Frest';Fcur;").
Proof.
  intros cur rest' rho HGL HV1 HV2.
  apply (seg_R_I0M X _ rho tp (HJQ _ _)). intros Tx M rho' HIN HKp.
  unfold Ts0M, Ts0 in HIN. cbn [map In] in HIN.
  destruct HIN as [E|[E|[E|[E|[]]]]]; injection E as <- <-; destruct (HV_keep_0 rho rho' (cur :: rest') _ HKp HV1 HV2) as (V1 & V2).
  - apply (xg_of_exists X tp CONT _ [cur] rest'); [discriminate | exact HGL |].
    intros w Hw. exact (exit0_glue true cur rest' _ rho' tp w HGL HSZ eq_refl Hw V1 V2).
  - apply (tr_pure X _ (true = true /\ rest' <> [])).
    { intros w Hw. apply (cont_nz_J (Cont0 true) true [] cur rest' rho' tp w HGL HSZ Hw); [| | exact V1 | exact V2];
        unfold Cont0, mkR; cbn [ax_S mkA ss_facts]; apply in_or_app; right; cbn; tauto. }
    intros [_ NE]. destruct rest' as [|nxt rest'']; [congruence|].
    apply (tr_ex X valuation (fun rho2 w => SPA segsA (JRQ K A0 rho0 A1 [cur] (nxt :: rest'')) Headk rho2 tp w
                                /\ HVH rho2 (nxt :: rest'') (last_addr (aa_q_global A1)) /\ HVC rho2 (nxt :: rest'') /\ HVT rho2 [cur]) _
             (fun w Hw => cont0_glue cur nxt rest'' _ rho' tp w HGL HSZ Hw V1 V2)).
    intros rho2. apply (tr_pure X _ (HVH rho2 (nxt :: rest'') (last_addr (aa_q_global A1)) /\ HVC rho2 (nxt :: rest'') /\ HVT rho2 [cur])); [intros w (_ & a); exact a|].
    intros (W1 & W2 & W3). eapply (tr_conseq X); [|exact (deq_loop_k X HJQ tp HSZ CONT (nxt :: rest'') [cur] rho2 ltac:(discriminate) ltac:(discriminate) HGL W1 W2 W3)].
    intros w (Hs & _). exact Hs.
  - apply (xg_of_exists X tp CONT _ [cur] rest'); [discriminate | exact HGL |].
    intros w Hw. exact (exit0_glue false cur rest' _ rho' tp w HGL HSZ eq_refl Hw V1 V2).
  - apply (tr_pure X _ (false = true /\ rest' <> [])); [|intros [E _]; discriminate E].
    intros w Hw. apply (cont_nz_J (Cont0 false) false [] cur rest' rho' tp w HGL HSZ Hw); [| | exact V1 | exact V2];
      unfold Cont0, mkR; cbn [ax_S mkA ss_facts]; apply in_or_app; right; cbn; tauto.
Qed.

Hypothesis HPM : ltac2:(tb__ "0|1|
S40SaeS51S1VA1;A1M0A1A2S20S65R1G0A2SafVQ;VX;S55S47S63VK;VA0;Vrho0;VA1;ScS0A1G0A6Sa4R2Vtp;A5A3F_;Frho';F_;").

Theorem recycle_deq : ltac2:(tb__ "0|2|
S20S1aS18SaS0A1S1VA1;A1M0ScS0A1M1A3A1S40SaeS51G0A1A2S65R3G0A2SafVQ;VX;S55S47S63VK;VA0;Vrho0;VA1;G1G0A6Sd6R4Vtp;A5A3F_;F_;F_;Frho;").
Proof.
  intros rho HNE HGT (E204 & E205 & E206 & E207 & E208).
  apply (seg_R_P2 X _ rho tp (HJQ _ _)). intros Tx M rho' HIN [HAG HV].
  unfold TsP2 in HIN. cbn [In] in HIN.
  assert (VH : M = MH -> HVH rho' (aa_q_global A1) (last_addr (aa_q_global A1))).
  { intros ->. unfold HVH. rewrite (HV 160%positive vGN), (HV 161%positive vGF), (HV 162%positive vGB), (HV 163%positive vGS), (HV 208%positive vMIN) by (cbn; tauto).
    unfold vGN, vGF, vGB, vGS, vMIN. cbn [eval]. tauto. }
  assert (PXF : forall w, SPA segsA (JRQ K A0 rho0 A1 [] (aa_q_global A1)) PX rho' tp w -> M = MH -> False).
  { intros w Hw EM. destruct (VH EM) as (_ & _ & _ & E163 & E208'). pose proof (SPA_facts_hold segsA _ rho' PX tp w Hw) as HFa.
    assert (Xf : holds rho' (SPBranch BC_GEU vMIN vS)) by (apply (proj1 (Forall_forall _ _) HFa); unfold PX, mkR; cbn [ax_S mkA ss_facts]; apply in_or_app; right; left; reflexivity).
    cbn [holds branch_taken] in Xf. unfold vMIN, vS in Xf. cbn [eval] in Xf. rewrite E163, E208' in Xf. apply negb_true_iff in Xf. unfold bv_ltu in Xf. apply Z.ltb_ge in Xf.
    rewrite !u64_lit in Xf by (unfold kQuarantineMin, kQuarantineMax in *; lia). unfold kQuarantineMin, kQuarantineMax in *. lia. }
  destruct HIN as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <-.
  - apply (tr_pure X _ False); [intros w Hw; exact (PXF w Hw eq_refl) | intros []].
  - assert (EX : exists cur rest', aa_q_global A1 = cur :: rest') by (destruct (aa_q_global A1) as [|c r]; [congruence | exists c, r; reflexivity]).
    destruct EX as (cur & rest' & EG).
    assert (V0 : HVH rho' (cur :: rest') (last_addr (aa_q_global A1))) by (rewrite <- EG; exact (VH eq_refl)).
    destruct (head0_vals cur rest' _ rho' V0) as [W1 W2].
    eapply (tr_conseq X); [intros w Hw; exact (proj1 (head0_carve cur rest' _ rho' tp w EG ltac:(rewrite <- EG; exact Hw) V0))|].
    exact (deq_loop_0 cur rest' _ EG W1 W2).
  - apply (tr_pure X _ False); [intros w Hw; exact (PXF w Hw eq_refl) | intros []].
  - assert (EX : exists cur rest', aa_q_global A1 = cur :: rest') by (destruct (aa_q_global A1) as [|c r]; [congruence | exists c, r; reflexivity]).
    destruct EX as (cur & rest' & EG).
    assert (V0 : HVH rho' (cur :: rest') (last_addr (aa_q_global A1))) by (rewrite <- EG; exact (VH eq_refl)).
    destruct (head0_vals cur rest' _ rho' V0) as [W1 W2].
    eapply (tr_conseq X); [intros w Hw; exact (proj1 (head0_carve cur rest' _ rho' tp w EG ltac:(rewrite <- EG; exact Hw) V0))|].
    exact (deq_loop_0 cur rest' _ EG W1 W2).
  - apply (HPM HGT). unfold HVP. rewrite !(keepsM_id [204; 205; 206; 207; 208]%positive rho rho' _ (conj HAG HV)) by (cbn; tauto). tauto.
Qed.
End TRLoop0.
End Loop.
