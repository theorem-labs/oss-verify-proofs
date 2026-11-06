(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
Local Set Warnings "-require-in-module".
(* [comment removed for export] *)
From Stdlib Require ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_cert k1 F0A_hbN_env F0A_cLN2 ls.

(* [comment removed for export] *)
Module F0A_hbN_tail.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "False"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@Stdlib.ZArith.BinInt.Z"; "modulo"; "le"; "add"; "lt"; "pow"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "@Corelib.Init.Datatypes"; "list"; "false"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_tail.TailB"; "TPIN"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4"; "chunk_sh_zone"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_blind"; "JW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert"; "hbvar_ok"; "hv_C5"; "hv_E5"; "hv_EMd"; "hv_EMx"; "hv_EUs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQS_glue SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_cert.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_env.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0A_hbN_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.F0A_hbN_step OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_env.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Lemma mod8_of_4096 : ltac2:(tb__ "0|1|
S4S0S4SaR1Z1000A2Z0M0A3S0S4SaR2Z8A2G0A3F_;Fx;").
Proof. intros x Hx. destruct (proj1 (Z.mod_divide x 4096 ltac:(lia)) Hx) as [k ->]. replace (k * 4096) with (k * 512 * 8) by lia. apply Z.mod_mul. lia. Qed.

Section TailB.
Variables (nW : nat) (Kc : KcA) (A : AA) (rho1 : valuation) (ch : sec_chunk) (TZ : Z -> Prop).
Hypothesis HZT : ltac2:(tb__ "0|0|
S4S15Vch;R1A2VTZ;R2A1F_;Fz;").
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.
Let JH : jpredA := ltac2:(tb__ "0|0|
S16S6S15Vch;A1VTZ;S1dVnW;S1eS12VA;VKc;Vrho1;A6A4").
Variables (SC : axst) (f : nat) (l : bool) (cv : hbvar).
Hypothesis VOK : ltac2:(tb__ "0|0|
S17VSC;Vf;Vl;Vcv;A4").
Definition CHFh : Prop := ltac2:(tb__ "0|2|
S1S0S4SaVh;Z1000M0A2Z0M1A3S1S0S4SaVmsz;G0A2G1A3S1SbZ12000Vmsz;A2S1SbZ643000Vh;A2SdScVh;Vmsz;A2SeZ2Z2fA2A2A2A2A2A2").
Hypothesis CH : CHFh.
Definition TPIN (r : valuation) : Prop := ltac2:(tb__ "0|2|
S1S0SfQ40M0A1M1S8Vr;PcaA2S10G0Vh;A2A3S0G1S8Vr;PcbA2S10G0Vmsz;A2A3A2").

Lemma G_c5 : ltac2:(tb__ "0|0|
S7S11SfQ40A1A1S13S14R3A1S9S6VJH;S19Vcv;A1R4R3R2A6S9S6VJH;S18Vcv;A1R5R4R3A6F_;F_;Fw;Ftp;Fr;").
Proof.
  intros r tp w (EH & EM) Hw. destruct CH as (C1 & C2 & C3 & C4 & C5).
  rewrite <- (v_C5set SC f l cv VOK).
  apply (SPA_restate segsA JH r (hv_E5 cv) (ax_S (hv_C5 cv)) tp w _ _ (v_C5swf SC f l cv VOK) (v_C5diff SC f l cv VOK) (v_C5next SC f l cv VOK)); [|constructor|exact Hw].
  constructor; [|constructor]. cbn [fst snd].
  apply (eval_A2OLD r h msz); [unfold vH; cbn [eval]; exact EH | unfold vMS; cbn [eval]; exact EM | lia | lia | lia | exact (mod8_of_4096 _ C1) | exact (mod8_of_4096 _ C2)].
Qed.

Lemma G_eus : ltac2:(tb__ "0|0|
S7S11SfQ40A1A1S13S14R3A1S9S6VJH;S1cVcv;A1R4R3R2A6S2F_;F_;Fw;Ftp;Fr;").
Proof.
  intros r tp w (EH & EM) Hw. destruct CH as (CH1 & CH2 & CH3 & CH4 & CH5).
  pose proof (SPA_facts_hold segsA _ r (hv_EUs cv) tp w Hw) as HFa.
  pose proof (v_EUsfact SC f l cv VOK) as X0. apply existsb_exists in X0 as (g & Hg & Eg). apply sprop_eqb_sound in Eg. subst g.
  pose proof (proj1 (Forall_forall _ _) HFa _ Hg) as HB. cbn [holds branch_taken] in HB. apply negb_true_iff in HB. unfold bv_ltu in HB. apply Z.ltb_ge in HB.
  rewrite (eval_EBEG r h ltac:(unfold vH; cbn [eval]; exact EH) ltac:(lia)), (eval_EEND r h msz ltac:(unfold vH; cbn [eval]; exact EH) ltac:(unfold vMS; cbn [eval]; exact EM) ltac:(lia) ltac:(lia) ltac:(lia)) in HB.
  destruct (mrange_facts h msz ltac:(lia) CH1 CH2 CH3) as (M1 & M2 & M3 & M4 & M5).
  assert (SHB : 0 <= Sh h /\ Sh (h + msz) < 2 ^ 63).
  { unfold Sh, SHADOW_OFF. pose proof (Z.div_pos h 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (h + msz) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
  rewrite !u64_lit in HB by lia. lia.
Qed.

Lemma G_shd : ltac2:(tb__ "0|1|
S7S11SfQ40A1M0A1S13S14R3A1S9S6VJH;S1bVcv;A1R4R3R2A6S3S7S7S1S9S6VJH;S1aVcv;A1R1R5R4A6S5S0G0S8R2R1A2S8R7R1A2A3Fv;A2Lr2;A2F_;F_;Fw;Ftp;Fr;").
Proof.
  intros r tp [tr [ms md]] (EH & EM) H. destruct CH as (C1 & C2 & C3 & C4 & C5).
  pose proof (Z.div_pos msz 8 ltac:(lia) ltac:(lia)) as MD0. pose proof (Z.div_lt_upper_bound msz 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as MD1.
  pose proof (Sh_in_band h ltac:(lia)) as SB1. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in SB1.
  assert (SHE : Sh (h + msz) = Sh h + msz / 8) by (apply Sh_add8; [exact (mod8_of_4096 _ C1) | exact (mod8_of_4096 _ C2)]).
  assert (RG : obj_range r (O_csh vH vMS) = (Sh h, Sh h + msz / 8)).
  { unfold O_csh, obj_range, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi].
    rewrite (eval_BSHS r vH h ltac:(unfold vH; cbn [eval]; exact EH) ltac:(lia)), (soff_LENS r vMS msz ltac:(unfold vMS; cbn [eval]; exact EM) ltac:(lia)).
    rewrite soff_lit_small by lia. rewrite u64_lit by lia. f_equal. lia. }
  destruct (dissolveZW (chunk_sh_zone ch) TZ (JF nW UStopLe false A Kc rho1) HZT (hv_EMx cv) (ss_objs (ax_S (hv_EMd cv))) [O_csh vH vMS] r tp tr ms md (v_EMxobjs SC f l cv VOK) H) as (H2 & RW & RL).
  - intros x (o & Ho & Hz). destruct Ho as [<-|[]]. rewrite RG in Hz. cbn [fst snd] in Hz. unfold chunk_sh_zone. fold h msz. rewrite SHE. exact Hz.
  - constructor; [left; reflexivity | constructor].
  - rewrite (v_EMdset SC f l cv VOK) in H2. eexists. split; [exact H2 | exact RW].
Qed.
End TailB.
End F0A_hbN_tail.

(* [comment removed for export] *)
Module F0A_hbN_entry.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "pair"; "cons"; "nat"; "prod"; "list"; "nil"; "bool"; "true"; "Some"; "app"; "false"; "length"; "option"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "or"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "rw"; "valuation"; "sprop"; "SLit"; "holds"; "sobj"; "ss_objs"; "sprop_below"; "sprop_eqb"; "ss_facts"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "div"; "of_nat"; "opp"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_signed"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "SEC_INST"; "AInvA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "aa_geom"; "ag_spacebeg"; "sc_map_beg"; "sc_map_size"; "sec_chunk"; "aa_sec"; "ag_ctx"; "ag_thread"; "ag_pab"; "sc_size"; "topG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states"; "XO_hb"; "F1_hb"; "vRISh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "Wcan"; "UStopLe"; "chain_pre"; "free_depth"; "top_high"; "F_depth"; "V_DEPTH"; "tp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4"; "chunk_sh_zone"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_blind"; "blind_rel"; "JW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_entry.Entry"; "zbH"; "ZUH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_entry"; "N_hb"; "ZUH"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_env"; "hbenv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0A_hbN_zones"; "zd_allb"; "zds_of"; "zenv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws"; "N8"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "PG"; "LOW_SHADOW_BEG"; "kSpaceSize"; "round_up"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue"; "fam_ok"; "zloS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop"; "zhiX"; "zbX"; "@Stdlib.Lists.List"; "In"; "forallb"; "existsb"; "nth_error"; "@Stdlib.PArith.BinPos.Pos"; "lt"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_obj"; "carve_spec"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM"; "idm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib"; "mkST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states"; "vNCH"; "vPAB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI"; "stopJ_stable"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQS_glue SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.InvQ10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQS_k.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ih.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skel F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_env.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.F0A_laws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jv.F0A_hbN_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k1.F0A_hbN_step OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_env.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition N_hb : list carve_spec := ltac2:(tb__ "0|f|
S1S3S3S3S14SdA2M0SdA2M1S4S3S3SdS2A2M2S14A2M3A1M4A2M5S0G1G4S0G0SdS0S14SdS18Z0A1M6Zeaa80M7A4Zeaa84A4S1G3S0G2S14S0SdS2G7U4M8A4S18ZffffffffA1A4S5G3A1M9A3A4S1G5S0G1G4S0G0SdS0S14SdG6Zeaa88MaA4Zeaa91A4S1G3S0G2S14S0SdS2GaU8MbA4S39A4S1G3S0G2S14S0SdS2Zeaa90U1A4G6A4G9A3A3A4S1G5S0G1G4S0G0SdS0S14SdG6S29A4S1fS29Z10A2A4S1G3S0G2S14S0SdS2S29GbA4S18S51A1A4S1G3S0G2S14S0SdS2S1fS29Z8A2GbA4S68A4G9A3A3A4S1G5S0G1G4S0G0SdS0S14SdG6S1fS29Z38A2McA4S1fS29Z40A2MdA4S1G3S0G2S14S0SdS2GcGbA4S67A4G9A3A4S1G5S0G1G4S0G0SdS0S14SdG6GdA4Zead00MeA4G9A4S1G5S0G1G4S0G0SdS0S14SdG6GeA4Zead04A4S1G3S0G2S14S0SdS2GeG8A4G6A4G9A3A4S1G5S0G1G4S0G0SdS0S14SdG6Zead08A4Zead30A4G9A4S5G5A1A3A3A3A3A3A3A3").
Lemma N_hb_objs : ltac2:(tb__ "0|0|
SfS4S1aA1S44S62S1aS61S4aA4S37A3"). Proof. reflexivity. Qed.

Section Entry.
Variables (A : AA) (it : Z * Z) (i : nat) (ch : sec_chunk) (rho : valuation).
Hypothesis QS : ltac2:(tb__ "0|0|
S4cVA;Vit;Vi;Vch;Vrho;A5").

Lemma carve_hb : Forall (carve_okq rho) N_hb.
Proof.
  pose proof QS as [HG HSEP3 HRTC HRIG HSR HI HU HSZ HSEP HIM HSTAT HN HV].
  pose proof (qs_nums A it i ch rho QS) as (T0 & T1 & C0 & C1' & TG & TI & CI & _).
  destruct HRIG as (E151 & E152 & E155 & E195). destruct HV as (E12 & E200 & E201 & _).
  assert (HR : cells_ok (view segsA (rm rho)) (rtc_cells RTC_A (aa_geom A))) by exact HRTC.
  destruct HSR as (_ & _ & _ & _ & _ & S0c & S8 & _ & _ & _ & S56 & _ & SM & _).
  unfold N_hb. repeat apply Forall_cons; try apply Forall_nil; unfold carve_okq; lazy beta iota zeta.
  all: cbn [eval]; rewrite ?u64_lit by lia.
  all: unfold SEC_INST, PG, IMG_HI in *.
  all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|]. all: split; [lia|].
  all: split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
  all: split.
  all: try match goal with
       | |- forall off, _ -> wok_of _ _ (Z_to_bv 64 (0 + off)) = true /\ _ => intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]
       end.
  all: try (unfold cells_in_view; apply Forall_nil).
  - unfold cells_in_view; repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; civ_any2 HR.
  - unfold cells_in_view, vRISh; repeat apply Forall_cons; try apply Forall_nil; cbn [eval]; rewrite ?E195; civ_any2 HR.
  - unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
    + intros j Hj. apply (civ_cell rho (rm rho) 0 961176 8 4096 (SLit 4096)); [exact S0c | cbn [eval]; reflexivity | lia | lia | exact Hj].
    + intros j Hj. apply (civ_cell rho (rm rho) 0 961184 8 (ag_pab (aa_geom A)) vPAB); [exact S8 | unfold vPAB; cbn [eval]; exact E200 | lia | lia | exact Hj].
  - unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
    intros j Hj. apply (civ_cell rho (rm rho) 0 961232 8 (Z.of_nat (length (aa_sec A))) vNCH); [exact S56 | unfold vNCH; cbn [eval]; exact E201 | lia | lia | exact Hj].
  - unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
    intros j Hj. apply (civ_cell rho (rm rho) 0 961792 4 0 (SLit 0)); [exact SM | cbn [eval]; reflexivity | lia | lia | exact Hj].
Qed.

Lemma facts_hb : ltac2:(tb__ "0|0|
S2S55R1S2cS2bVA;A1A1S2dVch;A1S2eVch;A1A4S43S17S19Vrho;A1S38R2A1A3F_;Ff;").
Proof.
  intros f HFAM. pose proof QS as [HG HSEP3 HRTC HRIG HSR HI HU HSZ HSEP HIM HSTAT HN HV].
  pose proof (qs_nums A it i ch rho QS) as (T0 & T1 & C0 & C1' & TG & _). pose proof (qs_chunk A it i ch rho QS) as (_ & _ & MS & IH & HTG & _).
  pose proof (hb_E A it i ch rho QS) as (_ & _ & EmT & RmT).
  pose proof (geom_nums _ HG) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S1 & S2 & _). rewrite kSpaceSize_val in S2. unfold HIGH_SHADOW_END in S1.
  destruct HRIG as (E151 & E152 & E155 & E195). destruct HV as (E12 & E200 & E201 & _).
  assert (NCpos : 1 <= Z.of_nat (length (aa_sec A)) <= 2 ^ 20).
  { pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)) as LT.
    destruct HSR as (_ & _ & (B1 & B2) & _). unfold kPtrArrayReserve in B2. lia. }
  unfold F1_hb. apply Forall_app. split.
  - unfold Fm_hb. destruct f as [|[|f]]; cbn [fam_ok] in HFAM; repeat apply Forall_cons; try apply Forall_nil; unfold IMG_HI, PG in *.
    + apply (hlt rho mT vSB (fst it - 16) (ag_spacebeg (aa_geom A))); [exact EmT | exact E155 | lia | lia | lia].
    + apply (hlt rho mT vSB (fst it - 16) (ag_spacebeg (aa_geom A))); [exact EmT | exact E155 | lia | lia | lia].
    + apply (hle rho (SAlu ALU_ADD vSB (SLit (2 ^ 37))) mT (ag_spacebeg (aa_geom A) + 2 ^ 37) (fst it - 16)); [apply (ev_add_lit rho vSB); [exact E155 | lia | lia | lia] | exact EmT | lia | lia | lia].
  - unfold HIGH_SHADOW_END, TOPMAX, IMG_HI, PG in *. repeat apply Forall_cons; try apply Forall_nil.
    + apply (hle rho _ vSB 0x10007fff8000 (ag_spacebeg (aa_geom A))); [apply elit | exact E155 | lia | lia | lia].
    + apply (hle rho vSB _ (ag_spacebeg (aa_geom A)) (140737479966720 - 2 ^ 37 - 4096)); [exact E155 | apply elit | lia | lia | lia].
    + apply (hne0 rho vNCH (Z.of_nat (length (aa_sec A)))); [exact E201 | lia].
    + apply (hle rho vNCH _ (Z.of_nat (length (aa_sec A))) (2 ^ 20)); [exact E201 | apply elit | lia | lia | lia].
Qed.

Definition zbH : nat -> Z := ltac2:(tb__ "0|2|
S58S32S2bVA;A1M0A1S31G0A1S35G0A1S2dVch;A1S52Z0M1G1G1G1A9").
Definition ZUH : list nat := ltac2:(tb__ "0|0|
S1S2U0S1S2U1S1S2U2S1S2U3S1S2U4S1S2U5S5S2A1A3A3A3A3A3A3").
Lemma zsepH : ltac2:(tb__ "0|4|
S2S2S59S2R2S49A3M0G0S12SfS2R4R3A3A1S13S20S1fS48R5A1M1S57S2eVch;A1M2R5A2A2S1fS48R4A1M3S56R4A1A2A2S20S1fG3S57G2R4A2A2S1fG1S56R5A1A2A2A2F_;F_;F_;Fz';Fz;").
Proof.
  pose proof QS as [HG HSEP3 HRTC HRIG HSR HI HU HSZ HSEP HIM HSTAT HN HV].
  pose proof (qs_nums A it i ch rho QS) as (T0 & T1 & C0 & C1' & TG & TI & CI & TC). pose proof (qs_chunk A it i ch rho QS) as (_ & _ & MS & IH & HT & HB & _).
  destruct HSEP as (_ & HT' & _ & HC' & _).
  destruct HG as (_ & _ & TD & CD & _). destruct TD as (_ & _ & _ & _ & _ & TB). destruct CD as (_ & _ & _ & _ & CB).
  intros z z' Hz Hz' NE. unfold ZUH in Hz, Hz'. cbn [In] in Hz, Hz'.
  unfold zbH, zbX, zloS, zhiX, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *.
  repeat (destruct Hz as [<-|Hz]); try (exfalso; exact Hz); repeat (destruct Hz' as [<-|Hz']); try (exfalso; exact Hz'); try (exfalso; apply NE; reflexivity); cbn [Nat.eqb]; lia.
Qed.
End Entry.

Section EntryGlue.
Variables (nW : nat) (Kc : KcA).
Hypothesis HKc : Kc_ok Kc.
Hypothesis HUS : ltac2:(tb__ "0|0|
S69S3aVnW;A1S3bA2").
Variables (A : AA) (rho1 : valuation) (p n : Z) (i : nat) (ch : sec_chunk) (f : nat) (TZ : Z -> Prop).
Hypothesis HI : ltac2:(tb__ "0|0|
SfScS2fA1S5cS2fS30VA;A1Vi;A3S8S2fVch;A2A3").
Hypothesis HU : ltac2:(tb__ "0|0|
SfSdVp;S1fS1fS2dVch;A1S51A2Z800A2A3").
Hypothesis HSZ : ltac2:(tb__ "0|0|
SfSdS34Vch;A1S1fS54Vn;Z8A2Z1000A2A3").
Hypothesis HN : 1 <= n.
Hypothesis HNB : ltac2:(tb__ "0|0|
S20S1fZ1800S50Vn;A1A2S2eVch;A1A2").
Hypothesis HFAM : ltac2:(tb__ "0|0|
S55Vf;S2cS2bVA;A1A1S2dVch;A1S2eVch;A1A4").

Hypothesis HPIN : ltac2:(tb__ "0|4|
S10SfS25Q40M0A1M1S15Vrho1;P97A2S24G0S32S2bVA;A1M2A1A2A3S10SfG1S15Vrho1;P98A2S24G0S31G2A1A2A3S10SfG1S15Vrho1;P9bA2S24G0S2cG2A1A2A3S10SfG1S15Vrho1;PcA2S24G0Vp;A2A3S10SfG1S15Vrho1;P69A2S24G0S50Vn;A1M3A2A3SfG1S15Vrho1;P6aA2S24G0S21G3Z8A2A2A3A2A2A2A2A2").
Let JH : jpredA := ltac2:(tb__ "0|0|
S47S27S42Vch;A1VTZ;S63VnW;S3bSaVA;VKc;Vrho1;A6A4").
Variables (E S0 : axst).
Definition T_entry : strans := ltac2:(tb__ "0|1|
S66VE;U0S4aS1SePc8S1SePc9S1SePc3S5SeA1A3A3A3M0S38Vf;A1VS0;S65G0A1S4eVnW;S1bS36VE;A1A1A2S4eVnW;S37A2A9").
Hypothesis TOK : s_ok T_entry = true.
Hypothesis ZOK : ltac2:(tb__ "0|0|
S10SfS6S4dVnW;S4bS1bS36VE;A1A1A3S7A3SfS6S4dVnW;S4bS37A3S7A3A2").
Hypothesis FCH : ltac2:(tb__ "0|1|
S10SfS6S5aS17S17S5bS17S1dR1A1S1eS36VE;A1A1A3Lg;S9S17S3cS3aVnW;A1A1S3fS3dA1A3M0A3S7A3SfS6S5aS17S1cS64A1G0A3S7A3A2").

Lemma JH_parts : ltac2:(tb__ "0|1|
S16S4S25Q40A1M0A1S4S5fA1S5eVJH;R4R3R2R1A4S11S16S16S10S2aS27VA;R1R5R3A5S10VKc;R4R3A2S10S41VA;R1A2S10S3eVA;R1A2S10S46S27S42Vch;A1VTZ;R1R6A5SeS5dR1S28A2SfG0S15R8R2A2S15Vrho1;R2A2A3F_;Fv;A2A2A2A2A2Lrp;A2F_;Fmd;Ftr;Ftp;Fr;").
Proof.
  intros r tp tr md (rp & (Hag & HA & _ & _ & HK & Htp & _ & Htop) & BR). exists rp.
  split; [exact HA|]. split; [exact HK|]. split; [exact Htp|]. split; [exact Htop|]. split; [exact BR|].
  intros v Hv. rewrite (proj1 BR v). symmetry. exact (proj1 Hag v Hv).
Qed.

Lemma zenv_of : ltac2:(tb__ "0|1|
S16S16S4cVA;S0SdSdVp;Vn;A4Vi;Vch;R1A5S3eVA;R3A2S46S27S42Vch;A1VTZ;R4R3A5SeS5dR1S28A2SfS25Q40M0A1S15R6R2A2S15Vrho1;R2A2A3F_;Fv;S20S26G0S15R5S40A2A2S23S3dA1A2S43S17S19R6A1S3cS3aVnW;A1A1A3S4fVnW;VA;Vp;Vn;Vch;R7A6F_;F_;F_;F_;F_;F_;Fr4;Frp;").
Proof.
  intros rp r4 QS4 Htop BR RW4 HD HC. destruct HPIN as (P151 & P152 & P155 & P12 & P105 & P106).
  pose proof (qs_nums A (p, n) i ch r4 QS4) as (T0 & T1 & C0 & C1' & TG & _). pose proof (qs_chunk A (p, n) i ch r4 QS4) as (CM & _ & MS & IH & HT & _).
  pose proof (N8_facts n HN) as (N1 & N2 & N3 & N4). unfold PG, IMG_HI in *.
  constructor; try (rewrite RW4 by (unfold GW; lia); assumption).
  - unfold top_high in *. unfold V_DEPTH in *. rewrite !(proj1 BR). exact Htop.
  - exact HD.
  - exact HC.
  - lia.
  - repeat split; try assumption; lia.
Qed.

Lemma G_entry : ltac2:(tb__ "0|4|
S16S4S25Q40M0A1M1A1S60S45S27VJH;VE;R3R2R1A6S11S16S16S10S45S27VJH;VS0;R1R4R3A6SeG1S59S3SeG1A2M2S0SeG1R2R1A4S1G2S0SeG1Pc8S24G0S33S2bVA;A1M3A1A2A4S1G2S0SeG1Pc9S24G0S22SbS2fS30VA;A1A2A1A2A4S1G2S0SeG1Pc3S24G0S1fS2cG3A1S53A2A2A4S5G2A1A3A3A3A3SfG1S15R4R3A2R2A3F_;Fx;Fv;A2Lr2;A2F_;Fw;Ftp;FrhoE;").
Proof.
  intros rhoE tp [tr [ms md]] H.
  pose proof (JF_stable nW UStopLe false A Kc rho1 HUS HKc) as HST. change GW with NPRE in HST.
  set (bs := [(200%positive, Z_to_bv 64 (ag_pab (aa_geom A))); (201%positive, Z_to_bv 64 (Z.of_nat (length (aa_sec A)))); (195%positive, Z_to_bv 64 (ag_spacebeg (aa_geom A) + kSpaceSize))]).
  set (vals := map snd bs).
  pose proof (SPA_facts_hold segsA _ rhoE E tp _ H) as HFa.
  assert (FIN : forall g, In g (chain_pre (Wcan nW) ++ F_depth free_depth) -> holds rhoE g).
  { intros g Hg. pose proof (proj1 (forallb_forall _ _) (proj1 FCH) g Hg) as X. apply existsb_exists in X as (g' & Hg' & Eg). apply sprop_eqb_sound in Eg. subst g'.
    exact (proj1 (Forall_forall _ _) HFa g Hg'). }

  assert (ENVAT : forall r4, (forall v, (v < NPRE)%positive -> rw r4 v = rw rhoE v) -> (forall l, rl r4 l = rl rhoE l) -> (forall v x, In (v, x) bs -> rw r4 v = x) ->
            JH r4 tp tr md -> hbenv A (p, n) i ch r4 /\ zenv nW A p n ch r4).
  { intros r4 RWE RLE RB HJ4. destruct (JH_parts r4 tp tr md HJ4) as (rp & HA & HK & Htp & Htop & BR & RW4).
    destruct HPIN as (P151 & P152 & P155 & P12 & P105 & P106).
    assert (RP : forall v, (v < GW)%positive -> rw rp v = rw rho1 v) by (intros v Hv; rewrite <- (proj1 BR v); exact (RW4 v Hv)).
    pose proof (hbenv_intro Kc HKc A p n i ch HI HU HSZ HN TZ rp r4 tp tr md HA HK Htp Htop
                  ltac:(rewrite RP by (unfold GW; lia); exact P151) ltac:(rewrite RP by (unfold GW; lia); exact P152) ltac:(rewrite RP by (unfold GW; lia); exact P155)
                  BR ltac:(rewrite RW4 by (unfold GW; lia); exact P12) (RB _ _ (or_introl eq_refl)) (RB _ _ (or_intror (or_introl eq_refl))) (RB _ _ (or_intror (or_intror (or_introl eq_refl))))) as QS4.
    split; [exact QS4|].
    assert (AV : agree_vals NPRE rhoE r4) by (split; [intros v Hv; symmetry; exact (RWE v Hv) | intros l; symmetry; exact (RLE l)]).
    assert (F4 : forall g, In g (chain_pre (Wcan nW) ++ F_depth free_depth) -> holds r4 g).
    { intros g Hg. apply (proj1 (holds_agree_vals NPRE rhoE r4 g AV (proj1 (forallb_forall _ _) (proj2 FCH) g Hg))). exact (FIN g Hg). }
    apply (zenv_of rp r4 QS4 Htop BR RW4).
    - assert (D1 : holds r4 (SPBranch BC_GE (SLit (- free_depth)) (SVar V_DEPTH))) by (apply F4; apply in_or_app; right; left; reflexivity).
      cbn [holds eval branch_taken] in D1. unfold bv_lts in D1. apply negb_true_iff in D1. apply Z.ltb_ge in D1.
      change (bv_signed (Z_to_bv 64 (- free_depth))) with (- free_depth) in D1. exact D1.
    - apply Forall_forall. intros g Hg. apply F4. apply in_or_app. left. exact Hg. }
  set (rhoB := rho_sets rhoE bs).
  assert (HJB : JH rhoB tp tr md).
  { apply (JW_stable segsA NPRE (chunk_sh_zone ch) TZ _ HST rhoE rhoB tp tr md md); [|apply mat_equiv_refl | exact (proj2 H)].
    unfold rhoB. apply agree_below_rho_sets. intros v x Hin. cbn in Hin. unfold NPRE. repeat (destruct Hin as [Ein|Hin]; [injection Ein as <- _; lia|]). destruct Hin. }
  assert (NDB : List.NoDup (map fst bs)) by (cbn; repeat constructor; cbn; intuition discriminate).
  destruct (ENVAT rhoB) as (QSB & _); [| | | exact HJB |].
  { intros v Hv. unfold rhoB. rewrite rho_sets_other; [reflexivity|]. cbn. unfold NPRE in Hv. intros [<-|[<-|[<-|[]]]]; lia. }
  { intros l. unfold rhoB. rewrite rl_rho_sets. reflexivity. }
  { intros v x Hin. unfold rhoB. exact (rho_sets_get bs rhoE v x NDB Hin). }
  destruct (s_stepW (chunk_sh_zone ch) TZ (JF nW UStopLe false A Kc rho1) HST (zbH A ch) zloS (zhiX (sc_map_size ch)) ZUH (zsepH A (p, n) i ch rhoB QSB) T_entry [] vals rhoE tp tr ms md TOK
              (keepN0 E) eq_refl H (Forall_nil _)) as (rho5 & H5 & V5 & RM5 & AG5 & EV).
  { intros EV3 HJ4. set (rho3 := rho_absorb rhoE (map dobj []) (vms md tp ms)) in *. set (rho4 := rho_sets rho3 (combine (s_bs T_entry) vals)) in *.
    assert (EC : combine (s_bs T_entry) vals = bs) by reflexivity.
    destruct (ENVAT rho4) as (QS4 & ZE4); [| | | exact HJ4 |].
    { intros v Hv. unfold rho4. rewrite EC, rho_sets_other; [reflexivity|]. cbn. unfold NPRE in Hv. intros [<-|[<-|[<-|[]]]]; lia. }
    { intros l. unfold rho4. rewrite rl_rho_sets. reflexivity. }
    { intros v x Hin. unfold rho4. rewrite EC. exact (rho_sets_get bs rho3 v x NDB Hin). }
    assert (ZS : forall objs, zd_allb nW ZUH objs = true -> Forall2 (in_zoneW rho4 (zbH A ch) zloS (zhiX (sc_map_size ch)) ZUH) objs (zds_of nW objs)).
    { intros objs HB. apply (zds_sound nW A p n ch rho4 (zbH A ch) zloS (zhiX (sc_map_size ch)) ZUH); try (repeat split; reflexivity); [exact ZE4 | exact HB]. }
    assert (EO : ss_objs (ax_S (s_Cd T_entry)) = ss_objs (ax_S E)).
    { unfold s_Cd, dropN, keepN. cbn [s_C s_k T_entry]. destruct E as [SE XE BE]. cbn [ax_setS ax_S set_objs ss_objs]. rewrite Nat.sub_0_r. apply firstn_all. }
    split; [exact (carve_hb A (p, n) i ch rho4 QS4)|]. split; [exact (ZS _ (proj2 ZOK))|]. split; [rewrite EO; exact (ZS _ (proj1 ZOK))|].
    intros _. exact (facts_hb A (p, n) i ch rho4 QS4 f HFAM). }
  exists rho5. split; [exact H5|]. intros v x Hin. set (rho4 := rho_sets (rho_absorb rhoE (map dobj []) (vms md tp ms)) (combine (s_bs T_entry) vals)) in *.
  rewrite (V5 v (SVar v)); [cbn [eval]; exact (rho_sets_get bs _ v x NDB Hin)|].
  cbn in Hin. destruct Hin as [Ein|[Ein|[Ein|[]]]]; injection Ein as <- _; cbn; tauto.
Qed.
End EntryGlue.
End F0A_hbN_entry.

(* [comment removed for export] *)
Module F0A_hbN_unmap.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "or"; "not"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws"; "segsA"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "lt"; "of_nat"; "mul"; "pow"; "sub"; "modulo"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "sec_chunk"; "aa_sec"; "sc_map_beg"; "aa_geom"; "ag_pab"; "aa_live"; "ag_ctx"; "ag_spacebeg"; "ag_thread"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rm"; "sv"; "valuation"; "rw"; "eval"; "sobj"; "obj_range"; "ranges_disjoint"; "rl"; "reg_sv"; "ss_objs"; "@Corelib.Init.Datatypes"; "bool"; "length"; "list"; "false"; "option"; "true"; "pair"; "Some"; "prod"; "app"; "cons"; "nat"; "None"; "fst"; "snd"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RtCells"; "view"; "cell_ok"; "mkACell"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "@Corelib.Init.Nat"; "sub"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "m_vmmaps"; "vm_maps"; "map_remove"; "region_free"; "TASK_SIZE"; "map_has"; "page_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "liftKA"; "ok_frameA"; "stableA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SysCallA"; "ok_pframeA"; "smatch_pendingA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "kPtrArrayReserve"; "PG"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "@Stdlib.Lists.List"; "nth_error"; "In"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_unmap.Node"; "JH2"; "JPh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv"; "AInvA"; "SEC_INST"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4"; "chunk_zone"; "chunk_sh_zone"; "sec_junk_zone"; "sec_tbl_zone"; "@Corelib.Init.Peano"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysSpec"; "munmap_model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.SysStep"; "unmap_range"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "set_rm"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MmapFixedA"; "tp_forget"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "ax_X"; "ax_base"; "shadow_addr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_blind"; "blind_rel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_unmap"; "DUZh"; "JH2"; "JPh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l0.InvQ11"; "freeBigA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "NPRE"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_gpr"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.Virt"; "MI"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "GW"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN_unmap.Unmap"; "DUZh"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel"; "JF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "UStopLe"; "top_high"; "tp_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states"; "vH"; "@Stdlib.PArith.BinPos.Pos"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQS_k.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import PaidMunmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import SysCallA MmapA MmapFixedA MmapNodesA MunmapSymA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SpineMallocI.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SpineMallocI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import PaidMunmap.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require InvLaws F0A_skel F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_env.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require l0.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.InvQ10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvLaws OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_env OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.l0.InvQ11.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Unmap.
Variables (A : AA) (l1 l2 : list (Z * Z)) (p n : Z) (i : nat) (ch lst : sec_chunk) (l : bool).
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.
Hypothesis HLV : ltac2:(tb__ "0|1|
S0S26S2cSeSeA2M0A1S15VA;A1S2dG0Vl1;S2eG0S2aSeSeVp;Vn;A4Vl2;A3A3A3").
Hypothesis HPR : is_primary n = false.
Hypothesis HI : ltac2:(tb__ "0|0|
S0S28S10A1S4dS10S11VA;A1Vi;A3S2bS10Vch;A2A3").
Hypothesis HU : ltac2:(tb__ "0|0|
S0SeVp;S6S6S12Vch;A1S4aA2Z800A2A3").
Hypothesis Hl : ltac2:(tb__ "0|1|
S0S28S10A1S4dS10S11VA;A1M0S39S25S10G0A2U1A2A3S2bS10Vlst;A2A3").
Hypothesis HLT : ltac2:(tb__ "0|0|
S0S24Vl;S29A3S0S2fVi;S39S25S10S11VA;A1A2U1A2A3F_;").
Hypothesis HLF : ltac2:(tb__ "0|0|
S0S24Vl;S27A3S57Vi;S39S25S10S11VA;A1A2U1A2A2F_;").

Hypothesis CH : ltac2:(tb__ "0|1|
S1S7Z643000Vh;A2S1S8Z0Vmsz;A2S1S8S6Vh;Vmsz;A2M0SbZ2Z2fA2A2S2S7G0S4cA2S7S4bVh;A2A2A2A2A2").
Hypothesis LSTOFF : ltac2:(tb__ "0|1|
S0S24Vl;S27A3S2S7S6S12Vlst;A1M0Z20A2Vh;A2S7S6Vh;Vmsz;A2G0A2A2F_;").
Hypothesis PABOFF : ltac2:(tb__ "0|1|
S2S7S6S14S13VA;A1A1M0S49A2Vh;A2S7S6Vh;Vmsz;A2G0A2A2").
Hypothesis NCB : ltac2:(tb__ "0|0|
S7SaZ8S9S25S10S11VA;A1A2A1A2S49A2").
Definition DUZh (z : Z) : Prop := ltac2:(tb__ "0|0|
S2S53Vch;Vz;A2S2S54Vch;Vz;A2S2S55Vz;A1S56VA;Vi;Vz;A3A2A2A2").

Lemma unmap_inv : ltac2:(tb__ "0|a|
SeOF_;S1bS1bS26S36Q40M0A1A1S3aS51S5VA;R4R2R1A5S60S5S6cR6R5R4A5S34S33S5S19R5A1A2S35S6S52Z38A2U8M1ScS9S25S10S11VA;A1A2A1Z1A2A3A2S34S33S5S19R6A1A2S35Zead00U4Z0A3A2S0S24Vl;S27A3S1S34S33S5S19R8A1A2M2S35S6S14S13VA;A1A1SaZ8M3S9Vi;A1M4A2A2M5G1S12Vlst;A1M6A3A2S34G2S35S6G6Z18A2G1G4A3A2A2F_;S0S24Vl;S29A3SeS1S7G5R1A2S8R1S6G5G3A2A2A2S0S28S36Q8A1A1S33S5S19RbA1M7R2A3S33S5S19RcA1R2A3A3F_;Fz;F_;S6aS5R7R8A3S0S24S3fS3eS3dS3cR8A1A1S38G0Vh;A2M8A2G8S38G0Vmsz;A2M9A3S29A3S51S5S64VA;Vl1;Vl2;Vi;A4S5aRbS59G7G8G9A3A2S5bVh;S6Vh;Vmsz;A2RaA3S58R9G8G9A3A5F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Ftp;Fr;Frp;FTZ;").
Proof.
  intros TZ rp r tp md HA (BW & BL & BOUT & BIN & _) C1 C2 C3 C4 HMI MU3.
  destruct CH as (CH4 & CH3 & CH5 & CH6).
  set (aw := Z_to_bv 64 h). set (nw := Z_to_bv 64 msz). set (r4 := set_rm r (unmap_range (rm r) aw nw)).
  set (v := view segsA (rm rp)). set (v2 := view segsA (rm r)). set (v4 := view segsA (rm r4)).
  assert (INR : forall x : word, SysStep.in_range aw nw x = true <-> chunk_zone ch (bv_unsigned x)).
  { intros x. rewrite SysStep.in_range_spec. unfold aw, nw, chunk_zone. fold h msz. rewrite !u64_lit by lia. tauto. }
  assert (V4OUT : forall z, ~ chunk_zone ch z -> v4 z = v2 z).
  { intros z NZ. unfold v4, v2. apply view_agree. intros Hz. unfold r4. cbn [rm set_rm]. rewrite unmap_range_at.
    destruct (SysStep.in_range aw nw (Z_to_bv 64 z)) eqn:EI; [|reflexivity]. exfalso. apply NZ. pose proof (proj1 (INR _) EI) as X0. rewrite u64_lit in X0 by lia. exact X0. }
  assert (CELL4 : forall c, cell_ok v2 c -> (forall z, c_addr c <= z < c_addr c + Z.of_nat (c_w c) -> ~ chunk_zone ch z) -> cell_ok v4 c).
  { intros [ca cw cv] Hc Hz. apply (cell_ok_frame1 v2 v4 ca cw cv); [|exact Hc]. intros z Hzz. apply V4OUT. apply Hz. cbn [c_addr c_w]. exact Hzz. }
  assert (JOFF : forall z, sec_junk_zone z \/ chunk_sh_zone ch z -> ~ chunk_zone ch z).
  { intros z [HZ|HZ] HC; unfold chunk_zone in HC; fold h msz in HC.
    - unfold sec_junk_zone, SEC_INST in HZ. lia.
    - unfold chunk_sh_zone in HZ. fold h msz in HZ. pose proof (Z.div_pos h 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound (h + msz) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
      unfold Sh, SHADOW_OFF, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *. lia. }
  unfold kPtrArrayReserve in *.
  pose proof (AInvA_unmap_live A rp r4 tp md l1 l2 p n i ch HA HLV HPR HI HU) as LAW. cbv zeta in LAW. fold h msz in LAW. apply LAW; clear LAW.
  - intros i0. exact (BW i0).
  - intros l0. exact (BL l0).
  - intros z N2' N3' N4' N5'. transitivity (v2 z); [exact (V4OUT z N4') | apply BOUT; unfold DUZh; tauto].
  - intros z HZ Hd. change (v4 z <> None). rewrite (V4OUT z (JOFF z HZ)). apply BIN; [unfold DUZh; tauto | exact Hd].
  - apply (CELL4 _ C1). intros z Hz. cbn [c_addr c_w] in Hz. unfold chunk_zone, SEC_INST in *. fold h msz. lia.
  - apply (CELL4 _ C2). intros z Hz. cbn [c_addr c_w] in Hz. unfold chunk_zone. fold h msz. lia.
  - intros lst0 Hl0. rewrite Hl in Hl0. injection Hl0 as <-. split.
    + intros Hlt. destruct l; [pose proof (HLT eq_refl) as EI; exfalso; pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)); lia|]. destruct (C3 eq_refl) as [C3a C3b]. split.
      * apply (CELL4 _ C3a). intros z Hz. cbn [c_addr c_w] in Hz. unfold chunk_zone. fold h msz. pose proof (HLF eq_refl). lia.
      * apply (CELL4 _ C3b). intros z Hz. cbn [c_addr c_w] in Hz. unfold chunk_zone. fold h msz. pose proof (LSTOFF eq_refl). lia.
    + intros Heq z Hz. destruct l; [|pose proof (HLF eq_refl); exfalso; lia]. transitivity (v2 z); [apply V4OUT; unfold chunk_zone; fold h msz; pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite HI; discriminate)); lia | exact (C4 eq_refl z Hz)].
  - exact (paid_munmap_leZ segsA md tp h msz ltac:(lia) ltac:(lia) HMI MU3).
Qed.
End Unmap.

Section Node.
Variables (nW : nat) (Kc : KcA).
Hypothesis HKc : Kc_ok Kc.
Variables (A : AA) (rho1 : valuation) (l1 l2 : list (Z * Z)) (p n : Z) (i : nat) (ch lst : sec_chunk) (l : bool) (TZ : Z -> Prop).
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.
Let A2 : AA := ltac2:(tb__ "0|0|
S64VA;Vl1;Vl2;Vi;A4").
Let JF0 : jpredA := ltac2:(tb__ "0|0|
S6dVnW;S6eS27VA;VKc;Vrho1;A6").

Definition JPh : jpredA := ltac2:(tb__ "0|7|
S1bS26S36Q40A1A1S26S3bA1S3aS4S1bS1bS1VJF0;R1R4R3R2A4S1S60S5S61VA;Vi;Vch;A3VTZ;R1R5A5S1S34S33S5S19R5A1A2M0S35S6S52Z38A2U8M1ScS9S25S10S11VA;A1A2A1Z1A2A3A2S1S34G0S35Zead00U4Z0A3A2S1S0S24Vl;S27A3S1S34S33S5S19R6A1A2M2S35S6S14S13VA;A1A1SaZ8M3S9Vi;A1M4A2A2M5G1S12Vlst;A1M6A3A2S34G2S35S6G6Z18A2G1G4A3A2A2F_;S0S24Vl;S29A3SeS1S7G5R1A2S8R1S6G5G3A2A2A2S0S28S36Q8A1A1S33S5S19R8A1R2A3S33S5S19R4A1R2A3A3F_;Fz;F_;A2A2A2A2A2Lrp;A2Lmd;Ltr;Ltp;Lr;").

Definition JH2 : jpredA := ltac2:(tb__ "0|6|
S1bS26S36Q40M0A1M1A1S26S3bA1S3aS1S51S5VA2;R4R3R1A5S1VKc;R2R1A2S1S70VA2;R4A2S1S6fVA2;R4A2S1SfS72R1S6bA2S0G1S1cR6R2A2S1cVrho1;R2A2A3F_;Fv;S1SfS0S26S36Q8A1M2A1S21R5R1A2S21Vrho1;R1A2A3Fll;S1G1S3VTZ;S37G0R1A2A1A1S0S28G2A1M3S19R6R2A2S19Vrho1;R2A2A3F_;Fa;S1SeS3S61VA;Vi;Vch;R1A4A1S0G3S33S5S19R6A1R2A3S33S5S19Vrho1;A1R2A3M4A3F_;Fz;SeS3S53Vch;R1A2A1S3S0G3G4S30G2A1M5A3A1S3S0G3S33S5S19R7A1R3A3G5A3A1F_;F_;Fz;A2A2A2A2A2A2A2A2Lmd;Ltr;Ltp;Lr;").

Lemma JPh_stable : ltac2:(tb__ "0|0|
S46S5S65S50A3").
Proof.
  intros r r' tp tr md md' (Aw & Al & Am) Hme (rp & HJ & (Rw & Rl & Rout & Rin & Rrm) & C1 & C2 & C3 & C4).
  pose proof (JF_stable nW UStopLe false A Kc rho1 (stopJ_stable_le _) HKc) as HST.
  assert (Em : rm r' = rm r) by (apply functional_extensionality; intros a; symmetry; apply Am).
  exists (mkVal (rw r') (rl r') (rm rp)). split.
  - apply (HST rp (mkVal (rw r') (rl r') (rm rp)) tp tr md md'); [|exact Hme | exact HJ].
    split; [intros v Hv; cbn [rw]; rewrite <- (Rw v); apply Aw; exact Hv|]. split; [intros ll; cbn [rl]; rewrite <- (Rl ll); apply Al | intros a; reflexivity].
  - unfold blind_rel. cbn [rw rl rm]. rewrite Em. split; [split; [intros v; reflexivity | split; [intros ll; reflexivity | split; [exact Rout | split; [exact Rin | exact Rrm]]]]|]. repeat (split; [assumption|]). exact C4.
Qed.
Lemma JPh_okf : ltac2:(tb__ "0|0|
S43OF_;S45S5R1S44VKc;A1A3S45S5R2S50A3F_;Fok;").
Proof. intros ok H r t tr ms md msv' (rp & (_ & HJ) & _). apply (H r t tr ms md msv'). destruct HJ as (_ & _ & _ & HK & _). exact HK. Qed.
Lemma JPh_okpf : ltac2:(tb__ "0|0|
S43OF_;S47S5R1S44VKc;A1A3S47S5R2S50A3F_;Fok;").
Proof. intros ok H r t tr ms md x8 (rp & (_ & HJ) & _). apply (H r t tr ms md x8). destruct HJ as (_ & _ & _ & HK & _). exact HK. Qed.
Lemma JH2_stable : ltac2:(tb__ "0|0|
S46S5S65S4fA3").
Proof.
  intros r r' tp tr md md' (Aw & Al & Am) Hme (HA & HK & Htp & Htop & RW & RL & KEY & VK & PR).
  assert (Em : rm r' = rm r) by (apply functional_extensionality; intros a; symmetry; apply Am).
  split; [apply (AInvA_mat segsA A2 r' tp md md'); [unfold AInvA in *; rewrite Em; exact HA | exact Hme]|].
  split; [destruct Hme as ((mat' & ->) & _); rewrite with_vm_backing_with_vm; apply HKc; exact HK|].
  split; [unfold tp_ok in *; rewrite <- (Aw 24%positive) by (unfold NPRE; lia); exact Htp|].
  split; [unfold top_high in *; unfold V_DEPTH in *; rewrite <- (Aw 10%positive), <- (Aw 15%positive) by (unfold NPRE; lia); exact Htop|].
  split; [intros v Hv; rewrite <- (Aw v) by (unfold NPRE, GW in *; lia); exact (RW v Hv)|]. split; [intros ll; rewrite <- (Al ll); exact (RL ll)|].
  rewrite Em. exact (conj KEY (conj VK PR)).
Qed.
Lemma JH2_okf : ltac2:(tb__ "0|0|
S43OF_;S45S5R1S44VKc;A1A3S45S5R2S4fA3F_;Fok;").
Proof. intros ok H r t tr ms md msv' (_ & HK & _). exact (H r t tr ms md msv' HK). Qed.
Lemma JH2_okpf : ltac2:(tb__ "0|0|
S43OF_;S47S5R1S44VKc;A1A3S47S5R2S4fA3F_;Fok;").
Proof. intros ok H r t tr ms md x8 (_ & HK & _). exact (H r t tr ms md x8 HK). Qed.
End Node.

Section NodePre.
Variables (nW : nat) (Kc : KcA).
Hypothesis HKc : Kc_ok Kc.
Variables (A : AA) (rho1 : valuation) (l1 l2 : list (Z * Z)) (p n : Z) (i : nat) (ch lst : sec_chunk) (l : bool) (TZ : Z -> Prop).
Hypothesis HZTc : ltac2:(tb__ "0|0|
SeS53Vch;R1A2VTZ;R2A1F_;Fz;").
Let h : Z := sc_map_beg ch.
Let msz : Z := sc_map_size ch.
Hypothesis HLV : ltac2:(tb__ "0|1|
S0S26S2cSeSeA2M0A1S15VA;A1S2dG0Vl1;S2eG0S2aSeSeVp;Vn;A4Vl2;A3A3A3").
Hypothesis HPR : is_primary n = false.
Hypothesis HI : ltac2:(tb__ "0|0|
S0S28S10A1S4dS10S11VA;A1Vi;A3S2bS10Vch;A2A3").
Hypothesis HU : ltac2:(tb__ "0|0|
S0SeVp;S6S6S12Vch;A1S4aA2Z800A2A3").
Hypothesis Hl : ltac2:(tb__ "0|1|
S0S28S10A1S4dS10S11VA;A1M0S39S25S10G0A2U1A2A3S2bS10Vlst;A2A3").
Hypothesis HLT : ltac2:(tb__ "0|0|
S0S24Vl;S29A3S0S2fVi;S39S25S10S11VA;A1A2U1A2A3F_;").
Hypothesis HLF : ltac2:(tb__ "0|0|
S0S24Vl;S27A3S57Vi;S39S25S10S11VA;A1A2U1A2A2F_;").
Hypothesis CH : ltac2:(tb__ "0|1|
S1S7Z643000Vh;A2S1S8Z0Vmsz;A2S1S8S6Vh;Vmsz;A2M0SbZ2Z2fA2A2S2S7G0S4cA2S7S4bVh;A2A2A2A2A2").
Hypothesis CHM : h mod 4096 = 0.
Hypothesis LSTOFF : ltac2:(tb__ "0|1|
S0S24Vl;S27A3S2S7S6S12Vlst;A1M0Z20A2Vh;A2S7S6Vh;Vmsz;A2G0A2A2F_;").
Hypothesis PABOFF : ltac2:(tb__ "0|1|
S2S7S6S14S13VA;A1A1M0S49A2Vh;A2S7S6Vh;Vmsz;A2G0A2A2").
Hypothesis NCB : ltac2:(tb__ "0|0|
S7SaZ8S9S25S10S11VA;A1A2A1A2S49A2").
Hypothesis HPIN : ltac2:(tb__ "0|3|
S1S0S36Q40M0A1M1S1cVrho1;P97A2S38G0S18S13VA;A1M2A1A2A3S1S0G1S1cVrho1;P98A2S38G0S16G2A1A2A3S0G1S1cVrho1;P9bA2S38G0S17G2A1A2A3A2A2").
Variable EUd : axst.
Hypothesis NA0 : ltac2:(tb__ "0|0|
S0S1aS22S5cVEUd;A1ZaA2S71A3").
Hypothesis NAX : ax_X EUd = [].

Lemma mun_pre : ltac2:(tb__ "0|d|
S1bS26S36Q40M0A1M1A1S0G1S1cR2PcaA2S38G0Vh;A2A3S1eS4eS1eR1S23S5cVEUd;A1A1A3M2S20S1fR5R2A2S2aSeSeVh;S6Vh;Vmsz;A2A4A2F_;Fo;S26S3bA1M3S66S3aS48S5R7R6VEUd;S2aG3S68R3S69R2R1A2A4A5S63VnW;VKc;VA;Vrho1;Vi;Vch;Vlst;Vl;VTZ;R8R7R4R2AdS67R4U0A2G1S1S0SeSdS37G0R1A2M4S42A2Z0A3S1S7S6G4Vmsz;A2M5S40A2S1S0S24S41S3dS3cR4A1A1M6R1S38G0Vmsz;A2M7A3S29A3S1G1S4eS2cG1G1A2S2aG1G1R2R1A4S3dS3cR5A1A1A3S0G1R2G7A3F_;Fs;S1S0S24S3fS3eG6R1A2R1G7A3S29A3S1S1eG2S20S1fRcR2A2S2aSeSeS37G0R3A2M8S6G8Vmsz;A2A4A2F_;Fo;S1S2cS1aS1aA2M9SeS4eG9R2S5dVEUd;A1A3S1S7S37G0S1dRdS31S1aS1aR3A3A2A2MaR2A2S8R2S6GaS37G0S1dRdS32S1aS1aR3A3A2A2A2A2A2S3S1S7S37G0R5A2MbS37G0S5fS37G0S1dReS5eVEUd;A1A2A2R3A2A2McA2S8GcS6GbVmsz;A2A2A2A1F_;F_;Fy;Frr;S62VKc;VA;Vrho1;Vl1;Vl2;Vi;Vch;VTZ;S5aRaS59S19RaA1R1G7A3A2S5bG4G5R9A3R6S58R4R1G7A3AcA2A2A2A2A2A2A2Ta;F_;F_;Fmd;Fms;Ftr;F_;F_;Ftp;Fr;").
Proof.
  intros r tp E202 HDISJ tr ms md Hsp (rp & (Hag & HA & _ & _ & HK & Htp & _ & Htop) & BR & C1 & C2 & C3 & C4). cbv zeta.
  destruct CH as (CH4 & CH3 & CH5 & CH6). destruct HPIN as (P151 & P152 & P155).
  destruct (pending_argsA segsA r tp EUd tr ms md Hsp) as (G0 & _). rewrite NA0 in G0. unfold vH in G0. cbn [eval] in G0. rewrite E202 in G0. rewrite G0. rewrite (u64_lit h) by lia.

  set (rpK := rho_sets rp [(156%positive, Z_to_bv 64 (ag_spacebeg (aa_geom A) + kSpaceSize))]).
  assert (ERM : rm rpK = rm rp) by (unfold rpK; apply rm_rho_sets).
  assert (OTH : forall v, v <> 156%positive -> rw rpK v = rw rp v) by (intros v Hv; unfold rpK; rewrite rho_sets_other; [reflexivity | cbn; intros [E|[]]; congruence]).
  assert (RP : forall v, (v < GW)%positive -> rw rp v = rw rho1 v) by (intros v Hv; symmetry; exact (proj1 Hag v Hv)).
  assert (HK0 : K0 Kc A rpK tp tr md).
  { split; [|split; [exact HK|split; [|split]]].
    - pose proof (AInvA_Q A rp tp md HA) as HQ. unfold AInvQ in *. rewrite ERM. exact HQ.
    - unfold tp_ok in *. rewrite OTH by discriminate. exact Htp.
    - unfold top_high in *. unfold V_DEPTH in *. rewrite !OTH by discriminate. exact Htop.
    - unfold rigidQ. rewrite !OTH by discriminate. rewrite !RP by (unfold GW; lia). split; [exact P151|]. split; [exact P152|]. split; [exact P155|].
      unfold rpK. apply rho_sets_get; [cbn; repeat constructor; cbn; tauto | cbn; tauto]. }
  destruct (ks_munmap_ok segsA (K0 Kc) (K0_sec Kc HKc) A rpK tp tr md HK0 ch (nth_error_In _ _ HI)) as (MU1 & MU2 & MU3). fold h msz in MU1, MU2, MU3.
  split; [unfold page_size; exact CHM|]. split; [unfold TASK_SIZE; lia|]. split; [exact MU1|]. split; [exact MU2|]. split; [exact MU3|]. split; [exact HDISJ|].
  split; [intros rr y Hin; rewrite NAX in Hin; destruct Hin|].
  pose proof (unmap_inv A l1 l2 p n i ch lst l HLV HPR HI HU Hl HLT HLF (conj CH4 (conj CH3 (conj CH5 CH6))) LSTOFF PABOFF NCB TZ rp r tp md HA BR C1 C2 C3 C4
                (smatch_pendingA_MI segsA _ _ _ _ _ _ Hsp) MU3) as HA2. fold h msz in HA2.
  destruct BR as (BW & BL & BOUT & BIN & BRM).
  assert (INR : forall x : word, SysStep.in_range (Z_to_bv 64 h) (Z_to_bv 64 msz) x = true <-> chunk_zone ch (bv_unsigned x)).
  { intros x. rewrite SysStep.in_range_spec. unfold chunk_zone. fold h msz. rewrite !u64_lit by lia. tauto. }
  assert (V4OUT : forall z, ~ chunk_zone ch z -> view segsA (rm (set_rm r (unmap_range (rm r) (Z_to_bv 64 h) (Z_to_bv 64 msz)))) z = view segsA (rm r) z).
  { intros z NZ. apply view_agree. intros Hz. cbn [rm set_rm]. rewrite unmap_range_at.
    destruct (SysStep.in_range (Z_to_bv 64 h) (Z_to_bv 64 msz) (Z_to_bv 64 z)) eqn:EI; [|reflexivity]. exfalso. apply NZ. pose proof (proj1 (INR _) EI) as X0. rewrite u64_lit in X0 by lia. exact X0. }
  assert (VRP : forall z, view segsA (rm rp) z = view segsA (rm rho1) z) by (intros z; apply view_agree; intros _; symmetry; exact (proj2 (proj2 Hag) _)).
  split; [exact HA2|]. split; [exact (HKc tr md (m_vm (munmap_model md (Z_to_bv 64 h) (Z_to_bv 64 msz))) HK)|].
  split; [unfold tp_ok in *; cbn [rw set_rm]; rewrite BW; exact Htp|].
  split; [unfold top_high in *; unfold V_DEPTH in *; cbn [rw set_rm]; rewrite !BW; exact Htop|].
  split; [intros v Hv; cbn [rw set_rm]; rewrite BW; exact (RP v Hv)|]. split; [intros ll; cbn [rl set_rm]; rewrite BL; symmetry; exact (proj1 (proj2 Hag) ll)|].
  split; [|split].
  - intros a0 NT. cbn [rm set_rm]. rewrite unmap_range_at.
    destruct (SysStep.in_range (Z_to_bv 64 h) (Z_to_bv 64 msz) a0) eqn:EI; [exfalso; apply NT; apply HZTc; exact (proj1 (INR a0) EI)|].
    rewrite (BRM a0 NT). symmetry. exact (proj2 (proj2 Hag) a0).
  - intros z NZ. rewrite V4OUT by (intros HC; apply NZ; left; exact HC). rewrite (BOUT z NZ). exact (VRP z).
  - intros z NC Hp. rewrite V4OUT by exact NC. rewrite <- VRP in Hp.
    intros HN. assert (NN : ~ ~ (DUZh A i ch z \/ ~ DUZh A i ch z)) by tauto. apply NN. intros [HZ|NZ]; [exact (BIN z HZ Hp HN) | rewrite (BOUT z NZ) in HN; exact (Hp HN)].
Qed.
End NodePre.
End F0A_hbN_unmap.

(* [comment removed for export] *)
Module F0A_hbLN2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert"; "mkHBV"; "mkHBF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbLN2"; "AM_LN2_0L"; "AM_LN2_0M"; "AU_LN2_0L"; "AU_LN2_0M"; "C5_LN2_0L"; "C5_LN2_0M"; "DUo_LN2_0L"; "DUo_LN2_0M"; "E5_LN2_0L"; "E5_LN2_0M"; "EM_LN2_0L"; "EM_LN2_0M"; "EMd_LN2_0L"; "EMd_LN2_0M"; "EMx_LN2_0L"; "EMx_LN2_0M"; "EU_LN2_0L"; "EU_LN2_0M"; "EUd_LN2_0L"; "EUd_LN2_0M"; "EUs_LN2_0L"; "EUs_LN2_0M"; "EUx_LN2_0L"; "EUx_LN2_0M"; "LA_LN2_0"; "LR_LN2_0L"; "LR_LN2_0M"; "PT_LN2_0L"; "PT_LN2_0M"; "R5_LN2_0L"; "R5_LN2_0M"; "S0_LN2_0"; "SC_LN2_0"; "SX_LN2_0L"; "SX_LN2_0M"; "T5_LN2_0L"; "T5_LN2_0M"; "T5f_LN2_0L"; "T5f_LN2_0M"; "XF_LN2_0L"; "XF_LN2_0M"; "lPA_LN2_0"; "lPB_LN2_0L"; "lPB_LN2_0M"; "lPC_LN2_0L"; "lPC_LN2_0M"; "lPD_LN2_0L"; "lPD_LN2_0M"; "lPE_LN2_0L"; "lPE_LN2_0M"; "lPL_LN2_0"; "lPT_LN2_0L"; "lPT_LN2_0M"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln F0A_cLN2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_cert.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_cLN2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Ltac vml := match goal with |- ?l = _ => vm_cast_no_check (@eq_refl _ l) end.
Ltac nxr := split; [vmr | vmr].

Definition E_LN2 : axst := Eval vm_compute in Erc_LN2.
Lemma FRESH_LN2 : hb_fresh E_LN2 = true. Proof. vmr. Qed.

Definition S0_LN2_0 : axst := Eval vm_compute in (S0_hb E_LN2 0).
Definition lPA_LN2_0 : list leafA := Eval vm_compute in (runA 300 [GBSCAN; GBEXIT] S0_LN2_0).
Definition LA_LN2_0 : axst := Eval vm_compute in (leaf 0 lPA_LN2_0).
Definition SC_LN2_0 : axst := Eval vm_compute in (SC_hb LA_LN2_0).
Definition lPL_LN2_0 : list leafA := Eval vm_compute in (runA 100 [GBSCAN; GBEXIT] SC_LN2_0).
Definition FAM_LN2_0 : hbfam := ltac2:(tb__ "0|0|
S1S21S2bS1aS22S34A5").
Lemma FAM_LN2_0_ok : hbfam_ok Erc_LN2 0 FAM_LN2_0.
Proof.
  constructor; cbn [hf_S0 hf_lPA hf_LA hf_SC hf_lPL].
  - Time vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
Qed.

Definition SX_LN2_0L : axst := Eval vm_compute in (SX_hb SC_LN2_0 0 true).
Definition lPB_LN2_0L : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_LN2_0L).
Definition E5_LN2_0L : axst := Eval vm_compute in (leaf 0 lPB_LN2_0L).
Definition C5_LN2_0L : axst := Eval vm_compute in (C5_hb E5_LN2_0L).
Definition R5_LN2_0L : list sobj := Eval vm_compute in (R5_hb C5_LN2_0L).
Definition T5_LN2_0L : axst := Eval vm_compute in (T5_hb C5_LN2_0L).
Definition T5f_LN2_0L : axst := Eval vm_compute in (T5f_hb C5_LN2_0L).
Definition lPC_LN2_0L : list leafA := Eval vm_compute in (runA 900 [] T5f_LN2_0L).
Definition EUs_LN2_0L : axst := Eval vm_compute in (leaf 0 lPC_LN2_0L).
Definition EM_LN2_0L : axst := Eval vm_compute in (leaf 1 lPC_LN2_0L).
Definition EMx_LN2_0L : axst := Eval vm_compute in (selX EM_LN2_0L [O_csh vH vMS]).
Definition EMd_LN2_0L : axst := Eval vm_compute in (EMd_hb EM_LN2_0L).
Definition AM_LN2_0L : axst := Eval vm_compute in (A_after EMd_LN2_0L (SLit 0)).
Definition lPD_LN2_0L : list leafA := Eval vm_compute in (runA 900 [] AM_LN2_0L).
Definition EU_LN2_0L : axst := Eval vm_compute in (leaf 0 lPD_LN2_0L).
Definition EUx_LN2_0L : axst := Eval vm_compute in (selX EU_LN2_0L (D_U_hb true)).
Definition EUd_LN2_0L : axst := Eval vm_compute in (EUd_hb EU_LN2_0L true).
Definition DUo_LN2_0L : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_LN2_0L))) (ss_objs (ax_S EUx_LN2_0L))).
Definition AU_LN2_0L : axst := Eval vm_compute in (A_after EUd_LN2_0L (SLit 0)).
Definition lPE_LN2_0L : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_LN2_0L).
Definition LR_LN2_0L : axst := Eval vm_compute in (leaf 0 lPE_LN2_0L).
Definition PT_LN2_0L : axst := Eval vm_compute in (PT_hb LR_LN2_0L).
Definition lPT_LN2_0L : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_LN2_0L).
Definition XF_LN2_0L : axst := Eval vm_compute in (leaf 0 lPT_LN2_0L).
Definition VAR_LN2_0L : hbvar := ltac2:(tb__ "0|0|
S0S23S2cSaS6S1fS25S27S2eS16ScS10SeS2S30S12S18S14S8S4S32S1bS1dS35S29A18").
Lemma VAR_LN2_0L_ok : hbvar_ok SC_LN2_0 0 true VAR_LN2_0L.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.

Definition SX_LN2_0M : axst := Eval vm_compute in (SX_hb SC_LN2_0 0 false).
Definition lPB_LN2_0M : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_LN2_0M).
Definition E5_LN2_0M : axst := Eval vm_compute in (leaf 0 lPB_LN2_0M).
Definition C5_LN2_0M : axst := Eval vm_compute in (C5_hb E5_LN2_0M).
Definition R5_LN2_0M : list sobj := Eval vm_compute in (R5_hb C5_LN2_0M).
Definition T5_LN2_0M : axst := Eval vm_compute in (T5_hb C5_LN2_0M).
Definition T5f_LN2_0M : axst := Eval vm_compute in (T5f_hb C5_LN2_0M).
Definition lPC_LN2_0M : list leafA := Eval vm_compute in (runA 900 [] T5f_LN2_0M).
Definition EUs_LN2_0M : axst := Eval vm_compute in (leaf 0 lPC_LN2_0M).
Definition EM_LN2_0M : axst := Eval vm_compute in (leaf 1 lPC_LN2_0M).
Definition EMx_LN2_0M : axst := Eval vm_compute in (selX EM_LN2_0M [O_csh vH vMS]).
Definition EMd_LN2_0M : axst := Eval vm_compute in (EMd_hb EM_LN2_0M).
Definition AM_LN2_0M : axst := Eval vm_compute in (A_after EMd_LN2_0M (SLit 0)).
Definition lPD_LN2_0M : list leafA := Eval vm_compute in (runA 900 [] AM_LN2_0M).
Definition EU_LN2_0M : axst := Eval vm_compute in (leaf 0 lPD_LN2_0M).
Definition EUx_LN2_0M : axst := Eval vm_compute in (selX EU_LN2_0M (D_U_hb false)).
Definition EUd_LN2_0M : axst := Eval vm_compute in (EUd_hb EU_LN2_0M false).
Definition DUo_LN2_0M : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_LN2_0M))) (ss_objs (ax_S EUx_LN2_0M))).
Definition AU_LN2_0M : axst := Eval vm_compute in (A_after EUd_LN2_0M (SLit 0)).
Definition lPE_LN2_0M : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_LN2_0M).
Definition LR_LN2_0M : axst := Eval vm_compute in (leaf 0 lPE_LN2_0M).
Definition PT_LN2_0M : axst := Eval vm_compute in (PT_hb LR_LN2_0M).
Definition lPT_LN2_0M : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_LN2_0M).
Definition XF_LN2_0M : axst := Eval vm_compute in (leaf 0 lPT_LN2_0M).
Definition VAR_LN2_0M : hbvar := ltac2:(tb__ "0|0|
S0S24S2dSbS7S20S26S28S2fS17SdS11SfS3S31S13S19S15S9S5S33S1cS1eS36S2aA18").
Lemma VAR_LN2_0M_ok : hbvar_ok SC_LN2_0 0 false VAR_LN2_0M.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.
End F0A_hbLN2.

(* [comment removed for export] *)
Module F0A_hbN2.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert"; "mkHBV"; "mkHBF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.F0A_hbN2"; "AM_N2_1L"; "AM_N2_1M"; "AM_N2_2L"; "AM_N2_2M"; "AU_N2_1L"; "AU_N2_1M"; "AU_N2_2L"; "AU_N2_2M"; "C5_N2_1L"; "C5_N2_1M"; "C5_N2_2L"; "C5_N2_2M"; "DUo_N2_1L"; "DUo_N2_1M"; "DUo_N2_2L"; "DUo_N2_2M"; "E5_N2_1L"; "E5_N2_1M"; "E5_N2_2L"; "E5_N2_2M"; "EM_N2_1L"; "EM_N2_1M"; "EM_N2_2L"; "EM_N2_2M"; "EMd_N2_1L"; "EMd_N2_1M"; "EMd_N2_2L"; "EMd_N2_2M"; "EMx_N2_1L"; "EMx_N2_1M"; "EMx_N2_2L"; "EMx_N2_2M"; "EU_N2_1L"; "EU_N2_1M"; "EU_N2_2L"; "EU_N2_2M"; "EUd_N2_1L"; "EUd_N2_1M"; "EUd_N2_2L"; "EUd_N2_2M"; "EUs_N2_1L"; "EUs_N2_1M"; "EUs_N2_2L"; "EUs_N2_2M"; "EUx_N2_1L"; "EUx_N2_1M"; "EUx_N2_2L"; "EUx_N2_2M"; "LA_N2_1"; "LA_N2_2"; "LR_N2_1L"; "LR_N2_1M"; "LR_N2_2L"; "LR_N2_2M"; "PT_N2_1L"; "PT_N2_1M"; "PT_N2_2L"; "PT_N2_2M"; "R5_N2_1L"; "R5_N2_1M"; "R5_N2_2L"; "R5_N2_2M"; "S0_N2_1"; "S0_N2_2"; "SC_N2_1"; "SC_N2_2"; "SX_N2_1L"; "SX_N2_1M"; "SX_N2_2L"; "SX_N2_2M"; "T5_N2_1L"; "T5_N2_1M"; "T5_N2_2L"; "T5_N2_2M"; "T5f_N2_1L"; "T5f_N2_1M"; "T5f_N2_2L"; "T5f_N2_2M"; "XF_N2_1L"; "XF_N2_1M"; "XF_N2_2L"; "XF_N2_2M"; "lPA_N2_1"; "lPA_N2_2"; "lPB_N2_1L"; "lPB_N2_1M"; "lPB_N2_2L"; "lPB_N2_2M"; "lPC_N2_1L"; "lPC_N2_1M"; "lPC_N2_2L"; "lPC_N2_2M"; "lPD_N2_1L"; "lPD_N2_1M"; "lPD_N2_2L"; "lPD_N2_2M"; "lPE_N2_1L"; "lPE_N2_1M"; "lPE_N2_2L"; "lPE_N2_2M"; "lPL_N2_1"; "lPL_N2_2"; "lPT_N2_1L"; "lPT_N2_1M"; "lPT_N2_2L"; "lPT_N2_2M"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymEntail SymFrame SymCFG SymCall SymSummary Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import StepA EntailA CFGA GlueA SummaryA SysCallA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import MuslMemset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Str_memcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require n3.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.Str_memcpy OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.n3.Str_memset.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Geometry Model Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.CertMallocS1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ig.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_skeln F0A_cN2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require kf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_hbN_cert.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.F0A_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j3.F0A_xdefs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_skeln OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_cN2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.kf.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_hbN_cert.
Import ListNotations.
Open Scope Z_scope.
Ltac vmr := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Ltac vml := match goal with |- ?l = _ => vm_cast_no_check (@eq_refl _ l) end.
Ltac nxr := split; [vmr | vmr].

Definition E_N2 : axst := Eval vm_compute in Erc_N2.
Lemma FRESH_N2 : hb_fresh E_N2 = true. Proof. vmr. Qed.

Definition S0_N2_1 : axst := Eval vm_compute in (S0_hb E_N2 1).
Definition lPA_N2_1 : list leafA := Eval vm_compute in (runA 300 [GBSCAN; GBEXIT] S0_N2_1).
Definition LA_N2_1 : axst := Eval vm_compute in (leaf 0 lPA_N2_1).
Definition SC_N2_1 : axst := Eval vm_compute in (SC_hb LA_N2_1).
Definition lPL_N2_1 : list leafA := Eval vm_compute in (runA 100 [GBSCAN; GBEXIT] SC_N2_1).
Definition FAM_N2_1 : hbfam := ltac2:(tb__ "0|0|
S1S40S54S32S42S66A5").
Lemma FAM_N2_1_ok : hbfam_ok Erc_N2 1 FAM_N2_1.
Proof.
  constructor; cbn [hf_S0 hf_lPA hf_LA hf_SC hf_lPL].
  - Time vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
Qed.

Definition SX_N2_1L : axst := Eval vm_compute in (SX_hb SC_N2_1 1 true).
Definition lPB_N2_1L : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N2_1L).
Definition E5_N2_1L : axst := Eval vm_compute in (leaf 0 lPB_N2_1L).
Definition C5_N2_1L : axst := Eval vm_compute in (C5_hb E5_N2_1L).
Definition R5_N2_1L : list sobj := Eval vm_compute in (R5_hb C5_N2_1L).
Definition T5_N2_1L : axst := Eval vm_compute in (T5_hb C5_N2_1L).
Definition T5f_N2_1L : axst := Eval vm_compute in (T5f_hb C5_N2_1L).
Definition lPC_N2_1L : list leafA := Eval vm_compute in (runA 900 [] T5f_N2_1L).
Definition EUs_N2_1L : axst := Eval vm_compute in (leaf 0 lPC_N2_1L).
Definition EM_N2_1L : axst := Eval vm_compute in (leaf 1 lPC_N2_1L).
Definition EMx_N2_1L : axst := Eval vm_compute in (selX EM_N2_1L [O_csh vH vMS]).
Definition EMd_N2_1L : axst := Eval vm_compute in (EMd_hb EM_N2_1L).
Definition AM_N2_1L : axst := Eval vm_compute in (A_after EMd_N2_1L (SLit 0)).
Definition lPD_N2_1L : list leafA := Eval vm_compute in (runA 900 [] AM_N2_1L).
Definition EU_N2_1L : axst := Eval vm_compute in (leaf 0 lPD_N2_1L).
Definition EUx_N2_1L : axst := Eval vm_compute in (selX EU_N2_1L (D_U_hb true)).
Definition EUd_N2_1L : axst := Eval vm_compute in (EUd_hb EU_N2_1L true).
Definition DUo_N2_1L : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N2_1L))) (ss_objs (ax_S EUx_N2_1L))).
Definition AU_N2_1L : axst := Eval vm_compute in (A_after EUd_N2_1L (SLit 0)).
Definition lPE_N2_1L : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N2_1L).
Definition LR_N2_1L : axst := Eval vm_compute in (leaf 0 lPE_N2_1L).
Definition PT_N2_1L : axst := Eval vm_compute in (PT_hb LR_N2_1L).
Definition lPT_N2_1L : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N2_1L).
Definition XF_N2_1L : axst := Eval vm_compute in (leaf 0 lPT_N2_1L).
Definition VAR_N2_1L : hbvar := ltac2:(tb__ "0|0|
S0S44S56S12SaS3cS48S4cS5aS2aS16S1eS1aS2S5eS22S2eS26SeS6S62S34S38S68S50A18").
Lemma VAR_N2_1L_ok : hbvar_ok SC_N2_1 1 true VAR_N2_1L.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.

Definition SX_N2_1M : axst := Eval vm_compute in (SX_hb SC_N2_1 1 false).
Definition lPB_N2_1M : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N2_1M).
Definition E5_N2_1M : axst := Eval vm_compute in (leaf 0 lPB_N2_1M).
Definition C5_N2_1M : axst := Eval vm_compute in (C5_hb E5_N2_1M).
Definition R5_N2_1M : list sobj := Eval vm_compute in (R5_hb C5_N2_1M).
Definition T5_N2_1M : axst := Eval vm_compute in (T5_hb C5_N2_1M).
Definition T5f_N2_1M : axst := Eval vm_compute in (T5f_hb C5_N2_1M).
Definition lPC_N2_1M : list leafA := Eval vm_compute in (runA 900 [] T5f_N2_1M).
Definition EUs_N2_1M : axst := Eval vm_compute in (leaf 0 lPC_N2_1M).
Definition EM_N2_1M : axst := Eval vm_compute in (leaf 1 lPC_N2_1M).
Definition EMx_N2_1M : axst := Eval vm_compute in (selX EM_N2_1M [O_csh vH vMS]).
Definition EMd_N2_1M : axst := Eval vm_compute in (EMd_hb EM_N2_1M).
Definition AM_N2_1M : axst := Eval vm_compute in (A_after EMd_N2_1M (SLit 0)).
Definition lPD_N2_1M : list leafA := Eval vm_compute in (runA 900 [] AM_N2_1M).
Definition EU_N2_1M : axst := Eval vm_compute in (leaf 0 lPD_N2_1M).
Definition EUx_N2_1M : axst := Eval vm_compute in (selX EU_N2_1M (D_U_hb false)).
Definition EUd_N2_1M : axst := Eval vm_compute in (EUd_hb EU_N2_1M false).
Definition DUo_N2_1M : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N2_1M))) (ss_objs (ax_S EUx_N2_1M))).
Definition AU_N2_1M : axst := Eval vm_compute in (A_after EUd_N2_1M (SLit 0)).
Definition lPE_N2_1M : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N2_1M).
Definition LR_N2_1M : axst := Eval vm_compute in (leaf 0 lPE_N2_1M).
Definition PT_N2_1M : axst := Eval vm_compute in (PT_hb LR_N2_1M).
Definition lPT_N2_1M : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N2_1M).
Definition XF_N2_1M : axst := Eval vm_compute in (leaf 0 lPT_N2_1M).
Definition VAR_N2_1M : hbvar := ltac2:(tb__ "0|0|
S0S45S57S13SbS3dS49S4dS5bS2bS17S1fS1bS3S5fS23S2fS27SfS7S63S35S39S69S51A18").
Lemma VAR_N2_1M_ok : hbvar_ok SC_N2_1 1 false VAR_N2_1M.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.

Definition S0_N2_2 : axst := Eval vm_compute in (S0_hb E_N2 2).
Definition lPA_N2_2 : list leafA := Eval vm_compute in (runA 300 [GBSCAN; GBEXIT] S0_N2_2).
Definition LA_N2_2 : axst := Eval vm_compute in (leaf 0 lPA_N2_2).
Definition SC_N2_2 : axst := Eval vm_compute in (SC_hb LA_N2_2).
Definition lPL_N2_2 : list leafA := Eval vm_compute in (runA 100 [GBSCAN; GBEXIT] SC_N2_2).
Definition FAM_N2_2 : hbfam := ltac2:(tb__ "0|0|
S1S41S55S33S43S67A5").
Lemma FAM_N2_2_ok : hbfam_ok Erc_N2 2 FAM_N2_2.
Proof.
  constructor; cbn [hf_S0 hf_lPA hf_LA hf_SC hf_lPL].
  - Time vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
Qed.

Definition SX_N2_2L : axst := Eval vm_compute in (SX_hb SC_N2_2 2 true).
Definition lPB_N2_2L : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N2_2L).
Definition E5_N2_2L : axst := Eval vm_compute in (leaf 0 lPB_N2_2L).
Definition C5_N2_2L : axst := Eval vm_compute in (C5_hb E5_N2_2L).
Definition R5_N2_2L : list sobj := Eval vm_compute in (R5_hb C5_N2_2L).
Definition T5_N2_2L : axst := Eval vm_compute in (T5_hb C5_N2_2L).
Definition T5f_N2_2L : axst := Eval vm_compute in (T5f_hb C5_N2_2L).
Definition lPC_N2_2L : list leafA := Eval vm_compute in (runA 900 [] T5f_N2_2L).
Definition EUs_N2_2L : axst := Eval vm_compute in (leaf 0 lPC_N2_2L).
Definition EM_N2_2L : axst := Eval vm_compute in (leaf 1 lPC_N2_2L).
Definition EMx_N2_2L : axst := Eval vm_compute in (selX EM_N2_2L [O_csh vH vMS]).
Definition EMd_N2_2L : axst := Eval vm_compute in (EMd_hb EM_N2_2L).
Definition AM_N2_2L : axst := Eval vm_compute in (A_after EMd_N2_2L (SLit 0)).
Definition lPD_N2_2L : list leafA := Eval vm_compute in (runA 900 [] AM_N2_2L).
Definition EU_N2_2L : axst := Eval vm_compute in (leaf 0 lPD_N2_2L).
Definition EUx_N2_2L : axst := Eval vm_compute in (selX EU_N2_2L (D_U_hb true)).
Definition EUd_N2_2L : axst := Eval vm_compute in (EUd_hb EU_N2_2L true).
Definition DUo_N2_2L : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N2_2L))) (ss_objs (ax_S EUx_N2_2L))).
Definition AU_N2_2L : axst := Eval vm_compute in (A_after EUd_N2_2L (SLit 0)).
Definition lPE_N2_2L : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N2_2L).
Definition LR_N2_2L : axst := Eval vm_compute in (leaf 0 lPE_N2_2L).
Definition PT_N2_2L : axst := Eval vm_compute in (PT_hb LR_N2_2L).
Definition lPT_N2_2L : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N2_2L).
Definition XF_N2_2L : axst := Eval vm_compute in (leaf 0 lPT_N2_2L).
Definition VAR_N2_2L : hbvar := ltac2:(tb__ "0|0|
S0S46S58S14ScS3eS4aS4eS5cS2cS18S20S1cS4S60S24S30S28S10S8S64S36S3aS6aS52A18").
Lemma VAR_N2_2L_ok : hbvar_ok SC_N2_2 2 true VAR_N2_2L.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.

Definition SX_N2_2M : axst := Eval vm_compute in (SX_hb SC_N2_2 2 false).
Definition lPB_N2_2M : list leafA := Eval vm_compute in (runA 900 [MSENTS] SX_N2_2M).
Definition E5_N2_2M : axst := Eval vm_compute in (leaf 0 lPB_N2_2M).
Definition C5_N2_2M : axst := Eval vm_compute in (C5_hb E5_N2_2M).
Definition R5_N2_2M : list sobj := Eval vm_compute in (R5_hb C5_N2_2M).
Definition T5_N2_2M : axst := Eval vm_compute in (T5_hb C5_N2_2M).
Definition T5f_N2_2M : axst := Eval vm_compute in (T5f_hb C5_N2_2M).
Definition lPC_N2_2M : list leafA := Eval vm_compute in (runA 900 [] T5f_N2_2M).
Definition EUs_N2_2M : axst := Eval vm_compute in (leaf 0 lPC_N2_2M).
Definition EM_N2_2M : axst := Eval vm_compute in (leaf 1 lPC_N2_2M).
Definition EMx_N2_2M : axst := Eval vm_compute in (selX EM_N2_2M [O_csh vH vMS]).
Definition EMd_N2_2M : axst := Eval vm_compute in (EMd_hb EM_N2_2M).
Definition AM_N2_2M : axst := Eval vm_compute in (A_after EMd_N2_2M (SLit 0)).
Definition lPD_N2_2M : list leafA := Eval vm_compute in (runA 900 [] AM_N2_2M).
Definition EU_N2_2M : axst := Eval vm_compute in (leaf 0 lPD_N2_2M).
Definition EUx_N2_2M : axst := Eval vm_compute in (selX EU_N2_2M (D_U_hb false)).
Definition EUd_N2_2M : axst := Eval vm_compute in (EUd_hb EU_N2_2M false).
Definition DUo_N2_2M : list sobj := Eval vm_compute in (skipn (length (ss_objs (ax_S EUd_N2_2M))) (ss_objs (ax_S EUx_N2_2M))).
Definition AU_N2_2M : axst := Eval vm_compute in (A_after EUd_N2_2M (SLit 0)).
Definition lPE_N2_2M : list leafA := Eval vm_compute in (runA 900 [RET_PUT] AU_N2_2M).
Definition LR_N2_2M : axst := Eval vm_compute in (leaf 0 lPE_N2_2M).
Definition PT_N2_2M : axst := Eval vm_compute in (PT_hb LR_N2_2M).
Definition lPT_N2_2M : list leafA := Eval vm_compute in (runA FUELF [DRNE; RETF] PT_N2_2M).
Definition XF_N2_2M : axst := Eval vm_compute in (leaf 0 lPT_N2_2M).
Definition VAR_N2_2M : hbvar := ltac2:(tb__ "0|0|
S0S47S59S15SdS3fS4bS4fS5dS2dS19S21S1dS5S61S25S31S29S11S9S65S37S3bS6bS53A18").
Lemma VAR_N2_2M_ok : hbvar_ok SC_N2_2 2 false VAR_N2_2M.
Proof.
  constructor; cbn [hv_SX hv_lPB hv_E5 hv_C5 hv_R5 hv_T5 hv_T5f hv_lPC hv_EUs hv_EM hv_EMx hv_EMd hv_AM hv_lPD hv_EU hv_EUx hv_EUd hv_DUo hv_AU hv_lPE hv_LR hv_PT hv_lPT hv_XF].
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vmr.
  - vmr.
  - vmr.
  - vmr.
  - split; [vmr | split; [vmr | split; [vmr | split; [vmr | split; [vmr | vmr]]]]].
  - vmr.
  - Time vmr.
  - Time vmr.
  - nxr.
  - vml.
  - Time vmr.
  - Time vmr.
  - nxr.
Qed.
End F0A_hbN2.

(* [comment removed for export] *)
Module SegQCF_exit.

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "SLit"; "sobj"; "ss_objs"; "valuation"; "rw"; "SAlu"; "SVar"; "sprop"; "eval"; "sv_eqb"; "ob_hi"; "ob_lo"; "SExt"; "ob_base"; "sprop_eqb"; "ss_facts"; "@Corelib.Init.Datatypes"; "pair"; "prod"; "cons"; "nat"; "bool"; "nil"; "list"; "app"; "true"; "false"; "andb"; "fst"; "Some"; "length"; "option"; "S"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM"; "carve_spec"; "carve_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Model"; "qbatch"; "aa_geom"; "AA"; "aa_cache_inited"; "mkQB"; "aa_q_global"; "aa_q_thread"; "ageom"; "cs_cache"; "ag_ctx"; "ag_thread"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.AxXform"; "axform"; "AXRebase"; "AXSelect"; "apply_axforms"; "AXMerge"; "AXUnbase"; "@Corelib.Lists.ListDef"; "map"; "firstn"; "seq"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.le.SegQCF_exit"; "Lx"; "Ly"; "Lz"; "Lm"; "T_x"; "ref3"; "DSX"; "K24"; "K27"; "N_D2b"; "REFALL"; "findi"; "is3"; "N_2a"; "REF1"; "REF2a"; "REFK"; "XM1"; "dstS"; "fri"; "isfr"; "p1"; "p2"; "riS"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "@LinuxProcessSemantics.Riscv.Instr"; "ALU_ADD"; "aluop"; "mulop"; "ALU_SUB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lc.SegQCF_states"; "pcbF"; "L2"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel"; "drainA"; "drain_grows"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ"; "K0"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv"; "JRD"; "JRI"; "QP"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states"; "clsB"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2"; "cls_of"; "QW"; "push_cache"; "set_q"; "@Corelib.Init.Nat"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR"; "vMFA"; "vRI"; "vAU"; "vMU"; "vNF"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.CertStackMalloc"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Geometry"; "Size"; "PG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs"; "RCr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue"; "dspec"; "forallb2"; "dobj"; "keepN"; "same_rng"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop"; "HVX"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.SegQCF_glue"; "dstF"; "@Stdlib.ZArith.BinInt.Z"; "eqb"; "of_nat"; "add"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.Iface"; "pre_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states"; "add"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM"; "MC"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQ3D_qcs"; "cptrC";
"@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip"; "DQI0"; "N_rti"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states"; "DEPTH_R"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ls.SegQCF_call"; "ENVC"; "gmaxS"; "mtxS"; "szS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue"; "ZD_fixS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib"; "mkST"; "ro_cond"; "s_C"; "s_Cd"; "s_k"; "s_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail"; "sbS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs"; "qb_id"; "@Stdlib.Lists.List"; "existsb"; "forallb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
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
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require im.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require id.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require io.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iq.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require m9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ic.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i2.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ie.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i7.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ib.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m7.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ij.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ih.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.il.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.im.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.id.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ig.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i4.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.io.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iq.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.m9.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require i3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iu.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require je.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SegQS_glue SegQS_scan SegQS_lib.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jk.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jt.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require RefillModel DrainModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require iy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require j5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require lo.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require k3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require F0A_drain DepotCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require ls.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i6.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.i3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iu.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQS_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_scan OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegQS_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jk.SegQS_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jt.SegQS_tail OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j4.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.InvQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jd.InvQ6 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jb.InvQ9 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ia.CertMallocSR OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.RefillModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DrainModel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iy.DrainS OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.j5.DrainSG OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lc.SegQCF_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jo.SegQF_lib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.lo.SegQCF_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.je.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.InvQ7 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.k3.F0A_depot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.F0A_drain OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.DepotCall OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.ls.SegQCF_call OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jj.SegQF_ri OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.iv.SegQ3D_qcs.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require SMGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require jc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Fixpoint findi (f : sobj -> bool) (l : list sobj) (k : nat) : nat := match l with [] => k | o :: t => if f o then k else findi f t (S k) end.
Definition isfr (o : sobj) : bool := ltac2:(tb__ "0|a|
S0S15Lx;M0ScVo;A1S21G0SbVo;A1S21S1bS81R2N30A2S81R1Z0A2A2Lb;S22S1aLi;M1S5eS0S0S1aLb;M2La0;M3Lop;M4G4S5fG3Lop;M5G5S15S23S0S1aLa0;Lw;Lsgn;S22S0S21S1aLk;Li;Ll;M6X0x8La;G1S5eS0G2La;M7Lop;M8G8S5fG7Lop;M9G9S15S23S0S1aLa;Lw;Lsgn;G6X0x8").
Definition fri (g : bool) : nat := ltac2:(tb__ "0|0|
S4eS57S3S29S62Vg;A1A1A1U0A3").
Definition p1 (g : bool) : list nat := ltac2:(tb__ "0|2|
S13S14U0S13S14S56Vg;A1M0S18S14S3fU1M1S6fG0G1A2A2S3fS20G0A1S6fU1dG0A2A2A3A3A3").
Definition XM1 (g : bool) : list axform := ltac2:(tb__ "0|1|
S13S37S39S58Vg;A1A1S13S37S38U0M0A1S13S37S38U1A1S13S37S3bG0A1S13S37S3cG0Nc0A2S16S37A1A3A3A3A3A3").
Definition optA (d : axst) (o : option axst) : axst := match o with Some Y => Y | None => d end.
Definition Lm_f : axst := Eval vm_compute in (optA (L2 false) (apply_axforms (L2 false) (XM1 false))).
Definition Lm_g : axst := Eval vm_compute in (optA (L2 true) (apply_axforms (L2 true) (XM1 true))).
Definition Lm (g : bool) : axst := if g then Lm_g else Lm_f.
Lemma Lm_eq : ltac2:(tb__ "0|0|
S15S24S1fS2aA1S3aS62R1A1S54R1A1A2S1dS2aS46R1A1A2A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition is3 (b lo hi : sv) (o : sobj) : bool := ltac2:(tb__ "0|0|
S1bS1bSaSeVo;A1Vb;A2SaScVo;A1Vlo;A2A2SaSbVo;A1Vhi;A2A2").
Definition ref3 (k : carve_spec) : sv * sv * sv := ltac2:(tb__ "0|5|
S12S12S12S0S21A2M0S21A2M1S17S12S12S21S14A2S0A2A1M2A2S12S12S0S0A2M3S0A2M4Lk;Vk;G1G2G1G4Lp;R2G0S21G0G4Lp0;R2S0S21S11G3S0S11S0S0R2S1R1A1A4S1R3A1A4Llo;Lb;X12x1Lhi;Lp0;X12x1Ll;Lp;X12x1").
Definition REFK : list (sv * sv * sv) := ltac2:(tb__ "0|6|
S13S12S12S0S0A2M0S0A2M1S11G0S0S11S0S0S6S5dS7PaA1M2S1Nc0A1M3A3S6S5dS7PfA1S1Zc0A1A3A4S1Z0A1M4A4S13G1S11G0S0S11S0S0G2G3A4S1Nb8A1M5A4S13G1S11G0S0S11S0S0S6S5dG2G5A3G4A4S1Z10A1A4S13G1S11G0S0S11S0S0G2S1Na8A1A4G4A4S13G1S48S8fA1S13G1S48S8eA1S13G1S11G0S0S11S0S0G4S1Ze4868A1A4S1Ze5608A1A4S13G1S11G0S0S11S0S0G4S1Zee0b8A1A4S1Zee0c4A1A4S16G1A1A3A3A3A3A3A3A3A3").
Definition N_D2b : list carve_spec := ltac2:(tb__ "0|d|
S18S27S8bS13S12S12S12S0S21A2M0S21A2M1S17S12S12S21S14A2M2S0A2M3A1M4A2M5S11G1G4S11G0S21S11S0S21S1Z0A1M6Z17db60M7A4Z17db68A4S13G3S11G2S0S11S21S14G7U8M8A4S1S78A1A4S16G3A1M9A3A4S13G5S11G1G4S11G0S21S11S0S21G6Z17fcecMaA4Z17fcedA4S13G3S11G2S0S11S21S14GaU1A4G6A4G9A3A4S13G5S11G1G4S11G0S21S11S0S21G6Z17fc78MbA4Z17fc80A4S13G3S11G2S0S11S21S14GbG8A4G6A4G9A3A4S13G5S11G1G4S11G0S21S11S0S21S61Z4McA4Z8A4S13G3S11G2S0S11S21S14GcU4A4S1Z2A1A4G9A3A4S13S27S90S16S27A1A3A3A3A3A3A3").
Definition REF2a : list (sv * sv * sv) := ltac2:(tb__ "0|2|
S13S12S12S0S0A2M0S0A2M1S11G0S0S11S0S0S61S1Z0A1A4S1Z4A1A4S13G1S11G0S0S11S0S0S61S1Z14A1A4S1Z18A1A4S13G1S11G0S0S11S0S0S76S1Zad0A1A4S1Zc60A1A4S16G1A1A3A3A3").
Definition REF1 : list (sv * sv * sv) := ltac2:(tb__ "0|3|
S13S12S12S0S0A2M0S0A2M1S11G0S0S11S0S0S72S1Z0A1M2A4S1Z80A1A4S13G1S11G0S0S11S0S0S80G2A4S1Z4A1A4S16G1A1A3A3").
Definition REFALL : list (sv * sv * sv) := ltac2:(tb__ "0|1|
S18S12S12S0S0A2S0A2M0S53S18G0S3dS27G0S48S4cA4S18G0S52S51A3A3A3").
Definition p2 (g : bool) : list nat := ltac2:(tb__ "0|2|
S3dS12S12S0S0A2M0S0A2M1S14G1G1S14Lr;R1G0S0G0S14Lp;R2S0S0S4eS4fR2R1R3A3S3S29S46Vg;A1A1A1U0A3Llo;Lb;X12x1Lhi;Lp;X12x1Lr;S4dA4").
Definition Lx_f : axst := Eval vm_compute in (optA Lm_f (apply_axforms Lm_f [AXSelect (p2 false)])).
Definition Lx_g : axst := Eval vm_compute in (optA Lm_g (apply_axforms Lm_g [AXSelect (p2 true)])).
Definition Lx (g : bool) : axst := if g then Lx_g else Lx_f.
Lemma Lx_eq : ltac2:(tb__ "0|0|
S15S24S1fS2aA1S3aS46R1A1S13S37S39S59R1A1A1S16S37A1A3A2S1dS2aS43R1A1A2A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Lx_shape : ltac2:(tb__ "0|2|
S15S24S15S7bS2S12S12S0S0A2M0S0A2M1S2G1G1S15Lr;R1G0S0G0S15Lp;R2S0S0S4fR2R1R3R6A4Llo;Lb;X12x1Lhi;Lp;X12x1Lr;Lo;S3S29S43R1A1A1A1S4dA5S19A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Definition riS (g : bool) : carve_spec := ltac2:(tb__ "0|6|
S11S12S12S0S21A2M0S21A2S17S12S12S21S14A2M1S0A2M2A1S11G0S21S11S0S21S72Z0M3A4Z80A4S13G2S11G1S0S11S21S14G3U8M4A4S1G3A1M5A4S13G2S11G1S0S11S21S14Z10G4A4S6S5dS75S1Z1A1A3A4S13G2S11G1S0S11S21S14Z18G4A4S15S0Lg;Vg;S6S5dS71S1Z40000A1A3S71X15x2A4S13G2S11G1S0S11S21S14Z20G4A4S73A4S13G2S11G1S0S11S21S14Z28G4A4G5A4S13G2S11G1S0S11S21S14Z30G4A4S74A4S13G2S11G1S0S11S21S14Z38G4A4G5A4S13G2S11G1S0S11S21S14Z44U1A4G5A4S16G2A1A3A3A3A3A3A3A3A3A4").
Definition dstS : carve_spec := ltac2:(tb__ "0|4|
S11S12S12S0S21A2M0S21A2S17S12S12S21S14A2M1S0A2M2A1S11G0S21S11S0S21S80Z0M3A4Z4A4S13G2S11G1S0S11S21S14G3U4A4SdS19Q20S7Pe7A1A3A4S16G2A1A3A4").
Definition K27 (g : bool) : list sobj := ltac2:(tb__ "0|0|
S3eS2U1bS3S29S43Vg;A1A1A1A3").
Lemma Lx_objs1 : ltac2:(tb__ "0|0|
S15S24S17S2A1S3S29S43R1A1A1A1S18S2S4bR1A1S3dS27S2S28S13S27S5aR1A1S13S27S55S16S27A1A3A3A4A3A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Ly (g : bool) : axst := ltac2:(tb__ "0|1|
S2bS43Vg;A1M0S70S29G0A1S4bVg;A1A2A2").

Section ExitF.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).

Lemma qcf_x1 : ltac2:(tb__ "0|5|
S15S2eS21S21S21S14S17S2cA1M0G0S4S17S5cQ40A1M1A1S66S24G0S32RaA1S16S2cA1A3S24S15S2fRbA1S19A3S69VA0;RcA2S24G0S31RdA1S13S2cS30RcS16S12S21S21A2A1M2RbA3S18S2cR8R7A3A3A3S24S21S82S1eS21S34S6bReZ18M3A2A1A2A1Z2A3S24S15S64G3S6bRfG3A2A2R10A3S8dR10R9A2S41S42S68S65VKc;A1M4VA0;Vrho0;S63R11G3A2R10ReRdG2RcRbAaS43R12A1RaR9R8A6S26S4S4S25S41S42S68G4VA0;Vrho0;S63R13G3A2R12R10RfG2ReRdAaS44R14A1R1RbRaA6S22S24G1S5R2R1A2S5RdR1A2A3Fi;A2Lrho3;A2F_;F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest;Ftmp';Fnd;Fn0;Fs;Fa;FA;Fg;").
Proof.
  intros g A a s n0 nd tmp' rest rho tp [tr [ms md]] HTH HCI HQP HGL HFULL HGR (EC & E201 & E208 & E221 & E222 & E223 & E224 & E225 & E231) H.
  destruct (proj2 H) as (HK & HCB & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB, HRM, HFRM.
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (A1 := drainA A 24) in *.
  assert (EG : aa_geom A = aa_geom A0) by (destruct HQP as (ESB & _); unfold same_but_qcs in ESB; rewrite ESB; reflexivity).
  pose proof (K0_laws Kc HKc) as HL.
  destruct (kq_facts segsA (K0 Kc) HL A1 rho tp _ _ HK) as [HG HRIG _ _ _ HLEN HCLS _ _ _ _ _ _]. change (aa_geom A1) with (aa_geom A) in HG, HRIG.
  destruct HRIG as (E151 & E152 & E155 & E156).
  assert (HLA : (24 < length (aa_cls A))%nat) by (unfold A1, drainA in HLEN; cbn [aa_cls] in HLEN; rewrite length_list_upd in HLEN; lia).
  pose proof (HCLS HCI 24 ltac:(lia)) as CV1. change (aa_geom A1) with (aa_geom A) in CV1. unfold A1 in CV1. rewrite (drainA_cls A HLA) in CV1.
  set (cs := SegQ_wf2.cls_of A 24) in *. set (SB := ag_spacebeg (aa_geom A)) in *. set (nf := Z.of_nat (length (cs_free_array cs))) in *.
  pose proof (cv_fa_bounds _ _ _ _ _ CV1) as (FC1 & FC2 & FC3). unfold drain_cs in FC1, FC2, FC3. cbn [cs_free_array cs_mapped_free_array] in FC1, FC2, FC3. fold cs in HGR. rewrite HGR in FC1, FC2, FC3. unfold kFreeArrayMapSize in FC1, FC2, FC3.
  rewrite length_app, length_skipn in FC2. unfold drain_keep in FC2. change (Z.to_nat (kchunks 24)) with 1%nat in FC2.
  assert (NF0 : 0 <= nf) by (unfold nf; lia). assert (HFL : length (cs_cache cs) = 2%nat) by lia. rewrite HFL in FC2. change (Z.of_nat (length (cs_free_array cs) + (2 - (2 - 1)))) with (Z.of_nat (length (cs_free_array cs) + 1)) in FC2.
  rewrite Nat2Z.inj_add in FC2. fold nf in FC2. change (Z.of_nat 1) with 1 in FC2.
  destruct (geo_nums Kc A1 rho tp tr md HKc HK) as (S1 & S2 & _). cbv zeta in S1, S2. change (aa_geom A1) with (aa_geom A) in S1, S2. fold SB in S1, S2.
  pose proof (topG_range (aa_geom A)) as TG. unfold HIGH_SHADOW_END, kFreeArraySize in *. rewrite kSpaceSize_val in S2.
  assert (RIv : region_info SB 24 = SB + 2 ^ 37 + 3072) by (unfold region_info, kRegionInfoStride; rewrite kSpaceSize_val; lia).
  assert (FAv : free_array SB 24 = SB + 24 * 2 ^ 32 + 3758096384) by (unfold free_array, region_beg, kUserSpaceSize, kRegionSize, kFreeArraySize; lia).
  assert (ERI : bv_unsigned (eval rho vRI) = SB + 2 ^ 37 + 3072) by (unfold vRI; cbn [eval]; rewrite E225; fold SB; rewrite RIv, u64_lit by lia; reflexivity).
  assert (Edst : bv_unsigned (eval rho dstF) = SB + 24 * 2 ^ 32 + 3758096384 + 4 * nf).
  { unfold dstF. rewrite U_add, U_add, U_add, !U_sll_lit. unfold vSB, vNF. cbn [eval]. rewrite EC, E155, E221. fold SB nf. rewrite !u64_lit by lia. change (32 mod 64) with 32. change (2 mod 64) with 2.
    unfold M64v. rewrite (Z.mod_small (24 * 2 ^ 32)) by lia. rewrite (Z.mod_small (24 * 2 ^ 32 + 3758096384)) by lia. rewrite (Z.mod_small (SB + (24 * 2 ^ 32 + 3758096384))) by lia.
    rewrite (Z.mod_small (nf * 2 ^ 2)) by lia. rewrite Z.mod_small by lia. lia. }

  set (x1 := nth 1 (cs_cache cs) 0) in *.
  assert (ECA : cs_cache cs = [nth 0 (cs_cache cs) 0; x1]) by (unfold x1; destruct (cs_cache cs) as [|y0 [|y1 [|y2 l]]]; cbn in HFL; try lia; reflexivity).
  assert (EFA1 : cs_free_array (drain_cs 24 cs) = cs_free_array cs ++ [x1]).
  { unfold drain_cs, drain_keep. cbn [cs_free_array]. change (Z.to_nat (kchunks 24)) with 1%nat. rewrite HFL. rewrite ECA. reflexivity. }
  assert (EMF1 : cs_mapped_free_array (drain_cs 24 cs) = if g then cs_mapped_free_array cs + 262144 else cs_mapped_free_array cs).
  { unfold drain_cs. cbn [cs_mapped_free_array]. fold cs. rewrite HGR. unfold kFreeArrayMapSize. destruct g; reflexivity. }
  assert (HX1 : 0 <= x1 < 2 ^ 28).
  { apply (K0_id24_bound Kc A1 rho tp tr md x1 HKc HCI HK). unfold A1. rewrite (drainA_cls A HLA). fold cs. rewrite EFA1. apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
  pose proof (cv_ri_au _ _ _ _ _ CV1) as K_au. pose proof (cv_ri_mu _ _ _ _ _ CV1) as K_mu. pose proof (cv_bounds _ _ _ _ _ CV1) as (_ & BAU & BMU & _).
  pose proof (cv_fa_cells _ _ _ _ _ CV1 (length (cs_free_array cs)) x1 ltac:(rewrite EFA1; rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity)) as K_dst.
  fold SB in K_dst, K_au, K_mu. fold nf in K_dst. rewrite FAv in K_dst. cbn [cs_allocated_user cs_mapped_user drain_cs] in BAU, BMU. unfold kUserSpaceSize, kRegionSize, kFreeArraySize, kUserMapSize in BMU.

  set (R := map carve_obj [riS g; dstS]). set (rho3 := rho_absorb rho R (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)) in *.
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) (K27 g) R vRI 0 128 _ Hsm (Lx_objs1 g) ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite ERI; lia) ltac:(rewrite ERI; lia)) as [AV1 PR1].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) (K27 g) R dstF 0 4 _ Hsm (Lx_objs1 g) ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite Edst; lia) ltac:(rewrite Edst; lia)) as [AV2 PR2].
  fold rho3 v3 in AV1, PR1, AV2, PR2. rewrite ERI in AV1, PR1. rewrite Edst in AV2, PR2.
  set (ri := SB + 2 ^ 37 + 3072) in *. set (da := SB + 24 * 2 ^ 32 + 3758096384 + 4 * nf) in *.
  assert (Enf1 : eval rho (SAlu ALU_ADD vNF (SLit 1)) = Z_to_bv 64 (nf + 1)) by (apply (ev_add_lit rho vNF nf 1); [unfold vNF; cbn [eval]; exact E221 | lia | lia | lia]).
  assert (Emf1 : eval rho (if g then SAlu ALU_ADD vMFA (SLit 262144) else vMFA) = Z_to_bv 64 (if g then cs_mapped_free_array cs + 262144 else cs_mapped_free_array cs)).
  { destruct g; [apply (ev_add_lit rho vMFA (cs_mapped_free_array cs) 262144); [unfold vMFA; cbn [eval]; exact E222 | clear -FC1 FC2 FC3 NF0; lia | lia | clear -FC1 FC2 FC3 NF0; lia] | unfold vMFA; cbn [eval]; exact E222]. }
  assert (Edv : eval rho (SExt true 32 (SVar 231)) = Z_to_bv 64 x1) by (cbn [eval]; rewrite E231; apply OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.jc.SpineMallocR3.sext32_small; lia).
  assert (C0 : cell_ok v3 (mkACell (ri + 0) 8 0)) by exact (av_cell v3 ri 0 8 _ _ rho (fun j => AV1 _ _ _ j (or_introl eq_refl)) eq_refl).
  assert (C16 : cell_ok v3 (mkACell (ri + 16) 8 (nf + 1))) by exact (av_cell v3 ri 16 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_introl eq_refl))) Enf1).
  assert (C24 : cell_ok v3 (mkACell (ri + 24) 8 (if g then cs_mapped_free_array cs + 262144 else cs_mapped_free_array cs))) by exact (av_cell v3 ri 24 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_introl eq_refl)))) Emf1).
  assert (C32 : cell_ok v3 (mkACell (ri + 32) 8 (cs_allocated_user cs))) by exact (av_cell v3 ri 32 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_introl eq_refl))))) E223).
  assert (C40 : cell_ok v3 (mkACell (ri + 40) 8 0)) by exact (av_cell v3 ri 40 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))) eq_refl).
  assert (C48 : cell_ok v3 (mkACell (ri + 48) 8 (cs_mapped_user cs))) by exact (av_cell v3 ri 48 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))) E224).
  assert (C56 : cell_ok v3 (mkACell (ri + 56) 8 0)) by exact (av_cell v3 ri 56 8 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))) eq_refl).
  assert (C68 : cell_ok v3 (mkACell (ri + 68) 1 0)) by exact (av_cell v3 ri 68 1 _ _ rho (fun j => AV1 _ _ _ j (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))) eq_refl).
  assert (Cd3 : cell_ok v3 (mkACell (da + 0) 4 x1)) by exact (av_cell v3 da 0 4 _ _ rho (fun j => AV2 _ _ _ j (or_introl eq_refl)) Edv).
  set (P := fun z : Z => (ri <= z < ri + 128) \/ (da <= z < da + 4)).
  assert (PD : forall z, P z \/ ~ P z) by (intros z; unfold P; lia).
  assert (INRG : forall x, in_ranges rho R x -> P (bv_unsigned x)).
  { intros x (o & Ho & Hz). unfold P. destruct Ho as [<-|[<-|[]]]; unfold carve_obj, riS, dstS, carved in Hz; rewrite obj_range_mk in Hz by lia; cbn [fst snd] in Hz; rewrite ?ERI, ?Edst in Hz; fold ri da in Hz; lia. }
  destruct (absorb_out rho R (vms md tp ms) P INRG) as [FR FRrm]. fold rho3 v3 v in FR, FRrm.
  assert (VD : forall z, da <= z < da + 4 -> v3 z = v z).
  { intros z Hz. replace da with (da + 0) in Hz by lia. unfold da in K_dst. fold da in K_dst. replace (da) with (da + 0) in K_dst by lia.
    apply (cell_ok_same v v3 _ K_dst Cd3). cbn [c_addr c_w]. lia. }
  assert (VO : forall z, ~ (ri <= z < ri + 128) -> v3 z = v z).
  { intros z Hz. destruct (Z_le_dec da z) as [L1|L1]; [destruct (Z_lt_dec z (da + 4)) as [L2|L2]; [exact (VD z (conj L1 L2))|]|]; apply FR; unfold P; lia. }
  assert (HK3 : K0 Kc A1 rho3 tp tr md).
  { apply (K0_ri_blind Kc A1 rho rho3 tp tr md 24 HKc ltac:(lia) HCI); try (intros; reflexivity); try exact HK.
    all: change (ag_spacebeg (aa_geom A1)) with SB; rewrite ?RIv; fold ri; fold v3 v.
    all: unfold A1; rewrite ?(drainA_cls A HLA); fold cs; rewrite ?EFA1, ?EMF1, ?length_app; cbn [length cs_allocated_user cs_mapped_user drain_cs]; rewrite ?Nat2Z.inj_add; fold nf; change (Z.of_nat 1) with 1.
    all: unfold RI_mutex, RI_num_freed, RI_mapped_free_array, RI_allocated_user, RI_allocated_meta, RI_mapped_user, RI_mapped_meta, RI_exhausted.
    - exact VO.
    - intros z Hz. exact (PR1 z ltac:(lia)).
    - intros a0 Ha0. apply FRrm. unfold P, ri, da. rewrite u64_lit by (unfold IMG_LO, IMG_HI in Ha0; lia). unfold IMG_LO, IMG_HI in Ha0. lia.
    - exact C0.
    - exact C16.
    - exact C24.
    - exact C32.
    - exact C40.
    - exact C48.
    - exact C56.
    - exact C68. }
  assert (PDZ : forall z, P z -> DZ A1 24 z).
  { intros z Hz. unfold DZ. cbv zeta. change (aa_geom A1) with (aa_geom A). fold SB. rewrite RIv, FAv. unfold kRegionInfoStride, kFreeArraySize. unfold P, ri, da in Hz.
    destruct Hz as [Hz|Hz]; [right; left; lia | right; right; left; clear -Hz FC2 FC3 NF0; destruct g; lia]. }
  destruct (CR_drain (K0 Kc) HL (K0_secband Kc) A1 a s [] tmp' rest 24 HTH HCI HGL ltac:(lia) rho tp tr md v v3 n0 nd HK) as (HCB3 & HRM3); [ | | exact HCB | exact HRM | ].
  { intros z Hz. apply FR. intros HP. exact (Hz (PDZ z HP)). }
  { intros z HB Hd. rewrite FR; [exact Hd|]. unfold P, ri, da. unfold bandz, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in HB. lia. }
  assert (HF3 : FRM A0 rho0 rho3).
  { apply (FRM_absorb_QFP A0 rho0 rho rho3 P PD ltac:(intros i; reflexivity) ltac:(intros l; reflexivity)); [| exact FR | exact FRrm | exact HFRM].
    intros z Hz. split; [exact (DZ_QFP A1 A0 z EG (PDZ z Hz))|]. unfold P, ri, da in Hz. unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END. lia. }
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ (Lx g) rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ rho (Lx g) (K27 g) R tp tr ms md (Lx_objs1 g) HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU.
  exists rho3. split; [|intros i; reflexivity].
  split; [exact (proj1 HU)|]. cbn [w_tr w_cfg cfg_model fst snd]. split; [exact HK3|]. split; [exact HCB3|]. split; [exact HRM3 | exact HF3].
Qed.
End ExitF.

Definition N_2a : list carve_spec := ltac2:(tb__ "0|a|
S13S12S12S12S0S21A2M0S21A2M1S17S12S12S21S14A2M2S0A2M3A1M4A2M5S11G1G4S11G0S21S11S0S21S61Z0M6A4Z4A4S13G3S11G2S0S11S21S14G6U4M7A4S1Z2A1A4S16G3A1M8A3A4S13G5S11G1G4S11G0S21S11S0S21S61Z14M9A4Z18A4S13G3S11G2S0S11S21S14G9G7A4S89A4G8A3A4S13G5S11G1G4S11G0S21S11S0S21S76Zad0A4Zc60A4S13G3S11G2S0S11S21S14Zae0U8A4S87S7Pd1A1S6S60S1G6A1S7Pc9A1A3A2A4G8A3A4S16G5A1A3A3A3").
Definition K24 (g : bool) : list sobj := ltac2:(tb__ "0|0|
S3eS2U18S3S29S44Vg;A1A1A1A3").
Lemma Ly_objs2 : ltac2:(tb__ "0|0|
S15S24S17S2A1S3S29S44R1A1A1A1S18S2S4aR1A1S3dS27S2S28S50A4A3A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Definition Lz (g : bool) : axst := ltac2:(tb__ "0|1|
S2bS44Vg;A1M0S70S29G0A1S4aVg;A1A2A2").

Section ExitG.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).

Lemma qcf_x2a : ltac2:(tb__ "0|7|
S15S2eS21S21S21S14S17S2cA1M0G0S4S17S5cQ40M1A1M2A1S66S24G0S32RaA1S16S2cA1M3A3S24S15S2fRbA1S19A3S69VA0;RcA2S24G0S31RdA1S13S2cS30RcS16S12S21S21A2A1M4RbA3S18S2cR8R7A3A3A3S24S21S82S1eS21S34S6bReZ18M5A2A1A2A1Z2A3S41S42S68S65VKc;A1M6VA0;Vrho0;S63RfG5A2ReRcRbG4RaR9AaS44R10A1R8R7R6A6S24G2S5R9Pa6A2S5bG1RfA2A3S26S4S4S25S41S42S67G6VA0;Vrho0;S6dS6eS63R12G5A2G3S18S2cRdRcA3A3G5S99S2dR12A1S30R11G4R10A3A2A3RdRcA6S45R13A1R1RaR9A6S25S22S24G2S5R2R1A2S5RcR1A2A3Fi;S24G2S9R1S6aA2S5bG1G5A2A3A2A2Lrho3;A2F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest;Ftmp';Fnd;Fn0;Fs;Fa;FA;Fg;").
Proof.
  intros g A a s n0 nd tmp' rest rho tp [tr [ms md]] HTH HCI HQP0 HGL HFULL H E166.
  destruct (proj2 H) as (HK & HCB & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HCB, HRM, HFRM.
  pose proof (proj1 (proj1 H)) as Hsm. unfold virt in Hsm. cbn [fst snd w_tr w_cfg cfg_ms cfg_model] in Hsm.
  set (A1 := drainA A 24) in *. pose proof (K0_laws Kc HKc) as HL.
  assert (HTH1 : aa_q_thread A1 = []) by exact HTH. assert (HGL1 : aa_q_global A1 = mkQB a [] s :: tmp' ++ rest) by exact HGL. assert (HCI1 : aa_cache_inited A1 = true) by exact HCI.
  destruct (kq_facts segsA (K0 Kc) HL A1 rho tp _ _ HK) as [HG HRIG HRTC HMIN HST HLEN HCLS HQPU HIDS HSEP HSEP3 HKTOP HKSECQ].
  change (aa_geom A1) with (aa_geom A) in HG, HRIG, HST, HSEP.
  destruct HRIG as (E151 & E152 & E155 & E156).
  assert (HLA : (24 < length (aa_cls A))%nat) by (unfold A1, drainA in HLEN; cbn [aa_cls] in HLEN; rewrite length_list_upd in HLEN; lia).
  assert (HK1 : Z.of_nat (length (cs_cache (SegQ_wf2.cls_of A1 24))) = 1).
  { unfold A1. rewrite (drainA_cls A HLA). unfold drain_cs, drain_keep. cbn [cs_cache]. change (Z.to_nat (kchunks 24)) with 1%nat. rewrite length_firstn. lia. }
  set (T := ag_thread (aa_geom A)) in *.
  pose proof (geom_old _ HG) as HG'. destruct HG' as (_ & _ & _ & _ & G5 & G6 & G7 & _). fold T in G5, G6, G7.
  pose proof (geom_bands _ HG) as (_ & TBD & _ & _ & TI & _). unfold IMG_LO, IMG_HI in TI. fold T in TI, TBD. pose proof (topG_range (aa_geom A)) as TG.
  pose proof (benv_of_K (K0 Kc) HL A1 HCI1 rho tp tr md HK) as BE. destruct BE as [_ _ HQP HAU _ _ _].
  destruct (batch_slot A1 HQP HAU HG (mkQB a [] s) ltac:(rewrite (qall_A1 A1 HTH1), HGL1; left; reflexivity)) as (y & Ey & Y0 & _ & Y1 & _). cbn [qb_addr] in Ey. rewrite kUserSpaceSize_val in Y1.
  change (aa_geom A1) with (aa_geom A) in Ey.
  pose proof (SB_facts A HG) as (_ & SBF1 & SBF2). unfold HIGH_SHADOW_END in SBF1. rewrite kSpaceSize_val in SBF2.
  assert (EC : eval rho clsB = Z_to_bv 64 24) by (apply (clsB_val rho (ag_spacebeg (aa_geom A)) a y); try lia; assumption).
  assert (ECP : eval rho cptrC = Z_to_bv 64 y) by (apply (cptrC_val rho (ag_spacebeg (aa_geom A)) a y); try lia; assumption).
  rewrite (qb_id_val (aa_geom A) a [] s y Ey).
  assert (EcbC : eval rho cbC = Z_to_bv 64 (T + 208)) by (unfold cbC; apply ev_add_lit; [unfold vT; cbn [eval]; exact E151 | lia | lia | lia]).
  assert (Epcb : bv_unsigned (eval rho pcbF) = T + 2128).
  { unfold pcbF, add. rewrite U_add, U_mul. fold (add vT (SLit 208)). fold cbC. rewrite EcbC, EC. change (eval rho (SLit 80)) with (Z_to_bv 64 80). rewrite !u64_lit by lia. unfold M64v.
    rewrite (Z.mod_small (24 * 80)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (EvT : bv_unsigned (eval rho vT) = T) by (unfold vT; cbn [eval]; rewrite E151, u64_lit by lia; reflexivity).
  set (R := map carve_obj N_2a).
  set (rho3 := rho_absorb rho R (vms md tp ms)). set (v3 := view segsA (rm rho3)). set (v := view segsA (rm rho)) in *.
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) (K24 g) R pcbF 0 4 _ Hsm (Ly_objs2 g) ltac:(left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite Epcb; lia) ltac:(rewrite Epcb; lia)) as [AV1 PR1].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) (K24 g) R pcbF 20 24 _ Hsm (Ly_objs2 g) ltac:(right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite Epcb; lia) ltac:(rewrite Epcb; lia)) as [AV2 PR2].
  destruct (absorb_view_cells segsA rho _ tr (vms md tp ms) (vmd md) (K24 g) R vT 2768 3168 _ Hsm (Ly_objs2 g) ltac:(right; right; left; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia) ltac:(rewrite EvT; lia) ltac:(rewrite EvT; lia)) as [_ PR3].
  fold rho3 v3 in AV1, PR1, AV2, PR2, PR3. rewrite Epcb in AV1, PR1, AV2, PR2. rewrite EvT in PR3.
  assert (C_cnt3 : cell_ok v3 (mkACell (T + 2128 + 0) 4 2)) by exact (av_cell v3 (T + 2128) 0 4 _ _ rho (fun j => AV1 _ _ _ j (or_introl eq_refl)) eq_refl).
  assert (C_slot3 : cell_ok v3 (mkACell (T + 2128 + 20) 4 y)) by exact (av_cell v3 (T + 2128) 20 4 _ _ rho (fun j => AV2 _ _ _ j (or_introl eq_refl)) ECP).
  clear AV1 AV2.
  set (P := fun z : Z => (T + 2128 <= z < T + 2132) \/ (T + 2148 <= z < T + 2152) \/ (T + 2768 <= z < T + 3168)).
  assert (PD : forall z, P z \/ ~ P z) by (intros z; unfold P; lia).
  assert (PT : forall z, P z -> T + 2128 <= z < T + 3168) by (intros z Hz; unfold P in Hz; lia).
  assert (INRG : forall x, in_ranges rho R x -> P (bv_unsigned x)).
  { intros x (o & Ho & Hz). unfold P. destruct Ho as [<-|[<-|[<-|[]]]]; unfold carve_obj, carved in Hz; rewrite obj_range_mk in Hz by lia; cbn [fst snd] in Hz;
      rewrite ?Epcb, ?EvT in Hz; lia. }
  destruct (absorb_out rho R (vms md tp ms) P INRG) as [FR FRrm]. fold rho3 v3 v in FR, FRrm.
  assert (PPR : forall z, P z -> v3 z <> None).
  { intros z Hz. destruct Hz as [Hz|[Hz|Hz]]; [destruct (PR1 z ltac:(lia)) as [x Hx] | destruct (PR2 z ltac:(lia)) as [x Hx] | destruct (PR3 z ltac:(lia)) as [x Hx]]; rewrite Hx; discriminate. }

  assert (HK3 : K0 Kc (push_cache (set_q A1 [] (tmp' ++ rest)) 24 y) rho3 tp tr md).
  { rewrite <- (qb_id_val (aa_geom A) a [] s y Ey). change (aa_geom A) with (aa_geom A1).
    apply (kq_push_batch segsA (K0 Kc) HL A1 rho rho3 tp tr md [] (tmp' ++ rest) (mkQB a [] s) HTH1 HGL1 eq_refl HCI1 ltac:(rewrite HK1; reflexivity)); [intros i; reflexivity | intros l; reflexivity | | | | | exact HK].
    - intros z NQ NPZ. fold v3 v. destruct (PD z) as [Hp|Np]; [|exact (FR z Np)]. exfalso. unfold push_zone, pc_entry in NPZ. change (aa_geom A1) with (aa_geom A) in NPZ. fold T in NPZ. rewrite HK1 in NPZ.
      destruct Hp as [Hp|[Hp|Hp]]; [apply NPZ; left; lia | apply NPZ; right; lia | apply NQ; right; right; unfold qstat_zone; change (aa_geom A1) with (aa_geom A); fold T; lia].
    - intros z _ Hd. fold v3. fold v in Hd. destruct (PD z) as [Hp|Np]; [exact (PPR z Hp) | rewrite (FR z Np); exact Hd].
    - fold v3. unfold pc_entry. change (aa_geom A1) with (aa_geom A). fold T. rewrite HK1. replace (T + 0xd0 + 80 * 24) with (T + 2128 + 0) by lia. exact C_cnt3.
    - fold v3. unfold pc_entry. change (aa_geom A1) with (aa_geom A). fold T. rewrite HK1. change (aa_geom A1) with (aa_geom A). rewrite (qb_id_val (aa_geom A) a [] s y Ey).
      replace (T + 0xd0 + 80 * 24 + 16 + 4 * 1) with (T + 2128 + 20) by lia. exact C_slot3. }

  assert (QF_OUT : forall z, q_foot A1 z -> ~ P z) by (intros z QF HP; pose proof (HSEP z QF) as NT; fold T in NT; pose proof (PT z HP); lia).
  assert (HR3 : RMEM2 v3 (aa_geom A1) tmp' rest).
  { destruct HRM as (HBM & HLT & HLR & HTHD & HGH). change Inv.QG with QG in *. change (aa_geom A1) with (aa_geom A) in *.
    assert (INQ : forall b, In b (tmp' ++ rest) -> In b (qall A1)) by (intros b Hb; rewrite (qall_A1 A1 HTH1), HGL1; right; exact Hb).
    split; [|split; [|split; [|split]]].
    - apply Forall_forall. intros b Hb.
      apply (batch_mem_frame A1 v v3 b (proj1 (Forall_forall _ _) (proj1 HQP) b (INQ b Hb))); [|exact (proj1 (Forall_forall _ _) HBM b Hb)].
      intros z Hz. apply FR. apply QF_OUT. unfold q_foot. fold (qall A1). apply Exists_exists. exists b. split; [exact (INQ b Hb)|]. unfold bfoot in Hz.
      destruct Hz as [Hz|Hz]; [left; unfold kQuarantineBatchSize in *; lia | right]. apply Exists_exists in Hz as (it & Hit & Hz). apply Exists_exists. exists it.
      split; [exact Hit|]. unfold ifoot, it_ab in Hz. exact Hz.
    - apply qlinks_to_0. apply (qlinks_to_frame v v3 tmp' 0); [|apply qlinks_to_0; exact HLT].
      intros b z Hb Hz. apply FR. apply QF_OUT. unfold q_foot. fold (qall A1). apply Exists_exists. exists b. split; [apply INQ; apply in_or_app; left; exact Hb|]. left. unfold kQuarantineBatchSize. lia.
    - apply qlinks_to_0. apply (qlinks_to_frame v v3 rest 0); [|apply qlinks_to_0; exact HLR].
      intros b z Hb Hz. apply FR. apply QF_OUT. unfold q_foot. fold (qall A1). apply Exists_exists. exists b. split; [apply INQ; apply in_or_app; right; exact Hb|]. left. unfold kQuarantineBatchSize. lia.
    - destruct HTHD as (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr. fold T in Q1, Q2, Q3, Q4 |- *.
      assert (TOUT : forall z, T + 0x50 <= z < T + 0x70 -> v3 z = v z) by (intros z Hz; apply FR; intros HP; pose proof (PT z HP); lia).
      split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply TOUT; lia|]. split; [intros X; exfalso; exact (X eq_refl)|].
      split; [eapply present_frame; [|exact Q3]; intros z Hz; apply TOUT; lia | eapply cell_ok_frame1; [|exact Q4]; cbn; intros z Hz; apply TOUT; lia].
    - destruct HGH as (Q1 & Q2 & Q3 & Q4). unfold qhdr_repr.
      assert (GOUT : forall z, QG + 160 <= z < QG + 192 -> v3 z = v z) by (intros z Hz; apply FR; intros HP; pose proof (PT z HP); unfold QG in *; lia).
      split; [eapply cell_ok_frame1; [|exact Q1]; cbn; intros z Hz; apply GOUT; lia|].
      split; [intros NE; destruct (Q2 NE) as [Qa Qb]; split; (eapply cell_ok_frame1; [|eassumption]); cbn; intros z Hz; apply GOUT; lia|].
      split; [eapply present_frame; [|exact Q3]; intros z Hz; apply GOUT; lia | eapply cell_ok_frame1; [|exact Q4]; cbn; intros z Hz; apply GOUT; lia]. }
  assert (HF3 : FRM A0 rho0 rho3).
  { apply (FRM_absorb_QFP A0 rho0 rho rho3 P PD ltac:(intros i; reflexivity) ltac:(intros l; reflexivity)); [| exact FR | exact FRrm | exact HFRM].
    intros z Hz. pose proof (PT z Hz) as PTz. split; [|unfold SHADOW_BAND_LO, SHADOW_BAND_HI in *; lia].
    destruct HQP0 as (ESB & _). assert (EG : aa_geom A = aa_geom A0) by (unfold same_but_qcs in ESB; rewrite ESB; reflexivity).
    destruct (Z_lt_dec z (T + 2768)) as [|]; [right; left; rewrite <- EG; fold T; lia | left; right; right; unfold qstat_zone; rewrite <- EG; fold T; lia]. }
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ (Ly g) rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  pose proof (SPA_unobj segsA TJ rho (Ly g) (K24 g) R tp tr ms md (Ly_objs2 g) HT (fun x => x)) as HU. cbn zeta in HU. fold rho3 in HU.
  exists rho3. split; [|split; [intros i; reflexivity | unfold rho3; rewrite eval_absorb; exact EC]].
  split; [exact (proj1 HU)|]. cbn [w_tr w_cfg cfg_model fst snd]. split; [exact HK3|]. split; [exact HR3 | exact HF3].
Qed.
End ExitG.

Definition T_x (g : bool) : strans := ltac2:(tb__ "0|2|
S92S45Vg;A1U10S13S27S98S16S27A1A3S16S22A1S16S8A1S79S88S91S13S12S12S14S21A2M0S21A2M1S11G0S21S11S14S21U0Zeaa78A4Zeaa80A4S16G1A1A3A9").
Lemma T_x_ok : ltac2:(tb__ "0|0|
S15S24S15S97S47R1A1A1S19A3Fg;"). Proof. intros [|]; vm_cast_no_check (eq_refl true). Qed.
Definition DSX (ctx pcb : Z) : list dspec := ltac2:(tb__ "0|4|
S3dS27S12S27S21A2S27S11S27S21R1S0S21Lx;S1cS0S21S1cS12S0S21A2M0S21S1cS12G0S21A2S17S12S12S21S14A2S0A2A1R1A3A3A3S21Z0Lz;S22Vctx;Li;S5eS0S0Vpcb;Lb;La;M1Lop;M2G2S5fG1Lop;M3G3S15S23S0Vpcb;La;Lw;Lsgn;S22S0S21Vpcb;Lk0;Li;Ll;X0x8A4Lk;S4cA4").
Lemma Lz_objs : ltac2:(tb__ "0|2|
S15S21S21S24S17S2A1S3S29S94S47R3A1M0A1M1A1A1S18S2S7dG1S96G0A1A2S3dS7aS2S7cS49R2R1A2A4A3A3Fpcb;Fctx;Fg;").
Proof. intros g ctx pcb. change (map dobj (DSX ctx pcb)) with (map carve_obj N_D2b). revert g. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Lz_ref : ltac2:(tb__ "0|0|
S15S24S15S7bS2S2S7eS3S29S95S47R1A1A1A1A1S3S29S8aA1A1A5S19A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma Lz_pre : ltac2:(tb__ "0|0|
S15S24S15S9bS8S8S9aS8SfR1A1S10S29S45R2A1A1A1A3Lf;S86S8cA1A3S19A3Fg;"). Proof. intros [|]; OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Ltac rtc_cellx HR := first [ exact (cells_ok_nth _ _ 0%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 1%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 2%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 3%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 4%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 5%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 6%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 7%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 8%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 9%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 10%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 11%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 12%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 13%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 14%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 15%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 16%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 17%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 18%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 19%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 20%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 21%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 22%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 23%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 24%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 25%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 26%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 27%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 28%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 29%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 30%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 31%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 32%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 33%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 34%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 35%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 36%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 37%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 38%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 39%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 40%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 41%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 42%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 43%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 44%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 45%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 46%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 47%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 48%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 49%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 50%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 51%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 52%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 53%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 54%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 55%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 56%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 57%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 58%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 59%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 60%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 61%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 62%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 63%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 64%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 65%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 66%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 67%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 68%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 69%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 70%nat _ HR eq_refl) | exact (cells_ok_nth _ _ 71%nat _ HR eq_refl) ].

Section ExitH.
Variable Kc : KcA.
Hypothesis HKc : Kc_ok Kc.
Variables (A0 : AA) (rho0 : valuation).

Lemma ro_allX : ltac2:(tb__ "0|4|
S2eS4S17S5cQ40M0A1M1A1S17S85A1S84S65VKc;R5R4R3R2R1A6S24S15S2fR6A1S19A3S24S33S2dR7A1S2dVA0;A1A3S24G1S9R7S6aA2S5bG0Z18M2A2A3S24G1S5R8Pc9A2S5bG0S77G2A1A2A3S40S7aS93VA0;R9A2S49S35S2dRaA1M3A1S83S36G3A1Z850A2A2A3F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Fr;FA';").
Proof.
  intros A' r tp tr md HK HCI EG EC E201. pose proof (K0_laws Kc HKc) as HL.
  destruct (kq_facts segsA (K0 Kc) HL A' r tp _ _ HK) as [HG HRIG HRTC _ _ _ HCLS _ _ _ _ _ _].
  destruct HRIG as (E151 & E152 & E155 & E156).
  assert (HR : cells_ok (view segsA (rm r)) (rtc_cells RTC_A (aa_geom A'))) by exact HRTC.
  pose proof (HCLS HCI 24 ltac:(lia)) as CV. pose proof (cv_max _ _ _ _ _ CV) as C_max. pose proof (cv_size _ _ _ _ _ CV) as C_sz. unfold pc_entry in C_max, C_sz.
  change (max_count 24) with 2 in C_max. change (Size 24) with 8192 in *.
  pose proof (geom_nums _ HG) as (_ & _ & _ & T0 & T1 & _ & C0 & C1' & _ & _ & _ & _ & _ & TG).
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & _ & CI & _). unfold IMG_LO, IMG_HI in CI.
  assert (CB : ag_ctx (aa_geom A') + 0x1000 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= ag_ctx (aa_geom A')) by (destruct HG as (_ & _ & _ & (_ & _ & _ & _ & X0) & _); exact X0).
  assert (TB : ag_thread (aa_geom A') + 0x1000 <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= ag_thread (aa_geom A')) by (destruct HG as (_ & _ & (_ & _ & _ & _ & _ & X0) & _); exact X0).
  unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in CB, TB.
  set (T := ag_thread (aa_geom A')) in *. set (CTX := ag_ctx (aa_geom A')) in *.
  assert (EcbC : eval r cbC = Z_to_bv 64 (T + 208)) by (unfold cbC; apply ev_add_lit; [unfold vT; cbn [eval]; exact E151 | lia | lia | lia]).
  assert (Epcb : eval r pcbF = Z_to_bv 64 (T + 2128)).
  { apply bv_eq. unfold pcbF, add. rewrite U_add, U_mul. fold (add vT (SLit 208)). fold cbC. rewrite EcbC, EC. change (eval r (SLit 80)) with (Z_to_bv 64 80). rewrite !u64_lit by lia. unfold M64v.
    rewrite (Z.mod_small (24 * 80)) by lia. rewrite Z.mod_small by lia. lia. }
  unfold DSX, N_D2b, N_rti, szS, vCTX. cbn [map app fst].
  repeat apply Forall_cons; try apply Forall_nil; apply (ro_cond_intro A0 (mkSC 0 0 0));
    try (unfold PG; lia); try reflexivity;
    try (cbn [eval]; exact E152); try exact Epcb;
    try (unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia).
  all: try (intros z Hz; cbv [pcbF add] in Hz; split; [|unfold SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *; lia];
            first [ right; left; unfold qrtc_zone; rewrite <- EG; fold CTX; unfold Inv.QG; lia
                  | right; right; unfold qrtc2_zone; lia
                  | left; right; left; rewrite <- EG; fold T; lia ]).
  all: repeat apply Forall_cons; try apply Forall_nil.
  all: cbv beta iota; eexists; (split; [first [reflexivity | exact E155 | exact E156 | exact E152 | exact E151 | exact E201]|]);
       cbv [pcbF add]; first [ rtc_cellx HR | (replace (T + 2128 + 4) with (T + 208 + 80 * 24 + 4) by lia; exact C_max) | (replace (T + 2128 + 8) with (T + 208 + 80 * 24 + 8) by lia; exact C_sz) ].
Qed.

Lemma qcf_x2b : ltac2:(tb__ "0|5|
S15S2eS17S2cA1M0G0S4S17S5cQ40M1A1M2A1S66S21S6cR7R1A2S6cVA0;R2A2F_;Fz;S24S15S2fR7A1S19A3S24S33S2dR8A1S2dVA0;A1A3S41S42S67S65VKc;A1M3VA0;Vrho0;R9R8R7A6S45RaA1R6R5R4A6S24G2S9R7S6aA2S5bG1Z18M4A2A3S24G2S5R8Pc9A2S5bG1S77G4A1A2A3S7fR9RbA2S26S4S4S25S41S42S67G3VA0;Vrho0;ReRdRcA6S79R1RaR9A6S7fR1RdA2A2Lrho5;A2F_;F_;F_;F_;F_;F_;F_;Fw;Ftp;Frho;Frest;Ftmp';FA';Fg;").
Proof.
  intros g A' tmp' rest rho tp [tr [ms md]] HQW HCI EG H EC E201 HVx.
  destruct (proj2 H) as (HK & HRM & HFRM). cbn [w_tr w_cfg cfg_model fst snd] in HK, HRM, HFRM.
  pose proof (K0_laws Kc HKc) as HL.
  pose proof (smatch_facts_hold _ _ _ _ (proj1 (proj1 H))) as HFa.
  assert (HFp : Forall (holds rho) (pre_facts DEPTH_R)).
  { apply Forall_forall. intros f Hf. pose proof (proj1 (forallb_forall _ _) (Lz_pre g) f Hf) as X0. apply existsb_exists in X0 as (f' & Hf' & E). apply sprop_eqb_sound in E. subst f'.
    exact (proj1 (Forall_forall _ _) HFa f Hf'). }
  pose proof HK as (_ & _ & _ & HTOP & _).
  set (TJ := (fun (_ : valuation) (_ : list word) (_ : list event) (_ : Model) => True) : jpredA).
  assert (HT : SPA segsA TJ (s_C (T_x g)) rho tp (tr, mkCfg ms md)) by (split; [exact (proj1 H) | exact I]).
  destruct (s_step (K0 Kc) HL A0 rho0 (zbF A') zloS zhiF ZUF (zsepF Kc A' rho tp tr md HKc HK) (T_x g) (JRD (K0 Kc) A0 rho0 A' tmp' rest)
              (DSX (ag_ctx (aa_geom A')) (ag_thread (aa_geom A') + 2128)) [] A' rho tp tr ms md (T_x_ok g)
              (JRD_stable (K0 Kc) HL A0 rho0 A' tmp' rest) HQW (Lz_objs g _ _) eq_refl HT HK HFRM (ro_allX A' rho tp tr md HK HCI EG EC E201))
    as (rho5 & H5 & V5 & RM5 & AG5 & EV).
  { intros HK3 HF3 EV3. set (rho3 := rho_absorb rho (map dobj (DSX (ag_ctx (aa_geom A')) (ag_thread (aa_geom A') + 2128))) (vms md tp ms)) in *. cbn [T_x s_bs combine rho_sets].
    split; [split; [exact HK3 | split; [rewrite EV3; exact HRM | exact HF3]]|].
    destruct (kq_facts segsA (K0 Kc) HL A' rho3 tp _ _ HK3) as [_ HRIG3 HRTC3 _ _ _ _ _ _ _ _ _ _].
    split; [|split; [|split; [|intros _; apply Forall_nil]]].
    - unfold T_x. cbn [s_N]. apply Forall_cons; [|apply Forall_nil].
      unfold sbS, carve_okq. cbn [eval]. rewrite u64_lit by lia.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [unfold cells_inside; repeat apply Forall_cons; try apply Forall_nil; cbn; lia|].
      split; [intros off Hoff; split; [apply wok_of_imageA; lia | apply rd_of_imageA; lia]|].
      unfold cells_in_view. repeat apply Forall_cons; try apply Forall_nil.
      assert (HSB : cell_ok (view segsA (rm rho3)) (mkACell 0xeaa78 8 (ag_spacebeg (aa_geom A')))) by (unfold rtc_inv, rtc_cells in HRTC3; exact (cells_ok_nth _ _ 3 _ HRTC3 eq_refl)).
      eapply (civ_cell rho3 (rm rho3) 0 0xeaa78); [exact HSB | unfold vSB; cbn [eval]; exact (proj1 (proj2 (proj2 HRIG3))) | lia | lia].
    - unfold T_x. cbn [s_N s_ZDn map]. constructor; [|constructor].
      unfold in_zone, sbS, carve_obj, carved. rewrite obj_range_mk by lia. cbn [eval fst snd]. rewrite u64_lit by lia.
      split; [unfold ZUF; cbn; tauto|]. unfold zloS, zhiF, zbF. split; [lia|]. split; [lia|]. right. lia.
    - unfold T_x at 2. cbn [s_ZDo].
      apply (in_zone_same rho3 _ _ _ _ _ (ss_objs (ax_S DQI0)) ZD_fixS (Lz_ref g)).
      apply (in_zone_ext_list rho3 (zbS (ag_thread (aa_geom A')) (ag_ctx (aa_geom A')) (topG (aa_geom A')) 0) zloS (zhiS 0) ZUS).
      + apply (inz_fixS A' (0, 0) 0%nat (mkSC 0 0 0) rho3); [unfold top_high in *; exact HTOP|].
        apply Forall_forall. intros f0 Hf0. apply (holds_agree_vals NPRE rho rho3 f0); [split; [intros v0 _; reflexivity | intros l0; reflexivity] | exact (proj1 (forallb_forall _ _) pre_facts_below f0 Hf0) | exact (proj1 (Forall_forall _ _) HFp f0 Hf0)].
      + unfold ZD_fixS. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; (split; [unfold ZUF; cbn; tauto | split; [reflexivity | split; reflexivity]]). }
  cbn [T_x s_bs combine rho_sets] in V5, AG5.
  assert (VV : forall v0, In v0 [166; 184; 185; 186; 187; 208]%positive -> rw rho5 v0 = rw rho v0).
  { intros v0 Hv. rewrite (V5 v0 (SVar v0)); [reflexivity|]. unfold T_x. cbn [s_M]. unfold MC, idm. apply in_map_iff. exists v0. split; [reflexivity | exact Hv]. }
  exists rho5. split; [exact H5|]. destruct HVx as (E184 & E185 & E186 & E187 & E208). unfold HVX. rewrite !VV by (cbn; tauto). tauto.
Qed.
End ExitH.
End SegQCF_exit.

