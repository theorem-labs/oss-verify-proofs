(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the segment of sup_instance_verb's ASan walk (plugin-hostd/fuzz_command) from the
   return of the strcspn wrapper (0x8b498) through rec_shape_of's call to its return, after
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (a segment that ends in a call, cl_callS, and passes on to the next). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaArt PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  rec_calls_free_c arg_line_c arg_i_c rec_shape_of_c answer_c sup_instance_verb_c hand_back_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
  RecBTemplateSiv sup_instance_verb_s2 sup_instance_verb_s3 sup_instance_verb_s4 sup_instance_verb_s5 sup_instance_verb_s6.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require strspn_c strcspn_c.
(* the plain proof's lemmas on the line's first word (lib/Prog/sup_instance_verb.v:210-276); its module shares the
   base name of the walk, so it is named by its full path *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require sup_instance_verb.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module PSIV := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.sup_instance_verb.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma siv_seg_A4 : siv_hyps B MT ->
forall ly S W (regs : bvmap 5 word) mem md ch pl ledger line R O lyc Sc (Wc : world SEGS) memc mdc regs1 kk Q1,
siv_cx B MT ly S W regs mem md ch pl ledger line R O -> frm0 fx ->
siv_mid B MT ly S W regs mem md line ledger R O lyc Sc Wc memc mdc regs1 kk Q1 [canon line; dec ledger]
  (rec_spill_frees R + EV_ARG_LINE + EV_ARG_I) (rec_spill_frees R * mo_free MT + XM_ARG_LINE MT line + XM_ARG_I MT ledger)
  (LIVE_ARG_LINE line + LIVE_ARG_I ledger) ->
getr regs1 9 = w64 (pl + Z.of_nat (siv_spn line)) ->
getr regs1 10 = w64 (Z.of_nat (siv_cspn line)) ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + SIV_CSPN_RET)) memc (seg_rom SEGS)) mdc)
  (siv_post B MT ly S W regs mem md line ledger R O).
Proof.
intros HY ly S W regs mem md ch pl ledger line R O lyc Sc Wc memc mdc regs1 kk Q1 CX HFRM MID R9 R10.
pose proof HY as HY0.
destruct HY as [TRCF TARG_LINE TARG_I TRSO TANSWER ASTRSPN ASTRCSPN VOBJS TL HB MTL PIMG PWR SIGP ROK RRO RELRO HTV
  RECC ROMV ZSH HULLL ROPA].
pose proof CX as (HPRE & HROD & HRO & H10 & Hpl64 & H11 & Hled & HLB & HLSTR0 & HLL & HLAP & HREP & HFR8 & HEV
  & HLIVE & HMOK).
destruct MID as (HJ & Hkk & HF & HR & HAREP & I1 & I2 & I3 & HMLE & HLV).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HR as (Rsp & Rgp & Rtp & R8 & Rhi).
assert (WS : SUP_INSTANCE_VERB_STK = 16592) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hsp46 : 2 ^ 46 <= sp0 - 48 <= 2 ^ 47).
{ change (2 ^ 46) with 70368744177664. change (2 ^ 47) with 140737488355328. clear - Hceil Hslo Hshi H47 Hstk0 C1 WS. lia. }
assert (HrepE : rec_repA B ly S (rdW W mem) R O) by exact HREP.
destruct HREP as (Q & HAQ & HOQ).
pose proof HAQ as (_ & _ & _ & (Hlen16 & _) & _).
set (n := Z.of_nat (length (r_calls R))) in *.
set (c := siv_slot R) in *.
assert (Hn : 0 <= n <= 16) by (unfold n; lia).
assert (Hc : rbs_slot_ok c) by (unfold c; apply siv_slot_ok; exact Hlen16).
destruct (siv_seed_mid B HB VOBJS SIV_CSPN_RET sr_atoms lyc Sc Wc memc mdc regs regs1 sp0 n c (proj1 HJ)
  Hsp46 Hal16 Hn Hc Rsp HF ltac:(unfold siv_E; apply regs_ok_Eimg_Ereg)) as [HS SHOK].
pose proof (siv_env regs regs1 n c) as HE. pose proof HE as (HEI & _).
set (E := siv_E regs regs1 n c) in *.
assert (HAE : env_agree 32 (Ereg regs1 (rbs_extra regs n c)) E).
{ split; [intros k Hk; unfold E, siv_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
paj_run_tok RUN HS HJ SHOK siv_Bspan.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
pmkst HS.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ (ms_mem ?m2)) |- _ =>
  pose proof (siv_aview_eq (w_H Wc) memc (ms_mem m2) (siv_nowin E _ _ HFr)) as RDQ end.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
pose proof (aregs_preserved_of_st_ok SEGS (w_H Wc) E _ _ regs1 (rbs_extra regs n c) HS HAE ltac:(vm_compute; reflexivity)) as HPT.
cbn [ms_regs restrict] in HPT.
assert (E2v : bv_unsigned (ew E 2) = sp0 - 48) by (pose proof HE as (_ & E2 & _); rewrite E2, Rsp; apply unsigned_lit_small; lia).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by (intros k r Hk; apply siv_E_reg; exact Hk).
assert (TP : forall r, acallee_saved r -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) by exact HPT.
assert (T2 : getr (ms_regs ms) 2 = getr regs1 2) by exact (TP 2 ltac:(unfold acallee_saved; lia)).
assert (Tsp : spZ (ms_regs ms) = sp0 + -48) by (unfold spZ; rewrite T2; fold (spZ regs1); lia).
assert (T3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by exact (eq_trans (TP 3 ltac:(unfold acallee_saved; lia)) Rgp).
assert (T4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by exact (eq_trans (TP 4 ltac:(unfold acallee_saved; lia)) Rtp).
assert (T8 : getr (ms_regs ms) 8 = w64 c) by exact (eq_trans (TP 8 ltac:(unfold acallee_saved; lia)) R8).
assert (T10 : getr (ms_regs ms) 10 = w64 (pl + Z.of_nat (siv_spn line))) by (rewrite P10, (EE 9%nat 9%bv eq_refl); exact R9).
assert (T11 : getr (ms_regs ms) 11 = w64 (Z.of_nat (siv_cspn line))) by (rewrite P11, (EE 10%nat 10%bv eq_refl); exact R10).
assert (Hcb : A_G_REC + OFF_CALLS <= c <= A_REC_SPILL) by (destruct (rbs_slot_bounds c Hc) as [H _]; exact H).
assert (Hin_rso : In CS_rec_shape_of cmd_prog_syms) by (unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right])).
rewrite (siv_sig CS_rec_shape_of SIGP Hin_rso).
replace (cmd_af CS_rec_shape_of) with AF_rec_shape_of by (vm_compute; reflexivity).
pose proof (proj1 HJ) as HARc.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & Hnev & _).
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms)))
  by exact (siv_aro_kept B RRO RELRO ROPA ly S W mem md _ R O lyc Sc Wc (ms_mem ms) _ _ _ _ _ HAR HrepE HJ HROD).
assert (HROc : cmd_ro_ok (rdW Wc (ms_mem ms))) by exact (ROK lyc Sc Wc (ms_mem ms) _ HARc HRODc).
(* the line at the call *)
destruct (siv_line_kept B HB PIMG HTV ly S W mem md R O pl line lyc Sc Wc (ms_mem ms) _ _ _ kk
  HAR HrepE HLB HLAP HLSTR0 HJ I2) as (HLSTR & HLHOME & _).
set (spn := siv_spn line) in *. set (cspn := siv_cspn line) in *.
set (v := firstn cspn (skipn spn line)).
pose proof (siv_spn_le line) as Hspn. pose proof (siv_cspn_le line) as Hcspn. fold spn cspn in Hspn, Hcspn.
rewrite length_skipn in Hcspn.
assert (Hlv : length v = cspn) by (unfold v; rewrite length_firstn, length_skipn; lia).
assert (Hvfw : v = first_word line) by exact (siv_verb_first_word line).
assert (HPLB : pl + Z.of_nat (length line) + 1 <= alloc_ceiling).
{ destruct HLHOME as (p & k & Hpk & Hp1 & Hp2).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HARc Hpk) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hkr).
  pose proof (req_size_pos k ltac:(lia)) as [_ Hreq]. lia. }
pose proof alloc_ceiling_lt as HACL.
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS Wc (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_rec_shape_of)) SUP_INSTANCE_VERB_STK sp0
    (siv_FP O) ly S W mem md [] lyc Sc _ kk REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-48) (getr (ms_regs ms) 1) [] _ HJ).
  - exact Tsp.
  - reflexivity.
  - lia.
  - unfold REC_SHAPE_OF_STK, ESTACK. lia.
  - rewrite WS. unfold REC_SHAPE_OF_STK, ESTACK. lia.
  - exact T3.
  - exact T4.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [unfold SIV_RSO_RET, AF_sup_instance_verb; lia | reflexivity].
  - rewrite P1, unsigned_lit_small by (unfold SIV_RSO_RET, AF_sup_instance_verb; lia). unfold SIV_RSO_RET, AF_sup_instance_verb. lia.
  - apply achain_low. unfold s0Z. rewrite T8. unfold w64. rewrite unsigned_lit_small by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
    unfold A_REC_SPILL in Hcb. lia.
  - intros HPRE1. unfold trec_shape_of_spec in TRSO.
    eapply (TRSO fx lyc Sc Wc (ms_regs ms) (ms_mem ms) _ (pl + Z.of_nat spn) v (afn_pre_na_of _ _ _ _ _ _ _ _ _ _ HPRE1) HRODc).
    + exact T10.
    + lia.
    + rewrite T11, Hlv. reflexivity.
    + rewrite Hlv. lia.
    + exact HROc.
    + exact VOBJS.
    + intros _. split.
      * exact (siv_slice_bytes _ pl line spn cspn HLSTR ltac:(lia)).
      * destruct HLHOME as (p & k & Hpk & Hp1 & Hp2).
        left. exists p, k. split; [exact Hpk|]. rewrite Hlv. lia.
    + unfold EV_REC_SHAPE_OF. unfold EV_SUP_INSTANCE_VERB, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in HEV. lia.
  - intros a (r & Hr & _). destruct Hr.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a (r & Hr & _). destruct Hr. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ2i & HP2 & HK2).
destruct HK2 as ((q & Q10 & Hq64 & HQARG) & HPerm & Hly2 & HS2).
rewrite P1. change (Z_to_bv 64 (BASE + 20416)) with (Z_to_bv 64 (BASE + SIV_RSO_RET)).
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2i as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _).
assert (KEEPF : forall a, sp0 - 48 <= a < sp0 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. rewrite <- (RDQ a). apply G1; [lia | lia | intros (r & Hr & _); destruct Hr]. }
assert (KEEPG : forall a, Exists (in_zr a) recb_PG -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. rewrite <- (RDQ a). destruct (siv_prog_unowned B HB a Ha) as [Hown Herr].
  apply G3; [exact (PIMG a Ha) | exact Hown | exact Herr |].
  apply fp_spares_closed; [apply sink_closed_pos; constructor | intros (r & Hr & _); destruct Hr]. }
assert (I4 : forall pn, In pn (lay_blocks Q1) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in B lyc Sc _ _ _ (ex_intro _ Q1 (conj HAREP (fun x => iff_refl _))) pn Hpn)).
assert (HBL2 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2))
  by (intros pn Hpn; apply (Permutation_in pn (Permutation_sym HPerm)); exact Hpn).
assert (HBL2' : forall pn, In pn (ablocks B ly2 S2) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; apply (Permutation_in pn HPerm); exact Hpn).
apply (siv_seg_tail B MT HY0 ly S W regs mem md ch pl ledger line R O ly2 S2 W2 mem2 md2 regs2
  (kk + EV_REC_SHAPE_OF) Q1 q CX HFRM).
unfold siv_at_tail. cbv zeta.
split; [exact HJ2|].
split; [unfold EV_REC_SHAPE_OF; lia|].
split; [exact (siv_frame_kept (w_H Wc) (w_H W2) memc mem2 sp0 regs HF KEEPF)|].
split.
{ assert (U2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
  split; [unfold spZ at 1; rewrite U2; exact Tsp|].
  split; [exact (eq_trans (HP2 3 ltac:(unfold acallee_saved; lia)) T3)|].
  split; [exact (eq_trans (HP2 4 ltac:(unfold acallee_saved; lia)) T4)|].
  split; [exact (eq_trans (HP2 8 ltac:(unfold acallee_saved; lia)) T8)|].
  intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)), (TP r ltac:(unfold acallee_saved; lia)). exact (Rhi r Hr). }
split.
{ apply (siv_arep_kept (ablocks B lyc Sc) _ (rdW Wc memc) _ _ Q1 HAREP).
  - intros pn Hpn. exact (HBL2 _ (I4 _ Hpn)).
  - intros a Ha. apply KEEPG. apply recb_grec_in. exact Ha.
  - intros a Ha. apply KEEPG. apply recb_spill_in. exact Ha.
  - intros p n0 i Hpn Hi. rewrite <- (RDQ (p + i)).
    pose proof (I4 _ Hpn) as Hpnc.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n0 HARc Hpnc) as (_ & _ & _ & _ & _ & _ & Hk).
    pose proof (req_size_pos n0 ltac:(lia)) as [_ Hreq].
    apply (G2 p n0 i Hpnc (HBL2 _ Hpnc)); [lia | intros (r & Hr & _); destruct Hr]. }
split; [exact I1|].
split; [intros pn Hpn Hno; exact (HBL2 _ (I2 pn Hpn Hno))|].
split; [intros pn Hpn; exact (I3 pn (HBL2' _ Hpn))|].
split; [exact Q10|]. split; [exact Hq64|].
rewrite <- Hvfw.
split; [exact HQARG|].
split.
{ rewrite HS2. apply (mle_weaken MT S Sc _ _ MTL HMLE). lia. }
rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HPerm), <- (blocks_bytes_bsum B lyc Sc). lia.
Qed.

End e.
End f.
End d.
