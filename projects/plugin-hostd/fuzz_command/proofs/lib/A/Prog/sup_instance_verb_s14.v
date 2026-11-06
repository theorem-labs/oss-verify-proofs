(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the segment of sup_instance_verb's ASan walk (plugin-hostd/fuzz_command) from the
   return of arg_i (0x8b474) through the strspn wrapper, after lib/A/Prog/sup_reply_code.v (a step through a
   runtime entry by PaArt.aj_art_at) and proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v. *)
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
  RecBTemplateSiv sup_instance_verb_s2 sup_instance_verb_s3 sup_instance_verb_s4 sup_instance_verb_s5 sup_instance_verb_s6 sup_instance_verb_s7 sup_instance_verb_s8 sup_instance_verb_s9 sup_instance_verb_s10.
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

Lemma siv_seg_A2 : siv_hyps B MT -> siv_A2_goal B MT.
Proof.
intros HY. unfold siv_A2_goal. intros ly S W regs mem md ch pl ledger line R O lyc Sc Wc memc mdc regs1 kk Q1 CX HFRM MID R9.
pose proof HY as HY0.
destruct HY as [TRCF TARG_LINE TARG_I TRSO TANSWER ASTRSPN ASTRCSPN VOBJS TL HB MTL PIMG PWR SIGP ROK RRO RELRO HTV
  RECC ROMV ZSH HULLL ROPA].
pose proof CX as (HPRE & HROD & HRO & H10 & Hpl64 & H11 & Hled & HLB & HLSTR0 & HLL & HLAP & HREP & HFR8 & HEV
  & HLIVE & HMOK).
pose proof MID as (HJ & Hkk & HF & HR & HAREP & I1 & I2 & I3 & HMLE & HLV).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO. pose proof pa_segs_low as Hsegs.
pose proof alloc_ceiling_value as [HACm HAC].
pose proof HR as (Rsp & Rgp & Rtp & R8 & Rhi).
assert (WS : SUP_INSTANCE_VERB_STK = 16592) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
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
destruct (siv_seed_mid B HB VOBJS SIV_I_RET sr_atoms lyc Sc Wc memc mdc regs regs1 sp0 n c (proj1 HJ)
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
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (10%bv : bv 5) P10.
prreg HS (11%bv : bv 5) P11. prreg HS (18%bv : bv 5) P18.

assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by (intros k r Hk; apply siv_E_reg; exact Hk).
pose proof (proj1 HJ) as HARc.
(* the line where it lives, and its bounds *)
destruct (siv_line_kept B HB PIMG HTV ly S W mem md R O pl line lyc Sc Wc (ms_mem ms) _ _ _ kk
  HAR HrepE HLB HLAP HLSTR0 HJ I2) as (HLSTR & HLHOME & HLTAIL).
assert (HPLB : 0 < pl /\ pl + Z.of_nat (length line) + 1 <= alloc_ceiling).
{ destruct HLHOME as (p & k & Hpk & Hp1 & Hp2).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HARc Hpk) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hkr).
  pose proof (req_size_pos k ltac:(lia)) as [_ Hreq]. lia. }
pose proof (siv_spn_le line) as Hspn.
assert (T2 : getr (ms_regs ms) 2 = getr regs1 2).
{ rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS); cbn [ms_regs].
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end.
  cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; apply EE; reflexivity. }
assert (Tsp : spZ (ms_regs ms) = sp0 + -48) by (unfold spZ; rewrite T2; fold (spZ regs1); lia).
assert (TR : forall r, r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ 20 <= r <= 27 ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)).
{ intros r Hr. assert (Hr8 : r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]];
  (rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ _ _ HS); cbn [ms_regs];
   lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
   cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; apply EE; reflexivity). }
assert (T3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by exact (eq_trans (TR 3 ltac:(lia)) Rgp).
assert (T4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by exact (eq_trans (TR 4 ltac:(lia)) Rtp).
assert (T8 : getr (ms_regs ms) 8 = w64 c) by exact (eq_trans (TR 8 ltac:(lia)) R8).
assert (EV61 : VAL (A_OBJ 61) = 0x21d60) by (rewrite (VOBJS 61%nat ltac:(vm_compute; lia)); vm_compute; reflexivity).
assert (E302 : ew E 302 = Z_to_bv 64 0x21d60).
{ change 302%nat with (A_OBJ 61). rewrite (img_env_atomP E (A_OBJ 61) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite EV61. reflexivity. }
assert (T9 : getr (ms_regs ms) 9 = w64 pl) by exact (eq_trans (TR 9 ltac:(lia)) R9).
assert (T18 : getr (ms_regs ms) 18 = w64 0x21d60) by (rewrite P18; exact E302).
assert (T10 : getr (ms_regs ms) 10 = w64 pl) by (rewrite P10, (EE 9%nat 9%bv eq_refl); exact R9).
assert (T11 : getr (ms_regs ms) 11 = w64 0x21d60) by (rewrite P11; exact E302).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms)))
  by exact (siv_aro_kept B RRO RELRO ROPA ly S W mem md _ R O lyc Sc Wc (ms_mem ms) _ _ _ _ _ HAR HrepE HJ HROD).
assert (HROc : cmd_ro_ok (rdW Wc (ms_mem ms))) by exact (ROK lyc Sc Wc (ms_mem ms) _ HARc HRODc).
pose proof (siv_set_at _ HROc) as [HSET HSETT].
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS Hsegs (pal_env B TL) (2 * ESTACK) (fun _ => False) (SIG CS___interceptor_trampoline_strspn)
    Wc (ms_regs ms) (ms_mem ms) SUP_INSTANCE_VERB_STK sp0 (siv_FP O) ly S W mem md [] lyc Sc _ kk (-48)
    (Z_to_bv 64 (BASE + 20388)) _ HJ Tsp eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite WS, Hes; lia) P1
    (fun a (H : False) => False_ind _ H)).
  apply (ASTRSPN fx lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pl 0x21d60 line PSIV.siv_set).
  - exact (proj1 (proj2 (RECC lyc Sc Wc (ms_mem ms) _ HARc))).
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) SUP_INSTANCE_VERB_STK sp0 (siv_FP O) ly S W mem md [] lyc Sc Wc (ms_mem ms) _ kk
      (ms_regs ms) (-48) HJ Tsp eq_refl ltac:(lia) ltac:(rewrite Hes; lia) ltac:(rewrite WS, Hes; lia) HraT T3 T4).
  - exact T10.
  - exact T11.
  - lia.
  - lia.
  - apply (astr_atR_view SEGS). exact HLSTR.
  - apply (astr_atR_view SEGS). exact HSET.
  - pose proof (siv_line_rd B lyc Sc Wc (ms_mem ms) _ (ms_regs ms) pl line 0%nat (2 * ESTACK) HARc HLHOME
      ltac:(lia) ltac:(rewrite Tsp, Hes; lia)) as HRD.
    rewrite Z.add_0_r in HRD. exact HRD.
  - destruct HLHOME as (p0 & k0 & Hpk0 & Hp01 & Hp02).
    apply (amem8_of_blockA SEGS B LAWS lyc Sc Wc (ms_mem ms) _ pl (astr_len line) HARc);
      [exists p0, k0; unfold astr_len; split; [exact Hpk0 | lia] | unfold astr_len; lia].
  - pose proof (ZSH lyc Sc Wc (ms_mem ms) _ HARc) as Zr. pose proof (HULLL lyc Sc Wc (ms_mem ms) _ HARc) as Zh.
    change (astr_len PSIV.siv_set + 1) with 3.
    split; [lia|]. split; [lia|]. split; [lia|]. split.
    + intros a Ha. split; [|unfold ascratch_stk; rewrite Tsp, Hes; lia].
      destruct HSET as [HSB _]. replace a with (0x21d60 + Z.of_nat (Z.to_nat (a - 0x21d60))) by lia.
      rewrite (HSB (Z.to_nat (a - 0x21d60))) by (cbn; lia). discriminate.
    + split; [unfold amem_range; left; lia|]. split; [exact Zr | intros _; exact Zh].
  - change (astr_len PSIV.siv_set) with 2. apply amem8_of_low; unfold kLowMemEnd; lia.
  - unfold astr_len. exact HLTAIL.
  - change (0x21d60 + astr_len PSIV.siv_set) with 0x21d62. exact HSETT.
  - exact (ROMV Wc (ms_mem ms) HRODc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
change (Z_to_bv 64 (BASE + 20388)) with (Z_to_bv 64 (BASE + SIV_SPN_RET)).
assert (KEEPA : forall a, 0 <= a < sp0 - 48 - 2 * ESTACK -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha. rewrite <- (RDQ a). apply HK2; [lia | rewrite Hes in *; lia | tauto]. }
assert (KEEPF : forall a, sp0 - 48 <= a < sp0 -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha. rewrite <- (RDQ a). apply HK2; [lia | rewrite Hes; lia | tauto]. }
pose proof (proj1 HJ2) as HAR2.
apply (siv_seg_A3 B MT HY0 ly S W regs mem md ch pl ledger line R O lyc Sc Wc mem2 md2 regs2 kk Q1 CX HFRM).
- split; [exact HJ2|]. split; [exact Hkk|].
  split; [exact (siv_frame_kept (w_H Wc) (w_H Wc) memc mem2 sp0 regs HF KEEPF)|].
  split.
  { assert (U2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
    split; [unfold spZ at 1; rewrite U2; exact Tsp|].
    split; [exact (eq_trans (HP2 3 ltac:(unfold acallee_saved; lia)) T3)|].
    split; [exact (eq_trans (HP2 4 ltac:(unfold acallee_saved; lia)) T4)|].
    split; [exact (eq_trans (HP2 8 ltac:(unfold acallee_saved; lia)) T8)|].
    intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)), (TR r ltac:(lia)). exact (Rhi r Hr). }
  split.
  { apply (siv_arep_kept (ablocks B lyc Sc) _ (rdW Wc memc) _ _ Q1 HAREP).
    - exact (rec_repA_in B lyc Sc _ _ _ (ex_intro _ Q1 (conj HAREP (fun x => iff_refl _)))).
    - intros a Ha. apply KEEPA. unfold A_G_REC in Ha. rewrite Hes. lia.
    - intros a Ha. apply KEEPA. unfold A_REC_SPILL in Ha. rewrite Hes. lia.
    - intros p n0 i Hpn Hi.
      assert (Hpnc : In (p, n0) (ablocks B lyc Sc))
        by exact (rec_repA_in B lyc Sc _ _ _ (ex_intro _ Q1 (conj HAREP (fun x => iff_refl _))) _ Hpn).
      destruct (al_blocks _ _ LAWS _ _ _ _ _ p n0 HARc Hpnc) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hk).
      pose proof (req_size_pos n0 ltac:(lia)) as [_ Hreq].
      apply KEEPA. rewrite Hes. lia. }
  split; [exact I1|]. split; [exact I2|]. split; [exact I3|]. split; [exact HMLE | exact HLV].
- exact (eq_trans (HP2 9 ltac:(unfold acallee_saved; lia)) T9).
- exact (eq_trans (HP2 18 ltac:(unfold acallee_saved; lia)) T18).
- rewrite HQ2. reflexivity.
Qed.

End e.
End f.
End d.
