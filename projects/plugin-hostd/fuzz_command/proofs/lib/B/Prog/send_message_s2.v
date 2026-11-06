(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from this harness's lib/A/Prog/send_message_s2.v (the ASan walk,
   a working branch 4f5a539710b) to the ASan+UBSan build fuzz_command.asan-ubsan (lib/B): B's program
   points, the same offsets from the entry 0x86bf8. Re-fitted to a Theorem Labs lane's pass 4b (a working branch f490061c104): the memcpy
   entry at every FP state (forall fx0), used at the entry's. *)
(* Modified by Theorem Labs, 2026-10: segment s2 of send_message's walk on plugin-hostd/fuzz_command's ASan+UBSan
   image, in the shape of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close's backward
   chain) at origin/ossv/recipes c8557374ad2e, the __asan_memcpy call step of A/ACgc.v (cgif_addframe: a copy into
   the fresh block the malloc wrapper returned, from a live block). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow CmdSyms CmdList CmdPa.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaJournal CmdPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YE00 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_clear_c verbs_receive_c send_message_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import send_message_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* The segment (listing offsets from BASE + AF_send_message = 0x86bf8):
     0x86d10  beqz a0,0x86e40        malloc returned NULL: not taken, res >= 4096
     0x86d14  mv s6,a0
     0x86d18  addi s5,s8,32          s5 = &msg = F + 32
     0x86d1c  beqz s3,0x86d30        len = 0 skips the copy
     0x86d20  mv a0,s6; mv a1,s4; mv a2,s3
     0x86d2c  jal __asan_memcpy      returns to 0x86d30 = BASE + SM_J
   None of these instructions reads or writes memory, so the symbolic state needs no region: the registers as atoms
   of the configuration's own register file, and no fact. *)
Definition s2_ss : sstate := mkSS SM_RET_MALLOC sr_atoms [] None (mkFacts [] [] []).
Definition s2_SH : list shent := [].
Lemma s2_sp1 : forall sp0, 112 <= sp0 -> sp0 mod 16 = 0 ->
sp0 - 112 <= sm_sp1 sp0 <= sp0 - 96 /\ (sm_sp1 sp0 - sp0) mod 16 = 0.
Proof.
intros sp0 H0 H16. unfold sm_sp1.
assert (M : (sp0 - 96) mod 16 = 0) by (rewrite Zminus_mod, H16; reflexivity).
pose proof (sp1_facts (sp0 - 96) ltac:(lia) M) as (B1 & _ & M16).
split; [lia|]. rewrite Zminus_mod, M16, H16. reflexivity.
Qed.
Lemma s2_core : forall regs regs1 regs' F n src,
sm_regs_core regs regs1 F n src ->
getr regs' 2 = getr regs1 2 -> getr regs' 3 = getr regs1 3 -> getr regs' 4 = getr regs1 4 ->
getr regs' 8 = getr regs1 8 -> getr regs' 9 = getr regs1 9 -> getr regs' 18 = getr regs1 18 ->
getr regs' 19 = getr regs1 19 -> getr regs' 20 = getr regs1 20 -> getr regs' 23 = getr regs1 23 ->
getr regs' 24 = getr regs1 24 -> getr regs' 25 = getr regs1 25 -> getr regs' 26 = getr regs1 26 ->
getr regs' 27 = getr regs1 27 -> sm_regs_core regs regs' F n src.
Proof.
intros regs regs1 regs' F n src (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13)
Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 Q13.
unfold sm_regs_core. rewrite Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13.
repeat split; assumption.
Qed.
Ltac s2_cs := lazymatch goal with |- acallee_saved (bv_unsigned ?r) =>
let z := eval vm_compute in (bv_unsigned r) in change (acallee_saved z); unfold acallee_saved; lia end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the seed at the malloc wrapper's return (cgif's ng_entry, lib/A/ACk4.v:594-697, with no region) *)
Lemma s2_seed : forall (W : world SEGS) (regs1 : bvmap 5 word) mem,
st_ok_pi SEGS VAL (Eimg (Ereg regs1 [])) s2_ss
(restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + SM_RET_MALLOC)) mem (seg_rom SEGS))).
Proof.
intros W regs1 mem. rewrite restrict_mkst_fx. unfold s2_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- apply pairwise_disjoint_of_extents. cbn. exact I.
- split; [|split; exact I]. cbn. exact I.
Qed.
Lemma s2_shok : forall E m, sh_ok SEGS SMBx s2_SH E m.
Proof. intros E m. constructor. Qed.
(* a run over a symbolic state with no region leaves every byte as it was *)
Lemma s2_aview_nil : forall E rs (m m' : word -> option byte),
frame_of E rs m m' -> rs = [] -> forall H a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs m m' Hf -> H a. unfold aview, mbyte, mrestrict. cbv beta.
rewrite (Hf (Z_to_bv 64 a)) by (intros (r & Hr & _); destruct Hr). reflexivity.
Qed.
Lemma s2_vm_kept : forall H (m m' : word -> option byte) a (nb : nat) v,
val_mem SEGS (mrestrict H m) a nb v ->
(forall j, 0 <= j < Z.of_nat nb -> aview SEGS H m' (a + j) = aview SEGS H m (a + j)) ->
val_mem SEGS (mrestrict H m') a nb v.
Proof.
intros H m m' a nb v HV HK j Hj.
rewrite (mbyte_of_aview SEGS H H m m' (a + Z.of_nat j) (HK (Z.of_nat j) ltac:(lia))). exact (HV j Hj).
Qed.
Lemma s2_saved_kept : forall regs H (m m' : word -> option byte),
sm_saved regs (mrestrict H m) ->
(forall a, spZ regs - 88 <= a < spZ regs -> aview SEGS H m' a = aview SEGS H m a) ->
sm_saved regs (mrestrict H m').
Proof.
intros regs H m m' HS HK o r Hin.
assert (Ho : -88 <= o <= -8)
by (unfold sm_saved_list in Hin; cbn in Hin; repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <-; lia|]); destruct Hin).
apply (s2_vm_kept H m m'); [exact (HS o r Hin)|]. intros j Hj. apply HK. cbn in Hj. lia.
Qed.
Lemma s2_frame_kept : forall H (m m' : word -> option byte) F FL,
sm_frame (mrestrict H m) F FL ->
(forall a, F + 32 <= a < F + 128 \/ SB_F F + 4 <= a < SB_F F + 7 -> aview SEGS H m' a = aview SEGS H m a) ->
sm_frame (mrestrict H m') F FL.
Proof.
intros H m m' F FL (V1 & V2 & V3 & V4 & V5) HK. unfold sm_frame.
split; [|split; [|split; [|split]]]; (eapply s2_vm_kept; [eassumption|]); intros j Hj; apply HK; cbn in Hj; lia.
Qed.
(* registers of a symbolic state over the configuration's register file *)
Lemma s2_rm : forall (W : world SEGS) ss ms regs1 (r rn : bv 5) (nn : nat), Z.of_nat nn = bv_unsigned rn ->
st_ok SEGS (Eimg (Ereg regs1 [])) ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = SOff nn 0 ->
getr (ms_regs ms) r = getr regs1 rn.
Proof.
intros W ss ms regs1 r rn nn Hn HS Hr.
rewrite (st_ok_restrict_reg SEGS (w_H W) _ ss ms r HS), Hr, sv_denot_SOff0.
rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 rn) as H5; change (bv_modulus 5) with 32 in H5; unfold A_TEXT; lia).
exact (ew_Ereg_nat regs1 [] nn rn Hn).
Qed.
Lemma s2_rm_pi : forall (W : world SEGS) ss ms regs1 (r rn : bv 5) (nn : nat), Z.of_nat nn = bv_unsigned rn ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 [])) ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = SOff nn 0 ->
getr (ms_regs ms) r = getr regs1 rn.
Proof.
intros W ss ms regs1 r rn nn Hn HS Hr.
rewrite (st_ok_pi_restrict_reg (w_H W) _ ss ms r HS), Hr, sv_denot_SOff0.
rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 rn) as H5; change (bv_modulus 5) with 32 in H5; unfold A_TEXT; lia).
exact (ew_Ereg_nat regs1 [] nn rn Hn).
Qed.
Lemma s2_ro : forall (W : world SEGS) ss ms regs1 (r rn : bv 5) (nn : nat) c v, Z.of_nat nn = bv_unsigned rn ->
st_ok SEGS (Eimg (Ereg regs1 [])) ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = SOff nn c ->
getr regs1 rn = w64 v -> 0 <= v < 2 ^ 64 -> getr (ms_regs ms) r = w64 (v + c).
Proof.
intros W ss ms regs1 r rn nn c v Hn HS Hr Hv Hv64.
rewrite (st_ok_restrict_reg SEGS (w_H W) _ ss ms r HS), Hr. cbn [sv_denot].
rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 rn) as H5; change (bv_modulus 5) with 32 in H5; unfold A_TEXT; lia).
rewrite (ew_Ereg_nat regs1 [] nn rn Hn), Hv. unfold w64. rewrite unsigned_lit_small by exact Hv64. reflexivity.
Qed.
Lemma s2_ro_pi : forall (W : world SEGS) ss ms regs1 (r rn : bv 5) (nn : nat) c v, Z.of_nat nn = bv_unsigned rn ->
st_ok_pi SEGS VAL (Eimg (Ereg regs1 [])) ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = SOff nn c ->
getr regs1 rn = w64 v -> 0 <= v < 2 ^ 64 -> getr (ms_regs ms) r = w64 (v + c).
Proof.
intros W ss ms regs1 r rn nn c v Hn HS Hr Hv Hv64.
rewrite (st_ok_pi_restrict_reg (w_H W) _ ss ms r HS), Hr. cbn [sv_denot].
rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 rn) as H5; change (bv_modulus 5) with 32 in H5; unfold A_TEXT; lia).
rewrite (ew_Ereg_nat regs1 [] nn rn Hn), Hv. unfold w64. rewrite unsigned_lit_small by exact Hv64. reflexivity.
Qed.
Lemma s2_ra : forall (W : world SEGS) ss ms E k, img_env VAL A_LIM E ->
st_ok SEGS E ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) 1 = SOff A_TEXT k ->
getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + k).
Proof.
intros W ss ms E k HEI HS Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) E ss ms 1 HS), Hr. exact (codeptr_val E k HEI).
Qed.
Ltac s2_name_ms nm :=
lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?m) _ _ _) _) _ =>
match goal with mm : machine_state |- _ => lazymatch mm with m => rename mm into nm end end end.
Ltac s2_keep_pi HS :=
lazymatch goal with |- getr (ms_regs ?m) ?r = getr ?rg ?r =>
let nn := eval vm_compute in (Z.to_nat (bv_unsigned r)) in exact (s2_rm_pi _ _ m rg r r nn eq_refl HS eq_refl) end.
Ltac s2_keep_call CS msT HS :=
lazymatch goal with |- getr _ ?r = getr ?rg ?r =>
let nn := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
rewrite (CS r ltac:(s2_cs)); exact (s2_rm _ _ msT rg r r nn eq_refl HS eq_refl) end.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIGMA CS___asan_memcpy).
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Theorem sm_s2 : SM_P2_stmt B MT -> SM_P1_stmt B MT.
Proof.
intros P2 ly S W regs mem md ch src n D R O rest lyc Sc Wc regs1 memc mdc k fpos res
CX JR Hk RC R10 SAV FRM Hbl Hres Hnin MLE.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hn8192 & HlenD & HD & Hrest & HPerm & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof RC as (Rsp & Rgp & Rtp & _ & _ & _ & R19 & R20 & _ & R24 & _).
pose proof asan_consts as (C1 & _).
assert (HSTK : 16496 <= SEND_MESSAGE_STK)
by (unfold SEND_MESSAGE_STK; pose proof (Z.le_max_l ASTACK (Z.max REC_CLEAR_STK VERBS_RECEIVE_STK)) as M; unfold ASTACK in M |- *; lia).
pose proof (s2_sp1 (spZ regs) ltac:(lia) Hal16) as SP1.
pose proof (proj1 JR) as HJ0.
pose proof HJ0 as (HARc & Hly & _).
assert (Hinres : In (res, Z.max n 1) (ablocks B lyc Sc)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hinres) as (_ & _ & Hresceil & Hresapp & _).
pose proof (req_size_pos (Z.max n 1) ltac:(lia)) as Hrq.
assert (Hinf : In (1, fpos) (frames Sc)) by (rewrite (proj2 JR); left; reflexivity).
pose proof (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 1 fpos HARc Hinf) as (HF4096 & HFceil & _).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc res (Z.max n 1) 1 fpos HARc Hinres Hinf) as DRF.
assert (HFA : frame_addr lyc 1 fpos = frame_addr ly 1 fpos)
by (unfold frame_addr; destruct Hly as (_ & _ & _ & _ & _ & HlyF & _); rewrite HlyF; reflexivity).
unfold zdisjoint in DRF. cbn [fst snd] in DRF. rewrite HFA in HF4096, HFceil, DRF.
replace (fs_frame_bytes 1) with 128 in HFceil, DRF by reflexivity.
pose proof (Z.div_mod (frame_addr ly 1 fpos) 8 ltac:(lia)) as DF.
pose proof (Z.mod_pos_bound (frame_addr ly 1 fpos) 8 ltac:(lia)) as MF.
pose proof (s2_seed Wc regs1 memc) as HS.
pose proof (s2_shok (Eimg (Ereg regs1 [])) (mrestrict (w_H Wc) memc)) as SHOK.
set (E := Eimg (Ereg regs1 [])) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E10 : ew E 10 = Z_to_bv 64 res)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 10 10%bv eq_refl); exact R10).
assert (E19 : ew E 19 = Z_to_bv 64 n)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs1 _ 19 19%bv eq_refl); exact R19).
pose proof HJ0 as HJ.
(* 0x86d10 beqz a0: res >= 4096 *)
psrr_branch_tok RUN BR HS SHOK SMBspan.
{ exfalso. rewrite branch_eq_U in Hc. replace (U E (SLit 0)) with 0 in Hc by reflexivity.
  rewrite (U_atom E 10 res E10) in Hc by lia. apply Z.eqb_eq in Hc. lia. }
clear Hc. paj_run_tok RUN HS HJ SHOK SMBspan.
{ apply awr_ok_nil. }
pose proof (s2_aview_nil _ _ _ _ HF eq_refl) as FN1. clear HF HFr HG.
(* 0x86d1c beqz s3 *)
psrr_branch_tok RUN BR HS SHOK SMBspan.
- (* len = 0: straight to 0x86d30 *)
  rewrite branch_eq_U in Hc. replace (U E (SLit 0)) with 0 in Hc by reflexivity.
  rewrite (U_atom E 19 n E19) in Hc by lia. apply Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK SMBspan SM_J.
  { apply awr_ok_nil. }
  pose proof (s2_aview_nil _ _ _ _ HF eq_refl) as FN2. clear HF HFr HG.
  pmkst HS. s2_name_ms msA.
  apply (P2 ly S W regs mem md ch src n D R O rest lyc Sc Wc (ms_regs msA) (ms_mem msA) _ k fpos res).
  + exact CX.
  + split; [exact HJ | exact (proj2 JR)].
  + exact Hk.
  + apply (s2_core regs regs1 _ _ _ _ RC); s2_keep_pi HS.
  + exact (s2_ro_pi Wc _ msA regs1 21%bv 24%bv 24%nat 32 _ eq_refl HS eq_refl R24 ltac:(lia)).
  + rewrite (s2_rm_pi Wc _ msA regs1 22%bv 10%bv 10%nat eq_refl HS eq_refl). exact R10.
  + apply (s2_saved_kept regs (w_H Wc) memc _ SAV). intros a _. rewrite FN2, FN1. reflexivity.
  + apply (s2_frame_kept (w_H Wc) memc _ _ _ FRM). intros a _. rewrite FN2, FN1. reflexivity.
  + exact Hbl.
  + exact Hres.
  + exact Hnin.
  + intros i Hi. exfalso. lia.
  + exact MLE.
- (* len <> 0: the copy *)
  rewrite branch_eq_U in Hc. replace (U E (SLit 0)) with 0 in Hc by reflexivity.
  rewrite (U_atom E 19 n E19) in Hc by lia. apply Z.eqb_neq in Hc.
  destruct (Hrest Hc) as (p & kk & Hinp & Hp1 & Hp2).
  assert (HinpS : In (p, kk) (ablocks B ly S))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPerm | apply in_or_app; right; exact Hinp]).
  assert (HinpC : In (p, kk) (ablocks B lyc Sc)) by (rewrite Hbl; apply in_or_app; left; exact HinpS).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc HinpC) as (_ & Hp4096 & Hpceil & _ & _ & _ & Hkk).
  pose proof (req_size_pos kk ltac:(lia)) as Hrqk.
  pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc res (Z.max n 1) p kk HARc Hinres HinpC
  ltac:(intros Heq; apply Hnin; rewrite Heq; exact HinpS)) as DRP.
  unfold zdisjoint in DRP. cbn [fst snd] in DRP.
  paj_run_tok RUN HS HJ SHOK SMBspan.
  { apply awr_ok_nil. }
  pose proof (s2_aview_nil _ _ _ _ HF eq_refl) as FN2. clear HF HFr HG.
  pmkst HS. s2_name_ms msT.
  pose proof HJ as (HART & _ & _ & _ & _ & _ & _ & _ & _ & HKB & _).
  assert (Q2 : getr (ms_regs msT) 2 = w64 (sm_sp1 (spZ regs)))
  by (rewrite (s2_rm Wc _ msT regs1 2%bv 2%bv 2%nat eq_refl HS eq_refl); exact Rsp).
  assert (Qsp : spZ (ms_regs msT) = sm_sp1 (spZ regs))
  by (change (spZ (ms_regs msT)) with (bv_unsigned (getr (ms_regs msT) 2)); rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
  assert (Q10 : getr (ms_regs msT) 10 = w64 res)
  by (rewrite (s2_rm Wc _ msT regs1 10%bv 10%bv 10%nat eq_refl HS eq_refl); exact R10).
  assert (Q11 : getr (ms_regs msT) 11 = w64 src)
  by (rewrite (s2_rm Wc _ msT regs1 11%bv 20%bv 20%nat eq_refl HS eq_refl); exact R20).
  assert (Q12 : getr (ms_regs msT) 12 = w64 n)
  by (rewrite (s2_rm Wc _ msT regs1 12%bv 19%bv 19%nat eq_refl HS eq_refl); exact R19).
  assert (Q3 : getr (ms_regs msT) 3 = w64 (as_gp B))
  by (rewrite (s2_rm Wc _ msT regs1 3%bv 3%bv 3%nat eq_refl HS eq_refl), Rgp; exact Hgp).
  assert (Q4 : getr (ms_regs msT) 4 = w64 (as_tp B))
  by (rewrite (s2_rm Wc _ msT regs1 4%bv 4%bv 4%nat eq_refl HS eq_refl), Rtp; exact Htp).
  assert (Q1 : getr (ms_regs msT) 1 = Z_to_bv 64 (BASE + SM_J)) by exact (s2_ra Wc _ msT E SM_J HEI HS eq_refl).
  assert (DEST : forall a, res <= a < res + n ->
    awr_byte SEGS B SEND_MESSAGE_STK (spZ regs) [] (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc [(1, fpos)] a /\
    ~ (spZ regs + (sm_sp1 (spZ regs) - spZ regs) - ESTACK <= a < spZ regs + (sm_sp1 (spZ regs) - spZ regs))).
  { intros a Ha. split.
    - right; right; left. exists res, (Z.max n 1). split; [exact Hinres|]. split; [exact Hnin|]. lia.
    - unfold ESTACK. lia. }
  assert (WR : forall a, res <= a < res + n -> inFP [] a ->
    (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a) \/ spZ regs <= a < ly_top lyc ->
    writable_at SEGS (mrestrict (w_H Wc) (ms_mem msT)) a).
  { intros a _ Hfp. destruct (inFP_nil a Hfp). }
  assert (SRC : 0 <= src /\ src + n <= 2 ^ 63 /\ src_ok SEGS Wc (ms_regs msT) (ms_mem msT) src n /\
    (res + n <= src \/ src + n <= res) /\ amem_range src n /\
    range_addressable (aview SEGS (w_H Wc) (ms_mem msT)) SHADOW_OFF src n /\
    (0 < n -> shadow_hull_vis (aview SEGS (w_H Wc) (ms_mem msT)) src n)).
  { split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - apply (aview_some_of_apresent SEGS).
        destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HART HinpC) as (_ & _ & _ & _ & HPp & _).
        exact (proj1 (HPp a ltac:(lia))).
      - rewrite Qsp. unfold ESTACK. lia. }
    split; [lia|]. split; [exact (amem_range_of_block SEGS B LAWS lyc Sc Wc _ _ p kk src n HART HinpC ltac:(lia) ltac:(lia))|].
    split; [exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc _ _ p kk src n HART HinpC ltac:(lia) ltac:(lia))|].
    intros H0. exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc _ _ p kk src n HART HinpC ltac:(lia) ltac:(lia) H0). }
  eapply SRr_bind.
  { exact (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA CS___asan_memcpy) (AMEMCPY fx) Wc (ms_regs msT) (ms_mem msT)
      SEND_MESSAGE_STK (spZ regs) [] ly S W mem md [(1, fpos)] lyc Sc _ k res src n (sm_sp1 (spZ regs) - spZ regs)
      (Z_to_bv 64 (BASE + SM_J)) HJ Q10 Q11 Q12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Qsp; lia) (proj2 SP1)
      ltac:(lia) ltac:(unfold ESTACK; lia) Q3 Q4 Q1 (ret_ok_codeptr_v SM_J ltac:(unfold SM_J, AF_send_message; lia) eq_refl)
      DEST WR
      (amem_range_of_block SEGS B LAWS lyc Sc Wc _ _ res (Z.max n 1) res n HART Hinres ltac:(lia) ltac:(lia))
      (range_addressable_of_block SEGS B LAWS lyc Sc Wc _ _ res (Z.max n 1) res n HART Hinres ltac:(lia) ltac:(lia))
      (fun H0 => shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc _ _ res (Z.max n 1) res n HART Hinres ltac:(lia) ltac:(lia) H0)
      SRC). }
  cbv beta. intros W3 c3 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & HCPY & HKEEP & _ & _).
  cbv beta iota in HCPY.
  assert (CS : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr (ms_regs msT) rr)
  by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx).
  apply (P2 ly S W regs mem md ch src n D R O rest lyc Sc Wc regs2 mem2 md2 k fpos res).
  + exact CX.
  + split; [exact HJ2 | exact (proj2 JR)].
  + exact Hk.
  + apply (s2_core regs regs1 _ _ _ _ RC); s2_keep_call CS msT HS.
  + rewrite (CS 21%bv ltac:(s2_cs)).
    exact (s2_ro Wc _ msT regs1 21%bv 24%bv 24%nat 32 _ eq_refl HS eq_refl R24 ltac:(lia)).
  + rewrite (CS 22%bv ltac:(s2_cs)), (s2_rm Wc _ msT regs1 22%bv 10%bv 10%nat eq_refl HS eq_refl). exact R10.
  + apply (s2_saved_kept regs (w_H Wc) memc mem2 SAV). intros a Ha.
    rewrite HKEEP by (unfold ESTACK; lia). rewrite FN2, FN1. reflexivity.
  + apply (s2_frame_kept (w_H Wc) memc mem2 _ _ FRM). intros a Ha. unfold SB_F, SB in Ha.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hresapp.
    rewrite HKEEP by (unfold ESTACK; lia). rewrite FN2, FN1. reflexivity.
  + exact Hbl.
  + exact Hres.
  + exact Hnin.
  + intros i Hi. rewrite (HCPY (Z.of_nat i) ltac:(lia)).
    replace (src + Z.of_nat i) with (p + (src - p + Z.of_nat i)) by lia.
    rewrite (HKB p kk (src - p + Z.of_nat i) HinpS HinpC ltac:(lia) (inFP_nil _)).
    replace (p + (src - p + Z.of_nat i)) with (src + Z.of_nat i) by lia. exact (HD i Hi).
  + exact MLE.
Qed.
End e.
End f.
End d.
