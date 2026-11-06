(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the last two steps of segment K of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B): 0x86a24 mv a0,s5; jal check_refusal and the call (lt_seg_K3), and 0x86a2c addi a0,sp,120; mv a1,s5; ld a2,112(sp) to the jal to check_round_trip at 0x86a38 (lt_seg_K4); the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_Krefusal.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (cl_FC_okX: a step from one segment statement to the next) and A/ACh2.v:122-290 (a program call through cl_callS and back). Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaSB CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo PaNoChain PaCallPg
  CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_Kcut
LLVMFuzzerTestOneInput_Karity_s1 LLVMFuzzerTestOneInput_Krefusal_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_reply_code_c HarnessPropsA.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the callee's statement, exactly LLVMFuzzerTestOneInput_c.v's Section hypothesis (every FP state) *)
Hypothesis HCHECK_REFUSAL : forall fx0 : YK11.FPState, @tcheck_refusal_spec fx0 rc SK PI B MT.
(* the per-binary facts, with the names of a Theorem Labs lane's RULING-STMT.md section 1 *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.
Let RUN := paj_run B LAWS.

(* 0x86a2c .. 0x86a38: a0 := sp + 120, a1 := s5 (g_rec.state before the send), a2 := the word at sp + 112
   (g_rec.host_settings before the send), jal check_round_trip; the state at the callee's entry is LT_RT_stmt's, at
   the ambient FP state (nothing here touches it) *)
Lemma lt_seg_K4 : lt_seg_K4_stmt B MT.
Proof.
unfold lt_seg_K4_stmt, LT_K4_stmt.
intros m HRT cx ly S W regs mem md k acc r Rh O1 text copy arr wp HBASE HFRM HBODY HKR.
cbv zeta.
destruct (vr_runA (RecModel.rec_clear (lt_R0 (x_pl cx) (x_n cx) r Rh)) (lt_D (x_pl cx) (x_n cx) r))
  as [[R1 xr] quit] eqn:HRUN.
intros HWORDS HREC HBUD.
pose proof HKR as (Hr & H23 & H24 & H21 & RS & RH & HWh).
pose proof HBODY as (HFR & _).
pose proof HFR as (HJ & Hsp & H3 & H4 & _).
pose proof HBASE as (HPRE0 & _).
pose proof HPRE0 as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (WL : LTOI_STK = 32768) by reflexivity.
assert (Hsp1 : spZ regs = spZ (x_regs cx) - 256) by (rewrite Hsp; reflexivity).
assert (Hal : spZ regs mod 16 = 0).
{ rewrite Hsp1. pose proof (Z.div_mod (spZ (x_regs cx)) 16 ltac:(lia)) as D. rewrite Hal16 in D.
  replace (spZ (x_regs cx) - 256) with ((spZ (x_regs cx) / 16 - 16) * 16) by lia. apply Z.mod_mul. lia. }
assert (HspR : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (HW112 : rdword (rdW W mem) (spZ regs + 112) = Some (r_host Rh)) by (rewrite Hsp; exact HWh).
destruct (kr_seed_loc W regs mem LO_K4 112 (r_host Rh) ltac:(vm_compute; reflexivity) HspR Hal ltac:(lia) HW112)
  as [HS SHOK].
assert (HEI : img_env VAL A_LIM (kr_E regs (r_host Rh))) by (unfold kr_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew (kr_E regs (r_host Rh)) n = ew (Ereg regs [Z_to_bv 64 (r_host Rh)]) n)
  by (intros n Hn; unfold kr_E; apply Eimg_low; exact Hn).
assert (HED : ed (kr_E regs (r_host Rh)) = ed (Ereg regs [Z_to_bv 64 (r_host Rh)])) by reflexivity.
remember (kr_E regs (r_host Rh)) as E eqn:HE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E21 : ew E 21 = getr regs 21) by (apply EEo; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 (r_host Rh)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 (r_host Rh)]) E).
{ split; [intros n Hn; rewrite EL by (unfold A_TEXT; lia); reflexivity | exact HED]. }
clear HE EL HED EEo.
paj_run_tok RUN HS HJ SHOK KRspan.
{ unfold awr_ok. intros a0 (r0 & Hin0 & Hr0). exfalso. vm_compute in Hin0. destruct Hin0 as [<- | []].
  cbn [YP09.r_wlo YP09.r_whi] in Hr0. lia. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
pmkst HS.
unfold frame_of in HF.
assert (Hmem : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (r0 & Hin0 & Hr0). vm_compute in Hin0.
  destruct Hin0 as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Hr0. lia. }
rewrite Hmem in HJ |- *.
assert (HPR : aregs_preserved regs (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [Z_to_bv 64 (r_host Rh)] HS); [exact HAE | vm_compute; reflexivity]. }
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
rewrite (SIGP CS_check_round_trip ltac:(unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (cmd_af CS_check_round_trip) with AF_check_round_trip by (vm_compute; reflexivity).
destruct (lt_kcut_keep B cx ly S W regs mem md k ly S W (ms_regs ms) mem mdv k m r Rh R1 O1
  (if quit then 1 else 0) text copy arr wp HBODY HKR HWORDS HREC HJ HPR (Permutation_refl _) (fun a _ => eq_refl))
  as (HB' & HK' & HW' & HR').
pose proof HK' as (_ & K23 & K24 & _).
pose proof (HRT fx cx ly S W (ms_regs ms) mem mdv k acc r Rh O1 text copy arr wp HBASE HFRM HB') as HRT'.
cbv zeta in HRT'. rewrite HRUN in HRT'. cbv beta iota in HRT'.
refine (HRT' Hr K23 K24 _ _ _ _ RS RH HW' HR' HBUD).
- rewrite P1. reflexivity.
- rewrite P10, Usp, Hsp. reflexivity.
- rewrite P11, E21. exact H21.
- rewrite P12, E32. reflexivity.
Qed.

(* 0x86a24 .. 0x86a28: a0 := s5 (g_rec.state before the send), jal check_refusal, and the call (PaNoChain.v's
   cl_callS_na with tcheck_refusal_spec at the ambient FP state: its post is apost_base); back at 0x86a2c the state
   is LT_K4_stmt's *)
Lemma lt_seg_K3 : lt_seg_K3_stmt B MT.
Proof.
unfold lt_seg_K3_stmt, LT_K3_stmt.
intros m K4 cx ly S W regs mem md k acc r Rh O1 text copy arr wp HBASE HFRM HBODY HKR.
cbv zeta.
destruct (vr_runA (RecModel.rec_clear (lt_R0 (x_pl cx) (x_n cx) r Rh)) (lt_D (x_pl cx) (x_n cx) r))
  as [[R1 xr] quit] eqn:HRUN.
intros HWORDS HREC HBUD.
pose proof HKR as (Hr & H23 & H24 & H21 & RS & RH & HWh).
(* the harness facts of the message (the cut file's lt_kregs_props) *)
pose proof (lt_kregs_props cx regs (rdW W mem) r Rh HKR) as HMP.
unfold msg_props_at in HMP. cbv zeta in HMP.
pose proof HRUN as HRUN'. unfold vr_runA in HRUN'. rewrite HRUN' in HMP. cbv beta iota in HMP.
destruct HMP as (HM1 & HM2 & HM3 & _ & _ & _ & _ & _ & HM9 & _).
pose proof HBODY as (HFR & _).
pose proof HFR as (HJ & Hsp & H3 & H4 & _).
pose proof HBASE as (HPRE0 & HROD0 & _ & HOBJ & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBOK.
assert (WL : LTOI_STK = 32768) by reflexivity.
assert (WS : CHECK_REFUSAL_STK = 12320) by reflexivity.
assert (E0 : EV_CHECK_REFUSAL = 0) by reflexivity.
assert (Hsp1 : spZ regs = spZ (x_regs cx) - 256) by (rewrite Hsp; reflexivity).
assert (Hal : spZ regs mod 16 = 0).
{ rewrite Hsp1. pose proof (Z.div_mod (spZ (x_regs cx)) 16 ltac:(lia)) as D. rewrite Hal16 in D.
  replace (spZ (x_regs cx) - 256) with ((spZ (x_regs cx) / 16 - 16) * 16) by lia. apply Z.mod_mul. lia. }
assert (HspR : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
assert (HW112 : rdword (rdW W mem) (spZ regs + 112) = Some (r_host Rh)) by (rewrite Hsp; exact HWh).
destruct (kr_seed_loc W regs mem LO_K3 112 (r_host Rh) ltac:(vm_compute; reflexivity) HspR Hal ltac:(lia) HW112)
  as [HS SHOK].
assert (HEI : img_env VAL A_LIM (kr_E regs (r_host Rh))) by (unfold kr_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew (kr_E regs (r_host Rh)) n = ew (Ereg regs [Z_to_bv 64 (r_host Rh)]) n)
  by (intros n Hn; unfold kr_E; apply Eimg_low; exact Hn).
assert (HED : ed (kr_E regs (r_host Rh)) = ed (Ereg regs [Z_to_bv 64 (r_host Rh)])) by reflexivity.
remember (kr_E regs (r_host Rh)) as E eqn:HE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E21 : ew E 21 = getr regs 21) by (apply EEo; reflexivity).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 (r_host Rh)]) E).
{ split; [intros n Hn; rewrite EL by (unfold A_TEXT; lia); reflexivity | exact HED]. }
clear HE EL HED EEo.
paj_run_tok RUN HS HJ SHOK KRspan.
{ unfold awr_ok. intros a0 (r0 & Hin0 & Hr0). exfalso. vm_compute in Hin0. destruct Hin0 as [<- | []].
  cbn [YP09.r_wlo YP09.r_whi] in Hr0. lia. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
pmkst HS.
unfold frame_of in HF.
assert (Hmem : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (r0 & Hin0 & Hr0). vm_compute in Hin0.
  destruct Hin0 as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Hr0. lia. }
rewrite Hmem in HJ |- *.
assert (HPR : aregs_preserved regs (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [Z_to_bv 64 (r_host Rh)] HS); [exact HAE | vm_compute; reflexivity]. }
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10.
rewrite (SIGP CS_check_refusal ltac:(unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (cmd_af CS_check_refusal) with AF_check_refusal by (vm_compute; reflexivity).
(* the state at the call *)
pose proof (proj1 HJ) as HAR.
assert (Hspm : spZ (ms_regs ms) = x_sp0 cx + -256).
{ unfold spZ at 1. rewrite (lt_pres_loc regs (ms_regs ms) 2%bv HPR ltac:(lt_cs)).
  change (bv_unsigned (getr regs 2)) with (spZ regs).
  rewrite Hsp. unfold x_sp1, x_sp0, LT_FRAME. lia. }
assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite (lt_pres_loc regs (ms_regs ms) 3%bv HPR ltac:(lt_cs)), H3; exact Hgp0).
assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite (lt_pres_loc regs (ms_regs ms) 4%bv HPR ltac:(lt_cs)), H4; exact Htp0).
assert (P10' : getr (ms_regs ms) 10 = w64 (r_state Rh)) by (rewrite P10, E21; exact H21).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4T : 4096 <= bv_unsigned (getr (ms_regs ms) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
(* arodata_okP and the read-only bytes at the call (CmdBase.v's arodata_ok_journalP with IMG's fields, and
   CmdRecRo.v's cmd_ro_ok_of_aro) *)
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW W mem)).
{ apply (arodata_ok_journalP SEGS CMD_RLO CMD_RHI (cif_relro_img _ _ IMG) (RO := cif_ro_below_ofl _ _ IMG) B
    LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem mdv k HJ).
  - intros a Hro Hf. exact (cif_prog_not_ro _ _ IMG a Hf Hro).
  - exact HROD0. }
pose proof (cmd_ro_ok_of_aro SEGS B LAWS HB IMG ly S W mem mdv HAR HRODc) as HROc.
(* the reply (rec_repA's areply_at at the message's reply x ++ [NUL]), g_rec.state and g_quitting *)
pose proof HREC as (HREP & _ & _ & HQ & RQ & _).
destruct HREP as (Q & HAREP & _).
destruct HAREP as (_ & _ & _ & _ & _ & HRPL & HSC & _).
unfold areply_at in HRPL. rewrite HM2 in HRPL.
destruct (l_reply Q) as [[p n]|]; [|destruct HRPL].
destruct HRPL as (A1 & _ & A3 & _ & A5 & A6 & A7 & _).
cbn [fst snd] in A1, A3, A5, A6, A7.
destruct (al_blocks _ _ LAWS ly S W mem mdv p n HAR A5) as (_ & Hp4096 & Hpceil & _).
destruct HSC as (_ & _ & _ & S4 & _ & _ & _ & _ & S9 & _).
assert (Hn0 : 0 <= n) by lia.
pose proof (req_size_pos n Hn0) as [Hrq _].
pose proof alloc_ceiling_lt as HACL.
assert (Rrep : 0 <= p < 2 ^ 64) by lia.
assert (HyN : Some xr = None -> p = 0) by discriminate.
assert (HyS : forall x, Some xr = Some x ->
  p <> 0 /\ in_blockA (ablocks B ly S) p (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) p x).
{ intros x Hx. injection Hx as <-. split; [exact A3|]. split.
  - exists p, n. split; [exact A5|]. rewrite length_app in A6. cbn [length] in A6. lia.
  - split; [exact A7 | exact HM3]. }
assert (HREF : forall x, Some xr = Some x -> reply_code_a x < 0 ->
  r_state R1 = r_state Rh /\ (if quit then 1 else 0) = 0).
{ intros x Hx Hneg. injection Hx as <-. destruct (HM9 Hneg) as [Hst Hq0]. rewrite Hq0. split; [|reflexivity].
  rewrite Hst. reflexivity. }
assert (HEV : st_nev S + EV_CHECK_REFUSAL <= EV_MAX).
{ pose proof (lt_nev_now B MT cx ly S W mem mdv k acc _ HBASE HJ HBUD) as H1. rewrite E0. lia. }
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS W (ms_regs ms) mem _ LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [] ly S mdv k CHECK_REFUSAL_STK [] EV_CHECK_REFUSAL (-256) (getr (ms_regs ms) 1)
    (fun ly2 S2 W2 regs2 mem2 md2 => Permutation (ablocks B ly2 S2) (ablocks B ly S) /\ ly2 = ly /\ S2 = S)
    HJ Hspm); [reflexivity | lia | rewrite WS; lia | rewrite WS, WL; lia | exact P3' | exact P4' | reflexivity
    | exact HraT | exact Hra4T | | ].
  - intros HPRE1. eapply SRr_mono.
    + apply (HCHECK_REFUSAL fx ly S W (ms_regs ms) mem mdv (r_state Rh) p (r_state R1) (if quit then 1 else 0)
        (Some xr) HPRE1 HRODc HROc HOBJ P10' RS A1 Rrep S4 S9 HQ RQ HyN HyS HREF HEV).
    + cbv beta. unfold apost_base. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HQ3).
      exists ly3, S3, regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|]. split; [exact HP3 | exact HQ3].
  - intros a (r0 & Hr0 & _). destruct Hr0. }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & _ & Hly3 & HS3e).
subst ly3 S3.
rewrite P1.
(* back at 0x86a2c: the frame, the live blocks and the program's statics are kept, s0..s11 preserved *)
assert (HPALL : aregs_preserved regs regs3) by exact (lt_pres_trans _ _ _ HPR HP3).
pose proof (lt_call_kept B HB LAWS IMG cx CHECK_REFUSAL_STK ly S W mem mdv ly S W3 mem3 md3 EV_CHECK_REFUSAL HJc3
  ltac:(unfold x_sp1, x_sp0, LT_FRAME; rewrite WL in Hslo; lia) ltac:(unfold x_sp0; lia) (Permutation_refl _)) as KEEP.
destruct (lt_kcut_keep B cx ly S W regs mem md k ly S W3 regs3 mem3 md3 (k + EV_CHECK_REFUSAL) m r Rh R1 O1
  (if quit then 1 else 0) text copy arr wp HBODY HKR HWORDS HREC HJ3 HPALL (Permutation_refl _) KEEP)
  as (HB3 & HKR3 & HW3 & HR3).
assert (HBUD3 : lt_bud MT cx S (k + EV_CHECK_REFUSAL) acc (3 + EV_CHECK_ROUND_TRIP R1 (lt_ws (x_pl cx) (x_n cx) r) +
  ev_from (31 - m) R1 (x_rest cx (lt_r' (x_pl cx) (x_n cx) r)))).
{ apply (lt_bud_eq MT cx S k acc _ _ _ HBUD); rewrite E0; ring. }
pose proof (K4 fx cx ly S W3 regs3 mem3 md3 (k + EV_CHECK_REFUSAL) acc r Rh O1 text copy arr wp HBASE HFRM HB3 HKR3) as K4'.
cbv zeta in K4'. rewrite HRUN in K4'. cbv beta iota in K4'.
exact (K4' HW3 HR3 HBUD3).
Qed.

End e.
End f.
End d.
