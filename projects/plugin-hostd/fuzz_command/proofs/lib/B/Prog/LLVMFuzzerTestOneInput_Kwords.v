(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the check_words step of segment K of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86a1c addi a0,sp,120 and 0x86a20 jal check_words, to the return point 0x86a24): lt_seg_K2, from the cut after check_arity (LT_K2_stmt) through the call to the cut after check_words (LT_K3_stmt, taken at every FP state: LTA_K3); the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_Kwords.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v cl_FC_okX (a symbolic run to the call, then the next statement) and A/ACh2.v:122-290 (a program call through cl_callS and back). check_words returns at an FP state of its own (apost_baseF), so the call goes through PaFx.v's cl_callSF, the next cut is applied at that FP state (rounding mode 0 by fxrel_frm0) and its post lifted back by srr_apost_baseF_lift; the frame chain at s0 = -1 is achain's empty case; the cut's facts are carried by _Karity_s1.v's lt_kcut_keep and lt_call_kept. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB PaCallPg PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo
  CmdRecFacts sup_reply_code_c HarnessPropsA.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import joined_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s01
LLVMFuzzerTestOneInput_Kcut LLVMFuzzerTestOneInput_Karity_s1 LLVMFuzzerTestOneInput_Kwords_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

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
(* the callee's statement, with the name LLVMFuzzerTestOneInput_c.v:204 gives it (at every FP state) *)
Hypothesis HCHECK_WORDS : forall fx0 : YK11.FPState, @tcheck_words_spec fx0 rc SK PI B MT.
(* the walk hypotheses, with the names of a Theorem Labs lane's RULING-STMT.md section 1 *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis MTL : ameter_laws MT.
Hypothesis IMG : cmd_img_facts SEGS B.

Lemma lt_seg_K2 : lt_seg_K2_stmt B MT.
Proof.
pose proof (paj_run B LAWS) as RUN.
unfold lt_seg_K2_stmt. intros m HK3. unfold LT_K2_stmt.
intros cx ly S W regs mem md k acc r Rh O1 text copy arr wp HBASE HFRM HBODY HKR.
cbv zeta.
destruct (vr_runA (RecModel.rec_clear (lt_R0 (x_pl cx) (x_n cx) r Rh)) (lt_D (x_pl cx) (x_n cx) r))
  as [[R1 xr] quit] eqn:EVR.
intros HWD HREC HBUD.
(* the next cut at the run's result, at an FP state with rounding mode 0 (check_words returns at one of its own) *)
assert (HK3' : forall (fx1 : YK11.FPState) ly' S' W' regs' mem' md' k' acc',
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx1)) 5) 7 = 0 ->
  lt_body B cx ly' S' W' regs' mem' md' k' m -> lt_kregs cx regs' (rdW W' mem') r Rh ->
  lt_words cx (rdW W' mem') (lt_D (x_pl cx) (x_n cx) r) (lt_ws (x_pl cx) (x_n cx) r) text copy arr wp ->
  lt_rec B cx ly' S' W' mem' R1 O1 (if quit then 1 else 0) (lt_wblocks (lt_D (x_pl cx) (x_n cx) r) text copy arr) ->
  lt_bud MT cx S' k' acc' (3 + EV_CHECK_REFUSAL + EV_CHECK_ROUND_TRIP R1 (lt_ws (x_pl cx) (x_n cx) r) +
    ev_from (31 - m) R1 (x_rest cx (lt_r' (x_pl cx) (x_n cx) r))) ->
  SRr SEGS W' (mkCfg (@mkst fx1 regs' (Z_to_bv 64 (BASE + LO_K3)) mem' (seg_rom SEGS)) md')
    (lt_post (fx := fx1) B MT cx)).
{ intros fx1 ly' S' W' regs' mem' md' k' acc' H0 H1 H2 H3 H4 H5.
  pose proof (HK3 fx1 cx ly' S' W' regs' mem' md' k' acc' r Rh O1 text copy arr wp HBASE H0 H1 H2) as HK.
  cbv zeta in HK. rewrite EVR in HK. exact (HK H3 H4 H5). }
clear HK3.
(* the harness facts: the words the recorder's calls carry (lt_kregs_props, conjunct 8) *)
assert (HWP : words_prop_at atoi_a R1 (lt_ws (x_pl cx) (x_n cx) r)).
{ pose proof (lt_kregs_props cx regs (rdW W mem) r Rh HKR) as HMSG.
  unfold msg_props_at in HMSG. cbv zeta in HMSG. unfold vr_runA in EVR. rewrite EVR in HMSG.
  destruct HMSG as (_ & _ & _ & _ & _ & _ & _ & HW & _). exact HW. }
pose proof (lt_ws_bounds (x_pl cx) (x_n cx) r) as Hbnd. cbv zeta in Hbnd.
destruct Hbnd as (HL0 & H2ws & Hws4 & H8ws & Hjn).
pose proof (lt_w_align B MT cx HBASE) as Hwal.
(* the entry's facts *)
pose proof HBASE as (HPRE0 & _ & _ & HOBJ & _ & _ & _ & _ & _ & HFR0 & _ & _ & _ & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (Hal0 & HS00 & Hceil0 & Hslo0 & Hshi0 & H470 & Hbot0 & Htop0 & Htop20).
assert (Hx0 : x_sp0 cx = spZ (x_regs cx)) by reflexivity.
assert (Hx1 : x_sp1 cx = spZ (x_regs cx) - 256) by reflexivity.
assert (WL : LTOI_STK = 32768) by reflexivity.
pose proof asan_consts as (C1 & _).
(* the point's facts *)
pose proof HBODY as (HFR & HSLOT & R8 & R9 & R18 & R25 & R26 & R27 & Hm).
pose proof HFR as (HJ0 & Hsp & R3 & R4 & HSAVED).
pose proof HKR as (Hr & R23 & R24 & R21 & Hstate & Hhost & Hhb).
pose proof HWD as HWD'. unfold lt_words in HWD'. cbv zeta in HWD'.
destruct HWD' as (Wtext & Wcopy & Warr & Wn & Wlen & Wslots & Wstr).
pose proof HREC as (HREPA & Hspill & Hcalls & Hq & Hqr & HPERM).
set (ws := lt_ws (x_pl cx) (x_n cx) r) in *.
set (L0 := StrFun.strnlen_res (Z.of_nat (length (lt_D (x_pl cx) (x_n cx) r))) (lt_D (x_pl cx) (x_n cx) r)) in *.
(* two of the three words blocks are live: the pointer array and the copy the words point into *)
assert (HinA : In (arr, SlotSpec.arr_size L0) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app; right. apply in_or_app; right.
  unfold lt_wblocks. cbv zeta. right. right. left. reflexivity. }
assert (HinC : In (copy, L0 + 1) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app; right. apply in_or_app; right.
  unfold lt_wblocks. cbv zeta. right. left. reflexivity. }
(* 0x86a1c addi a0,sp,120; 0x86a20 jal check_words *)
destruct (kw_seed_loc (fx := fx) (PI := PI) W regs mem) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
assert (HAE : env_agree 32 (Ereg regs []) (Eimg (Ereg regs []))).
{ split; [intros n Hn0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
assert (E2 : ew (Eimg (Ereg regs [])) 2 = getr regs 2).
{ rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs [] 2 2%bv eq_refl). }
remember (Eimg (Ereg regs [])) as E eqn:HE. clear HE.
paj_run_tok RUN HS HJ0 SHOK kw_span.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
rename HJ0 into HJ.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. rewrite E2 in P10.
change 1268 with LO_K3 in P1.
assert (HKEEP : forall rr, In rr kw_kept -> getr (ms_regs ms) rr = getr regs rr).
{ intros rr Hrr. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W) ms) regs [] kw_kept HS HAE
    ltac:(vm_compute; reflexivity) rr Hrr). }
(* the run wrote no memory *)
assert (Hmem : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (rg & Hrg & _). destruct Hrg. }
rewrite Hmem in HJ |- *. clear HF HFr HG SHOK Hmem.
rewrite (SIGP CS_check_words ltac:(unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (cmd_af CS_check_words) with AF_check_words by (vm_compute; reflexivity).
set (regsc := ms_regs ms) in *.
(* the state at the call *)
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eshi & _).
assert (HFS : frames S = []) by (rewrite Hfrs, HFR0; reflexivity).
assert (K2 : getr regsc 2 = getr regs 2) by (apply HKEEP; kw_in).
assert (Hspc : spZ regsc = x_sp0 cx + -256).
{ unfold spZ at 1. rewrite K2. change (bv_unsigned (getr regs 2)) with (spZ regs). lia. }
assert (P10' : getr regsc 10 = w64 (x_sp1 cx + LT_W)).
{ rewrite P10. unfold w64, LT_W. f_equal. change (bv_unsigned (getr regs 2)) with (spZ regs). lia. }
assert (Hgpc : getr regsc 3 = w64 (as_gp B)) by (rewrite (HKEEP 3%bv ltac:(kw_in)), R3; exact Hgp0).
assert (Htpc : getr regsc 4 = w64 (as_tp B)) by (rewrite (HKEEP 4%bv ltac:(kw_in)), R4; exact Htp0).
pose proof pa_B_ok as HBOK. pose proof pa_base_lo as HBLO.
assert (Hrac : YK0s.ret_ok (getr regsc 1)) by (rewrite P1; apply ret_ok_codeptr_v; [unfold LO_K3; lia | reflexivity]).
assert (Hra4c : 4096 <= bv_unsigned (getr regsc 1)).
{ rewrite P1, unsigned_lit_small by (unfold LO_K3; lia). unfold LO_K3. lia. }
(* the frame chain at sp = entry sp - 256: s0 = -1 (0x865f0), achain's empty case *)
assert (Hchc : achain ly (rdW W mem) (x_sp0 cx + -256) (s0Z regsc) []).
{ assert (Es0 : s0Z regsc = 2 ^ 64 - 1).
  { unfold s0Z. rewrite (HKEEP 8%bv ltac:(kw_in)), R8. vm_compute. reflexivity. }
  left. split; [right; right; rewrite Es0; intros Hc; vm_compute in Hc; discriminate Hc | reflexivity]. }
assert (HSTK1 : CHECK_WORDS_STK - -256 <= LTOI_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HSTK0 : 0 <= CHECK_WORDS_STK) by (apply Z.leb_le; vm_compute; reflexivity).
(* check_words' pre-condition *)
pose proof (lt_arodata_kept B MT LAWS HB IMG cx ly S W mem mdv [] k HBASE HJ) as HRODc.
pose proof (lt_ro_kept B MT LAWS HB IMG cx ly S W mem mdv [] k HBASE HJ) as HROc.
assert (HWdlo : spZ regsc <= x_sp1 cx + LT_W + 16) by (rewrite Hspc; unfold LT_W; lia).
assert (HWdhi : x_sp1 cx + LT_W + 32 <= ly_stk_hi ly) by (rewrite Eshi; unfold LT_W; lia).
pose proof (lt_rdword_aval8_loc SEGS (w_H W) mem _ _ Warr) as HAarr.
pose proof (lt_rdword_rng SEGS (w_H W) mem _ _ Warr) as HRarr.
assert (Hws31 : Z.of_nat (length ws) < 2 ^ 31) by lia.
pose proof (al_blocks _ _ LAWS ly S W mem mdv arr (SlotSpec.arr_size L0) HARc HinA)
  as (Harr16 & _ & _ & _ & _ & Hpw & _).
assert (Hasz : 16 <= SlotSpec.arr_size L0) by (unfold SlotSpec.arr_size; pose proof (Z.div_pos L0 2); lia).
assert (HBLK : in_blockA (ablocks B ly S) arr (8 * Z.of_nat (length ws))).
{ exists arr, (SlotSpec.arr_size L0). split; [exact HinA | lia]. }
assert (Harr8 : arr mod 8 = 0).
{ pose proof (Z.div_mod arr 16 ltac:(lia)) as Hd. rewrite Harr16 in Hd.
  replace arr with ((2 * (arr / 16)) * 8) by lia. apply Z.mod_mul. lia. }
assert (HWK : forall k0, (k0 < length ws)%nat ->
  aval_mem (rdW W mem) (arr + 8 * Z.of_nat k0) 8 (nth k0 wp 0) /\ 0 <= nth k0 wp 0 < 2 ^ 64 /\
  in_blockA (ablocks B ly S) (nth k0 wp 0) (Z.of_nat (length (nth k0 ws [])) + 1) /\
  astr_atR (rdW W mem) (nth k0 wp 0) (nth k0 ws [])).
{ intros k0 Hk0.
  destruct (nth_error wp k0) as [pt|] eqn:Ep; [|apply nth_error_None in Ep; lia].
  destruct (nth_error ws k0) as [w0|] eqn:Ew; [|apply nth_error_None in Ew; lia].
  rewrite (nth_error_nth wp k0 0 Ep), (nth_error_nth ws k0 [] Ew).
  pose proof (Wslots k0 pt Ep) as Hrw. destruct (Wstr k0 pt w0 Ep Ew) as (Hc1 & Hc2 & Hs).
  split; [exact (lt_rdword_aval8_loc SEGS (w_H W) mem _ _ Hrw)|].
  split; [exact (lt_rdword_rng SEGS (w_H W) mem _ _ Hrw)|].
  split; [exists copy, (L0 + 1); split; [exact HinC | lia] | exact Hs]. }
assert (HJN : join_need ws + 1 < MALLOC_MAX) by (unfold MALLOC_MAX; lia).
assert (HC0 : count_cid 0 (frames S) < fs_frames 0) by (rewrite HFS; vm_compute; reflexivity).
assert (HC4 : count_cid 4 (frames S) < fs_frames 4) by (rewrite HFS; vm_compute; reflexivity).
(* the budget: check_words' two events and its meter come out of the rest *)
pose proof (EV_CHECK_ROUND_TRIP_ge0 R1 ws) as HRT0.
pose proof (ev_from_nonneg (31 - m) R1 (x_rest cx (lt_r' (x_pl cx) (x_n cx) r))) as HF0.
pose proof (lt_ws_join_need (x_pl cx) (x_n cx) r ltac:(lia)) as Hjn'.
destruct (kw_bud_loc B MT MTL cx ly S W mem mdv k acc ws _ _ HBASE HJ Hjn' HRT0 HF0 HBUD) as (HEVc & HMOc & HBUD3).
(* the live bytes: the recorder's blocks, the entry's, the three words blocks, and joined's at its peak *)
pose proof (kw_live_loc B MT LAWS cx ly S W mem mdv R1 O1 _ _ text copy arr HBASE HARc HREC HL0) as HLIVEc.
(* the call *)
assert (HCALL : afn_pre SEGS B CHECK_WORDS_STK ly S W regsc mem mdv [] ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_check_words) regsc mem mdv)
  (apost_baseF SEGS B CHECK_WORDS_STK [] regsc ly S W mem mdv EV_CHECK_WORDS
  (fun ly' S' W' regs' mem' md' =>
   Permutation (ablocks B ly' S') (ablocks B ly S) /\
   rec_repA B ly' S' (rdW W' mem') R1 O1 /\
   mo_le MT S S' (XM_CHECK_WORDS MT ws)))).
{ intros HPRE1.
  exact (HCHECK_WORDS fx ly S W regsc mem mdv [] (x_sp1 cx + LT_W) arr wp ws R1 O1 HPRE1 HFRM HRODc P10'
    HROc HOBJ HWdlo HWdhi Hwal HAarr HRarr Wn Wlen Hws31 HBLK Harr8 HWK HJN HREPA HWP HC0 HC4
    HEVc HLIVEc HMOc). }
eapply SRr_bind.
{ exact (cl_callSF (fx := fx) (L := cmd_listing) (PI := PI) B LAWS W regsc mem (Z_to_bv 64 (BASE + AF_check_words))
    LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S mdv k CHECK_WORDS_STK []
    EV_CHECK_WORDS (-256) (getr regsc 1) []
    (fun ly' S' W' regs' mem' md' =>
     Permutation (ablocks B ly' S') (ablocks B ly S) /\
     rec_repA B ly' S' (rdW W' mem') R1 O1 /\
     mo_le MT S S' (XM_CHECK_WORDS MT ws))
    HJ Hspc eq_refl ltac:(lia) HSTK0 HSTK1 Hgpc Htpc eq_refl Hrac Hra4c Hchc HCALL
    ltac:(intros a (rg & Hrg & _); destruct Hrg)). }
(* back at 0x86a24, at the FP state fx3 check_words returned: the post there is the post at fx (fxrel fx fx3) *)
cbv beta. intros W3 c3 _ (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hfx & -> & HJ3 & HJc3 & HP3 & HPERM3 & _ & HMLE3).
rewrite P1.
apply (srr_apost_baseF_lift (fx := fx) SEGS fx3); [exact Hfx|].
(* the cut's facts, carried past the call: the callee-saved registers, the frame, the live blocks and the statics *)
assert (HPc : aregs_preserved regs regsc) by (apply kw_pres_loc; exact HKEEP).
assert (Hsp1 : alloc_ceiling <= x_sp1 cx) by (rewrite Hx1; rewrite WL in Hslo0; lia).
assert (Hsp0 : x_sp0 cx <= 2 ^ 64) by (rewrite Hx0; lia).
destruct (lt_kcut_keep B cx ly S W regs mem md k ly3 S3 W3 regs3 mem3 md3 (k + EV_CHECK_WORDS) m r Rh R1 O1
  (if quit then 1 else 0) text copy arr wp HBODY HKR HWD HREC HJ3 (lt_pres_trans regs regsc regs3 HPc HP3) HPERM3
  (lt_call_kept B HB LAWS IMG cx CHECK_WORDS_STK ly S W mem mdv ly3 S3 W3 mem3 md3 EV_CHECK_WORDS HJc3 Hsp1 Hsp0
    HPERM3)) as (B3 & KR3 & WD3 & REC3).
exact (HK3' fx3 ly3 S3 W3 regs3 mem3 md3 (k + EV_CHECK_WORDS) (acc + XM_CHECK_WORDS MT ws)
  (fxrel_frm0 fx fx3 HFRM Hfx) B3 KR3 WD3 REC3 (HBUD3 S3 HMLE3)).
Qed.
End e.
End f.
End d.
