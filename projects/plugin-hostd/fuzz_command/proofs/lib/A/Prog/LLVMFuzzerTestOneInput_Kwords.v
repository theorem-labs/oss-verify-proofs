(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the check_words step of segment K of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x86950 addi a0,sp,120 and 0x86954 jal check_words, to the return point 0x86958): lt_seg_K2, from the cut after check_arity (LT_K2_stmt) through the call to the cut after check_words (LT_K3_stmt, taken at every FP state: LTA_K3), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v cl_FC_okX (a symbolic run to the call, then the next statement) and A/ACh2.v:122-290 (a program call through cl_callS and back), and of check_refusal.v's call step. Statement passes 4, 5 and 5b: check_words returns at an FP state of its own (apost_baseF), so the call goes through PaFx.v's cl_callSF, the next cut is applied at that FP state (rounding mode 0 by fxrel_frm0) and its post lifted back by srr_apost_baseF_lift; its frame chain at s0 = 32 is achain_low; its astack_pres premise (pass 5b) is lt_base's, kept by the journal. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB PaCallPg PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
CmdGlob CmdBase CmdRep CmdObj CmdRo CmdRecBase CmdRecRo CmdRecImg sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import joined_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import joined_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c HarnessPropsA LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_Kcut
LLVMFuzzerTestOneInput_Kwords_s1.
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
(* the callee's statement, with the name LLVMFuzzerTestOneInput_c.v gives it (at every FP state) *)
Hypothesis HCHECK_WORDS : forall fx0 : YK11.FPState, @tcheck_words_spec fx0 rc SK PI B MT.
(* the walk hypotheses, with cgif's names *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis MTL : ameter_laws MT.
Hypothesis IMG : cmd_img_facts SEGS B.
Let RUN := paj_run B LAWS.

(* the registers the run to the call and the call keep: sp, gp, tp and the callee-saved s0 .. s11 *)
Definition kw_kept : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma kw_kept_saved_loc : forall rr, In rr kw_kept -> acallee_saved (bv_unsigned rr).
Proof.
intros rr Hrr.
assert (H : forallb (fun r : bv 5 => (bv_unsigned r =? 2) || (bv_unsigned r =? 3) || (bv_unsigned r =? 4) ||
  (bv_unsigned r =? 8) || (bv_unsigned r =? 9) || ((18 <=? bv_unsigned r) && (bv_unsigned r <=? 27))) kw_kept = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) H rr Hrr) as Hb. cbv beta in Hb. unfold acallee_saved.
repeat (apply orb_true_iff in Hb as [Hb|Hb];
  [|first [apply Z.eqb_eq in Hb; lia | apply andb_true_iff in Hb as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2; lia]]).
apply Z.eqb_eq in Hb. lia.
Qed.
Ltac kw_in := unfold kw_kept; cbn [In]; repeat (first [left; reflexivity | right]).

Lemma lt_seg_K2 : lt_seg_K2_stmt B MT.
Proof.
unfold lt_seg_K2_stmt. intros m HK3. unfold LT_K2_stmt.
intros cx ly S W regs mem md k acc r Rh O1 text copy arr wp HBASE HFRM HBODY HKR.
cbv zeta.
destruct (vr_runA (RecModel.rec_clear (lt_R0 (x_pl cx) (x_n cx) r Rh)) (lt_D (x_pl cx) (x_n cx) r))
  as [[R1 xr] quit] eqn:EVR.
intros HWD HREC HBUD.
(* the next cut at the run's result, at an FP state with rounding mode 0 (check_words returns at one of its own) *)
assert (HK3' : forall (fx1 : YK11.FPState) ly' S' W' regs' mem' md' k' acc',
  Z.land (Z.shiftr (bv_unsigned (@fp_csr fx1)) 5) 7 = 0 ->
  lt_body B cx ly' S' W' regs' mem' md' k' m -> lt_kregs cx regs' (rdW W' mem') m r Rh ->
  lt_words cx regs' (rdW W' mem') (lt_D (x_pl cx) (x_n cx) r) (lt_ws (x_pl cx) (x_n cx) r) text copy arr wp ->
  lt_rec B cx ly' S' W' mem' R1 O1 (if quit then 1 else 0) (lt_wblocks (lt_D (x_pl cx) (x_n cx) r) text copy arr) ->
  lt_bud MT cx S' k' acc' (3 + EV_CHECK_REFUSAL + EV_CHECK_ROUND_TRIP R1 (lt_ws (x_pl cx) (x_n cx) r) +
    ev_from (31 - m) R1 (x_rest cx (lt_r' (x_pl cx) (x_n cx) r))) ->
  SRr SEGS W' (mkCfg (@mkst fx1 regs' (Z_to_bv 64 (BASE + LO_K3)) mem' (seg_rom SEGS)) md')
    (lt_post (fx := fx1) B MT cx)).
{ intros fx1 ly' S' W' regs' mem' md' k' acc' H0 H1 H2 H3 H4 H5.
  pose proof (HK3 fx1 cx ly' S' W' regs' mem' md' k' acc' r Rh O1 text copy arr wp HBASE H0 H1 H2) as HK.
  cbv zeta in HK. rewrite EVR in HK. exact (HK H3 H4 H5). }
clear HK3.
(* the harness facts: the words the recorder's calls carry (lt_msg_props_rd, conjunct 8) *)
pose proof HKR as (Hr & R19 & R20 & R26 & R27 & Hhost & Hstate).
assert (HWP : words_prop_at atoi_a R1 (lt_ws (x_pl cx) (x_n cx) r)).
{ pose proof (lt_msg_props_rd SEGS (w_H W) mem _ _ (x_pl cx) (x_n cx) r Rh Hhost Hstate) as HMSG.
  unfold msg_props_at in HMSG. cbv zeta in HMSG. unfold vr_runA in EVR. rewrite EVR in HMSG.
  destruct HMSG as (_ & _ & _ & _ & _ & _ & _ & HW & _). exact HW. }
pose proof (lt_ws_bounds (x_pl cx) (x_n cx) r) as Hbnd. cbv zeta in Hbnd.
destruct Hbnd as (HL0 & H2ws & Hws4 & H8ws & Hjn).
pose proof (lt_w_align B MT cx HBASE) as Hwal.
(* the entry's facts *)
pose proof HBASE as (HPRE0 & HROD0 & _ & HOBJ & _ & _ & _ & _ & _ & HFR0 & _ & HEV0 & HLIVE0 & HMO0 & HSTKP0).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & Hstk0 & _ & _ & _).
pose proof Hstk0 as (_ & _ & Hceil0 & Hslo0 & Hshi0 & H470 & _ & _ & _).
assert (Hx0 : x_sp0 cx = spZ (x_regs cx)) by reflexivity.
assert (Hx1 : x_sp1 cx = spZ (x_regs cx) - 256) by reflexivity.
assert (WL : LTOI_STK = 32768) by reflexivity.
pose proof asan_consts as (C1 & _).
(* the point's facts *)
pose proof HBODY as (HFR & HSLOT & R8 & R9 & R18 & R22 & Hm & Hn & Hpn).
pose proof HFR as (HJ0 & Hsp & R3 & R4 & HSAVED).
pose proof HWD as (R24 & R23 & R25 & Wtext & Wcopy & Warr & Wn & Wlen & Wslots & Wstr).
pose proof HREC as (HREPA & Hspill & Hcalls & Hq & Hqr & HPERM).
pose proof HBUD as (Hk & Hrem & Hkrem & Hmle & Hacc & HaccU).
set (ws := lt_ws (x_pl cx) (x_n cx) r) in *.
set (L0 := StrFun.strnlen_res (Z.of_nat (length (lt_D (x_pl cx) (x_n cx) r))) (lt_D (x_pl cx) (x_n cx) r)) in *.
(* the three words blocks are live *)
assert (HinA : In (arr, SlotSpec.arr_size L0) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app; right. apply in_or_app; right.
  unfold lt_wblocks. cbv zeta. right. right. left. reflexivity. }
assert (HinC : In (copy, L0 + 1) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app; right. apply in_or_app; right.
  unfold lt_wblocks. cbv zeta. right. left. reflexivity. }
(* 0x86950 addi a0,sp,120; 0x86954 jal check_words *)
destruct (kw_seed_loc W regs mem) as [HS SHOK].
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
change 1140 with LO_K3 in P1.
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
pose proof HJ as (HARc & Hly & _ & _ & _ & Hfrs & Hnev & _).
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
assert (Hchc : achain ly (rdW W mem) (x_sp0 cx + -256) (s0Z regsc) []).
{ apply achain_low. unfold s0Z. rewrite (HKEEP 8%bv ltac:(kw_in)), R8. unfold w64.
  rewrite unsigned_lit_small by lia. lia. }
assert (HSTK1 : CHECK_WORDS_STK - -256 <= LTOI_STK) by (vm_compute; intros Habs; discriminate Habs).
assert (HSTK0 : 0 <= CHECK_WORDS_STK) by (vm_compute; intros Habs; discriminate Habs).
(* check_words' pre-condition; the stack above the call's sp is present (pass 5b): lt_base's astack_pres at the
   entry sp, kept by the journal (its footprint cmd_PG lies below the stack) and narrowed to the call's sp *)
assert (HPRESc : astack_pres ly (w_H W) mem (spZ regsc)).
{ apply (astack_pres_mono ly (w_H W) mem (x_sp0 cx - LTOI_STK)); [rewrite Hspc, WL; lia|].
  apply (astack_pres_journal SEGS B pa_segs_low LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx)
    (x_mem cx) (x_md cx) [] ly S W mem mdv k HJ HSTKP0).
  intros a Ha Hr0. exfalso. pose proof (kw_PG_range_loc a Ha) as Hpg. unfold A_G_REC, A_G_QUITTING in Hpg. lia. }
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW W mem)).
{ apply (@arodata_ok_journalP _ _ SEGS CMD_RLO CMD_RHI (cif_relro_img _ _ IMG) (cif_ro_below_ofl _ _ IMG) B
    LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem mdv k HJ).
  - intros a Hro Hfp. exact (cif_prog_not_ro _ _ IMG a Hfp Hro).
  - exact HROD0. }
pose proof (cmd_ro_ok_of_aro SEGS B LAWS HB IMG ly S W mem mdv HARc HRODc) as HROc.
assert (HWdlo : spZ regsc <= x_sp1 cx + LT_W + 16) by (rewrite Hspc; unfold LT_W; lia).
assert (HWdhi : x_sp1 cx + LT_W + 32 <= ly_stk_hi ly) by (rewrite Eshi; unfold LT_W; lia).
pose proof (aval_of_rdword_loc SEGS (w_H W) mem _ _ Warr) as HAarr.
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
  split; [exact (aval_of_rdword_loc SEGS (w_H W) mem _ _ Hrw)|].
  split; [exact (lt_rdword_rng SEGS (w_H W) mem _ _ Hrw)|].
  split; [exists copy, (L0 + 1); split; [exact HinC | lia] | exact Hs]. }
assert (HJN : join_need ws + 1 < MALLOC_MAX) by (unfold MALLOC_MAX; lia).
assert (HC0 : count_cid 0 (frames S) < fs_frames 0) by (rewrite HFS; vm_compute; reflexivity).
assert (HC4 : count_cid 4 (frames S) < fs_frames 4) by (rewrite HFS; vm_compute; reflexivity).
(* the budget: check_words' two events and its meter come out of the rest *)
assert (EVW : EV_CHECK_WORDS = 2) by reflexivity.
assert (EVF : EV_CHECK_REFUSAL = 0) by reflexivity.
pose proof (kw_rest_nonneg_loc R1 ws (31 - m) (x_rest cx (lt_r' (x_pl cx) (x_n cx) r))) as HAF.
pose proof (kw_xm_le_loc MT MTL ws Hjn) as HXW.
pose proof (mo_free_nonneg MT MTL) as HF0.
pose proof (mo_malloc_nonneg MT MTL 32784 ltac:(lia)) as HM0.
rewrite EVW, EVF in *.
set (A := EV_CHECK_ROUND_TRIP R1 ws) in *.
set (F := ev_from (31 - m) R1 (x_rest cx (lt_r' (x_pl cx) (x_n cx) r))) in *.
set (U := LT_U MT) in *.
set (XW := XM_CHECK_WORDS MT ws) in *.
assert (HU0 : 0 <= U) by (unfold U, LT_U; lia).
assert (HEVc : st_nev S + 2 <= EV_MAX) by lia.
assert (HremU : U <= (3 + 2 + 0 + A + F) * U) by nia.
assert (HMOc : mo_ok MT S XW).
{ apply (mok_station MT (x_S cx) S (XM_LTOI MT (x_pl cx)) acc XW MTL HMO0 Hmle); lia. }
(* the live bytes: the recorder's blocks, the entry's and the three words blocks, and joined's at its peak *)
assert (HND : List.NoDup (ablocks B ly S)).
{ apply nodup_blocks_loc.
  - apply Forall_forall. intros [p n0] Hin.
    destruct (al_blocks _ _ LAWS ly S W mem mdv p n0 HARc Hin) as (_ & _ & _ & _ & _ & _ & Hn0). cbn [snd]. lia.
  - destruct (al_sep _ _ LAWS ly S W mem mdv HARc) as [Hp _]. apply pairwise_app_l in Hp as [Hp _]. exact Hp. }
assert (HNDO : List.NoDup O1) by exact (NoDup_app_remove_r _ _ (Permutation_NoDup HPERM HND)).
pose proof (lt_rec_bsum_loc B ly S (rdW W mem) R1 O1 HREPA HNDO Hcalls Hspill) as HbO.
assert (HBBS : blocks_bytes S = bsum O1 + blocks_bytes (x_S cx) + bsum (lt_wblocks (lt_D (x_pl cx) (x_n cx) r) text copy arr)).
{ rewrite (blocks_bytes_ablocks B ly S), (bsum_perm _ _ HPERM), !bsum_app.
  unfold x_bl0. rewrite <- (blocks_bytes_ablocks B (x_ly cx) (x_S cx)). ring. }
pose proof (kw_wblocks_bsum_loc (lt_D (x_pl cx) (x_n cx) r) text copy arr HL0) as Hwbl.
assert (HLIVEc : blocks_bytes S + LIVE_CHECK_WORDS <= LIVE_MAX).
{ pose proof (Z.le_max_l LIVE_CHECK_WORDS LIVE_CHECK_ROUND_TRIP) as Hx1'.
  pose proof (Z.le_max_r LIVE_SEND_MESSAGE (Z.max LIVE_CHECK_WORDS LIVE_CHECK_ROUND_TRIP)) as Hx2'.
  unfold LIVE_LTOI in HLIVE0. unfold LT_RECB in HbO. unfold LT_WORDSB in Hwbl.
  revert HBBS HbO Hwbl HLIVE0 Hx1' Hx2'.
  generalize (Z.max LIVE_SEND_MESSAGE (Z.max LIVE_CHECK_WORDS LIVE_CHECK_ROUND_TRIP)).
  generalize (Z.max LIVE_CHECK_WORDS LIVE_CHECK_ROUND_TRIP). intros. lia. }
(* the call *)
assert (HCALL : afn_pre SEGS B CHECK_WORDS_STK ly S W regsc mem mdv [] ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_check_words) regsc mem mdv)
  (apost_baseF SEGS B CHECK_WORDS_STK [] regsc ly S W mem mdv EV_CHECK_WORDS
  (fun ly' S' W' regs' mem' md' =>
   Permutation (ablocks B ly' S') (ablocks B ly S) /\
   rec_repA B ly' S' (rdW W' mem') R1 O1 /\
   blocks_bytes S' <= blocks_bytes S + LIVE_CHECK_WORDS /\
   mo_le MT S S' (XM_CHECK_WORDS MT ws)))).
{ intros HPRE1.
  exact (HCHECK_WORDS fx ly S W regsc mem mdv [] (x_sp1 cx + LT_W) arr wp ws R1 O1 HPRE1 HPRESc HFRM HRODc P10'
    HROc HOBJ HWdlo HWdhi Hwal HAarr HRarr Wn Wlen Hws31 HBLK Harr8 HWK HJN HREPA HWP HC0 HC4
    ltac:(rewrite EVW; exact HEVc) HLIVEc HMOc). }
eapply SRr_bind.
{ exact (cl_callSF B LAWS W regsc mem (Z_to_bv 64 (BASE + AF_check_words)) LTOI_STK (x_sp0 cx) cmd_PG
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S mdv k CHECK_WORDS_STK [] EV_CHECK_WORDS (-256)
    (getr regsc 1) []
    (fun ly' S' W' regs' mem' md' =>
     Permutation (ablocks B ly' S') (ablocks B ly S) /\
     rec_repA B ly' S' (rdW W' mem') R1 O1 /\
     blocks_bytes S' <= blocks_bytes S + LIVE_CHECK_WORDS /\
     mo_le MT S S' (XM_CHECK_WORDS MT ws))
    HJ Hspc eq_refl ltac:(lia) HSTK0 HSTK1 Hgpc Htpc eq_refl Hrac Hra4c Hchc HCALL
    ltac:(intros a (rg & Hrg & _); destruct Hrg)). }
(* back at 0x86958, at the FP state fx3 check_words returned: the post there is the post at fx (fxrel fx fx3) *)
cbv beta. intros W3 c3 _ (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hfx & -> & HJ3 & HJc3 & HP3 & HPERM3 & HREP3 & _ & HMLE3).
rewrite P1.
apply (srr_apost_baseF_lift (fx := fx) SEGS fx3); [exact Hfx|].
(* the callee's journal keeps the frame words, the words blocks and g_quitting *)
pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _).
assert (KS : forall a, x_sp1 cx <= a < 2 ^ 64 -> rdW W3 mem3 a = rdW W mem a).
{ intros a Ha. apply G1; [lia | lia | intros (rg & Hrg & _); destruct Hrg]. }
assert (KB : forall p n0 i, In (p, n0) (ablocks B ly S) -> 0 <= i < req_size n0 ->
  rdW W3 mem3 (p + i) = rdW W mem (p + i)).
{ intros p n0 i Hin Hi. apply (G2 p n0 i); [exact Hin | exact (Permutation_in _ (Permutation_sym HPERM3) Hin) | exact Hi |].
  intros (rg & Hrg & _). destruct Hrg. }
assert (KQ : forall a, A_G_QUITTING <= a < A_G_QUITTING + 4 -> rdW W3 mem3 a = rdW W mem a).
{ intros a Ha.
  assert (Hpg : inFP cmd_PG a) by (exists (A_G_QUITTING, A_G_QUITTING + 4); split; [right; right; left; reflexivity | cbn [fst snd]; lia]).
  destruct (cmd_prog_unowned SEGS B LAWS HB IMG a Hpg) as (Hi & Ho & He).
  apply G3; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [exact sink_closed_nil | intros (rg & Hrg & _); destruct Hrg]]. }
assert (KR : forall rr, In rr kw_kept -> getr regs3 rr = getr regs rr).
{ intros rr Hrr. rewrite (aregs_pres_at_loc regsc regs3 rr HP3 (kw_kept_saved_loc rr Hrr)). exact (HKEEP rr Hrr). }
assert (KW : forall a, x_sp1 cx <= a -> a + 8 <= 2 ^ 64 -> rdword (rdW W3 mem3) a = rdword (rdW W mem) a).
{ intros a Ha1 Ha2. apply rdword_ext. intros k0 Hk0. apply KS. lia. }
apply (HK3' fx3 ly3 S3 W3 regs3 mem3 md3 (k + EV_CHECK_WORDS) (acc + XW) (fxrel_frm0 fx fx3 HFRM Hfx)).
- (* lt_body *)
  split; [|split; [|split; [|split; [|split; [|split; [|split; [exact Hm | split; [exact Hn | exact Hpn]]]]]]]].
  + split; [exact HJ3|]. split.
    { unfold spZ. rewrite (KR 2%bv ltac:(kw_in)). exact Hsp. }
    split; [rewrite (KR 3%bv ltac:(kw_in)); exact R3|]. split; [rewrite (KR 4%bv ltac:(kw_in)); exact R4|].
    intros i r0 Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    cbn [length LT_SAVED] in Hi13. rewrite KW by (rewrite ?Nat2Z.inj_succ; lia). exact (HSAVED i r0 Hi).
  + intros o v Hov.
    assert (HSL : forallb (fun ov => (0 <=? fst ov) && (fst ov <=? 80)) LT_SLOTS = true) by (vm_compute; reflexivity).
    pose proof (proj1 (forallb_forall _ LT_SLOTS) HSL (o, v) Hov) as Hb. cbn [fst] in Hb.
    apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
    rewrite KW by lia. exact (HSLOT o v Hov).
  + rewrite (KR 8%bv ltac:(kw_in)). exact R8.
  + rewrite (KR 9%bv ltac:(kw_in)). exact R9.
  + rewrite (KR 18%bv ltac:(kw_in)). exact R18.
  + rewrite (KR 22%bv ltac:(kw_in)). exact R22.
- (* lt_kregs *)
  split; [exact Hr|].
  split; [rewrite (KR 19%bv ltac:(kw_in)); exact R19|]. split; [rewrite (KR 20%bv ltac:(kw_in)); exact R20|].
  split; [rewrite (KR 26%bv ltac:(kw_in)); exact R26|]. split; [rewrite (KR 27%bv ltac:(kw_in)); exact R27|].
  split; rewrite KW by (unfold LT_HOSTB, LT_STATEB; lia); assumption.
- (* lt_words *)
  split; [rewrite (KR 24%bv ltac:(kw_in)); exact R24|]. split; [rewrite (KR 23%bv ltac:(kw_in)); exact R23|].
  split; [rewrite (KR 25%bv ltac:(kw_in)); exact R25|].
  split; [rewrite KW by (unfold LT_W; lia); exact Wtext|].
  split; [rewrite KW by (unfold LT_W; lia); exact Wcopy|].
  split; [rewrite KW by (unfold LT_W; lia); exact Warr|].
  split; [intros k0 Hk0; rewrite KS by (unfold LT_W; lia); exact (Wn k0 Hk0)|].
  split; [exact Wlen|]. split.
  + intros i pt Hpt. assert (Hi : (i < length ws)%nat) by (rewrite <- Wlen; apply nth_error_Some; rewrite Hpt; discriminate).
    pose proof (req_size_pos (SlotSpec.arr_size L0) ltac:(lia)) as [_ Hreq].
    rewrite (rdword_ext (rdW W mem) (rdW W3 mem3)); [exact (Wslots i pt Hpt)|].
    intros k0 Hk0. replace (arr + 8 * Z.of_nat i + k0) with (arr + (8 * Z.of_nat i + k0)) by ring.
    apply (KB arr (SlotSpec.arr_size L0)); [exact HinA | lia].
  + intros i pt w0 Hpt Hw. destruct (Wstr i pt w0 Hpt Hw) as (Hc1 & Hc2 & Hs).
    split; [exact Hc1|]. split; [exact Hc2|].
    pose proof (req_size_pos (L0 + 1) ltac:(lia)) as [_ Hreq].
    apply (astr_atR_kept_r (rdW W mem)); [|exact Hs].
    intros x Hx. replace x with (copy + (x - copy)) by ring. apply (KB copy (L0 + 1)); [exact HinC | lia].
- (* lt_rec *)
  split; [exact HREP3|]. split; [exact Hspill|]. split; [exact Hcalls|].
  split; [intros k0 Hk0; rewrite KQ by lia; exact (Hq k0 Hk0)|].
  split; [exact Hqr|]. exact (perm_trans HPERM3 HPERM).
- (* lt_bud: check_words' two events and its meter move from the rest into k and acc *)
  split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact (mle_station MT (x_S cx) S S3 acc XW MTL Hmle HMLE3)|].
  split; [lia|]. nia.
Qed.
End e.
End f.
End d.
