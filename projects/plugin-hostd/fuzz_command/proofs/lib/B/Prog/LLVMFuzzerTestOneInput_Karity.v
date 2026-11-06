(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the check_arity step of segment K of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86a14 addi a0,sp,120 and 0x86a18 jal check_arity, to the return point 0x86a1c): from the cut after check_reply to the cut after check_arity (lib/B/Prog/LLVMFuzzerTestOneInput_Kcut.v), through check_arity's statement; the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_Karity.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (cl_FC_okX: a symbolic run to a program call, the callee's contract, the next cut statement at the return point) and A/ACh2.v:122-290 (a program call through cl_callS and back). Proves no function (kind: segment lemma). *)
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
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo PaArt
  PaNoChain PaCallPg CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_clear_c send_message_c check_reply_c
  check_arity_c check_words_c check_refusal_c check_round_trip_c verbs_receive_c LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_Kcut LLVMFuzzerTestOneInput_Karity_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_reply_code_c HarnessPropsA.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the symbolic state at 0x86a14 (BASE + LO_K1): the registers as atoms, no region (the two instructions to the call
   read and write no memory), no fact; no shadow entry (no inline check) *)
Definition ka_ss : sstate := mkSS LO_K1 sr_atoms [] None (mkFacts [] [] []).
Definition KAx : sv := SOff 9 0.
Definition KAspan : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the environment of the run: the registers' values and the image's atoms *)
Definition ka_E (regs : bvmap 5 word) : env := Eimg (PI := PI) (Ereg regs []).
Lemma ka_E_env : forall regs, img_env VAL A_LIM (ka_E regs).
Proof. intros regs. unfold ka_E. apply Eimg_env. Qed.
Lemma ka_E_agree : forall regs, env_agree 32 (Ereg regs []) (ka_E regs).
Proof. intros regs. unfold ka_E. split; [intros i Hi; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.
Lemma ka_E_sp : forall regs, ew (ka_E regs) 2 = getr regs 2.
Proof. intros regs. unfold ka_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs [] 2 2%bv eq_refl). Qed.

(* the seed of the symbolic run at 0x86a14 *)
Lemma ka_seed_loc : forall (W : world SEGS) (regs : bvmap 5 word) mem,
  st_ok_pi SEGS VAL (ka_E regs) ka_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K1)) mem (seg_rom SEGS))) /\
  sh_ok SEGS KAx [] (ka_E regs) (mrestrict (w_H W) mem).
Proof.
intros W regs mem. split.
- unfold ka_ss, ka_E. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_nil.
  + exact I.
  + unfold facts_ok. cbn. tauto.
- apply Forall_nil.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the callee's statement, exactly LLVMFuzzerTestOneInput_c.v's Section hypothesis (every FP state) *)
Hypothesis HCHECK_ARITY : forall fx0 : YK11.FPState, @tcheck_arity_spec fx0 rc SK PI B MT.
(* the per-binary facts, with the names of a Theorem Labs lane's RULING-STMT.md section 1 *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.
Let RUN := paj_run B LAWS.

(* 0x86a14 addi a0,sp,120; 0x86a18 jal check_arity; check_arity's statement at the ambient FP state (its post is
   apost_base: the FP state is kept); then the cut at 0x86a1c, at the same FP state *)
Lemma lt_seg_K1 : lt_seg_K1_stmt B MT.
Proof.
intros m K2 cx ly S W regs mem md k acc r Rh O1 text copy arr wps HBASE HFRM HBODY HKR.
cbv zeta.
destruct (vr_runA (RecModel.rec_clear (lt_R0 (x_pl cx) (x_n cx) r Rh)) (lt_D (x_pl cx) (x_n cx) r))
  as [[R1 xr] quit] eqn:ERUN.
cbv beta iota.
intros HW HREC HBUD.
(* ---- the facts of the cut ---- *)
pose proof HBASE as (HPRE0 & HROD0 & HRO0 & HVO0 & H10 & H11 & HPN & HNL & HG8 & HFR0 & HGI & HEV0 & HLIVE0 & HMO0).
pose proof HPRE0 as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HBODY as (HFRAME & HSLOTS & R8 & R9 & R18 & R25 & R26 & R27 & Hm).
pose proof HFRAME as (HJ & Hsp & R3 & R4 & HSAVED).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & Hnev & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof HW as (WT & WC & WA & WN & WL & WP & WS).
pose proof HREC as (HRR & HSP & HCL & HQ & RQ & HPERM).
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
assert (Hsp0b : alloc_ceiling + 256 <= x_sp0 cx <= 2 ^ 47).
{ unfold x_sp0. clear - Hceil Hslo Hshi H47. unfold LTOI_STK, LLVMF_STK in Hslo. lia. }
(* the harness facts of the message: the arity conjunct (the cut file's lt_kregs_props) *)
pose proof (lt_kregs_props cx regs (rdW W mem) r Rh HKR) as HMP.
unfold msg_props_at in HMP. cbv zeta in HMP.
pose proof ERUN as ERUN'. unfold vr_runA in ERUN'. rewrite ERUN' in HMP. cbv beta iota in HMP.
destruct HMP as (_ & _ & _ & _ & _ & _ & HARITY & _).
pose proof (lt_ws_bounds (x_pl cx) (x_n cx) r) as WB. cbv zeta in WB. destruct WB as (WB0 & WB1 & WB2 & WB3 & WB4).
set (ws := lt_ws (x_pl cx) (x_n cx) r) in *.
set (L0 := StrFun.strnlen_res (Z.of_nat (length (lt_D (x_pl cx) (x_n cx) r))) (lt_D (x_pl cx) (x_n cx) r)) in *.
(* ---- check_arity's premises at the call (the two instructions write no memory) ---- *)
assert (HROD : arodata_okP SEGS RLO RHI B (rdW W mem)).
{ exact (arodata_ok_journalP SEGS CMD_RLO CMD_RHI (cif_relro_img _ _ IMG) (RO := cif_ro_below_ofl _ _ IMG)
    B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem md k
    HJ (fun a Hro Hin => cif_prog_not_ro _ _ IMG a Hin Hro) HROD0). }
assert (HRO : cmd_ro_ok (rdW W mem)) by exact (cmd_ro_ok_of_aro SEGS B LAWS HB IMG ly S W mem md HAR HROD).
pose proof (lt_w_align B MT cx HBASE) as Hal8.
assert (Hwp : 0 <= x_sp1 cx + LT_W < 2 ^ 64).
{ clear - Hsp0b AC1. unfold x_sp1, x_sp0, LT_FRAME, LT_W in *. lia. }
assert (Hhiw : x_sp1 cx + LT_W + WORDS_W + 12 <= ly_stk_hi ly).
{ rewrite Eshi. clear - Hshi. unfold x_sp1, x_sp0, LT_FRAME, LT_W, WORDS_W in *. lia. }
assert (WN' : aval_mem (rdW W mem) (x_sp1 cx + LT_W + WORDS_N) 4 (Z.of_nat (length ws))) by (unfold WORDS_N; exact WN).
assert (Ht : 0 <= Z.of_nat (length ws) <= 4096) by lia.
assert (WA' : aval_mem (rdW W mem) (x_sp1 cx + LT_W + WORDS_W) 8 arr)
  by (unfold WORDS_W; exact (lt_rdword_aval8_loc SEGS _ _ _ _ WA)).
assert (Hww : 0 <= arr < 2 ^ 64) by exact (lt_rdword_rng SEGS _ _ _ _ WA).
assert (HINW : forall b, In b (lt_wblocks (lt_D (x_pl cx) (x_n cx) r) text copy arr) -> In b (ablocks B ly S)).
{ intros b Hb. apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. right. apply in_or_app. right. exact Hb. }
assert (HINA : In (arr, SlotSpec.arr_size L0) (ablocks B ly S)).
{ apply HINW. unfold lt_wblocks. cbv zeta. right. right. left. reflexivity. }
assert (HINC : In (copy, L0 + 1) (ablocks B ly S)).
{ apply HINW. unfold lt_wblocks. cbv zeta. right. left. reflexivity. }
assert (H14 : 0 < Z.of_nat (length ws) ->
  in_blockA (ablocks B ly S) arr 8 /\ arr mod 8 = 0 /\ aval_mem (rdW W mem) arr 8 (nth 0 wps 0) /\
  0 <= nth 0 wps 0 < 2 ^ 64 /\ in_blockA (ablocks B ly S) (nth 0 wps 0) (Z.of_nat (length (nth 0 ws [])) + 1) /\
  astr_atR (rdW W mem) (nth 0 wps 0) (nth 0 ws [])).
{ intros Ht0.
  assert (Hp0 : nth_error wps 0 = Some (nth 0 wps 0)) by (apply nth_error_nth'; rewrite WL; lia).
  assert (Hw0 : nth_error ws 0 = Some (nth 0 ws [])) by (apply nth_error_nth'; lia).
  pose proof (WP 0%nat _ Hp0) as Hrd0. replace (arr + 8 * Z.of_nat 0) with arr in Hrd0 by lia.
  destruct (WS 0%nat _ _ Hp0 Hw0) as (S1 & S2 & S3).
  destruct (al_blocks _ _ LAWS ly S W mem md arr _ HAR HINA) as (Ha16 & _).
  split; [exists arr, (SlotSpec.arr_size L0); split; [exact HINA | lia]|].
  split.
  { pose proof (Z.div_mod arr 16 ltac:(lia)) as Hd. rewrite Ha16, Z.add_0_r in Hd. rewrite Hd.
    replace (16 * (arr / 16)) with ((2 * (arr / 16)) * 8) by ring. apply Z.mod_mul. lia. }
  split; [exact (lt_rdword_aval8_loc SEGS _ _ _ _ Hrd0)|].
  split; [exact (lt_rdword_rng SEGS _ _ _ _ Hrd0)|].
  split; [exists copy, (L0 + 1); split; [exact HINC | lia] | exact S3]. }
pose proof HRR as (QL & HAREP & HQO).
pose proof HAREP as (Hg8 & Hs8 & Hap & HC & HAn & HRe & HSc & HOwn).
pose proof HC as (C1c & C2c & C3c & C4c & C5c & C6c).
assert (Hnc : 0 <= Z.of_nat (length (r_calls R1)) <= 16) by lia.
assert (H17 : 0 < Z.of_nat (length (r_calls R1)) ->
  aval_mem (rdW W mem) (A_G_REC + OFF_CALLS + CALL_OFF_FN) 4 (fst (nth 0 (r_calls R1) (0, []))) /\
  0 <= fst (nth 0 (r_calls R1) (0, [])) < REC_FN_COUNT).
{ intros Hnc0.
  assert (Hc0 : nth_error (r_calls R1) 0 = Some (nth 0 (r_calls R1) (0, []))) by (apply nth_error_nth'; lia).
  assert (HP0 : nth_error (l_calls QL) 0 = Some (nth 0 (l_calls QL) [])) by (apply nth_error_nth'; rewrite C2c; lia).
  destruct (C4c 0%nat _ _ Hc0 HP0) as ((A1 & A2 & A3 & A4 & _) & _).
  split; [|exact A1].
  replace (A_G_REC + OFF_CALLS + CALL_OFF_FN) with (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat 0 + CALL_OFF_FN)
    by (cbn [Z.of_nat]; ring).
  exact A4. }
assert (HEVc : st_nev S + EV_CHECK_ARITY <= EV_MAX).
{ pose proof (lt_nev_now B MT cx ly S W mem md k acc _ HBASE HJ HBUD) as H1. unfold EV_CHECK_ARITY. lia. }
(* ---- 0x86a14 .. 0x86a18: a0 := sp + 120, then the call ---- *)
pose proof (ka_E_env regs) as HEI.
pose proof (ka_E_agree regs) as HAE.
destruct (ka_seed_loc W regs mem) as [HS SHOK].
paj_run_tok RUN HS HJ SHOK KAspan.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
assert (EM : ms_mem ms = mem).
{ apply functional_extensionality. intros x. apply HF. intros (r0 & Hr0 & _). unfold ka_ss in Hr0. cbn [ss_mem In] in Hr0.
  exact Hr0. }
pmkst HS.
prreg HS (1%bv : bv 5) P1.
prreg HS (10%bv : bv 5) P10.
assert (HPR : aregs_preserved regs (ms_regs ms)).
{ eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [] HS); [exact HAE | vm_compute; reflexivity]. }
rewrite (SIGP CS_check_arity ltac:(unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (cmd_af CS_check_arity) with AF_check_arity by (vm_compute; reflexivity).
rewrite EM in HJ |- *.
assert (E2c : getr (ms_regs ms) 2 = getr regs 2) by exact (HPR 2 ltac:(unfold acallee_saved; lia)).
assert (Hspc : spZ (ms_regs ms) = x_sp0 cx + -256).
{ unfold spZ at 1. rewrite E2c. change (bv_unsigned (getr regs 2)) with (spZ regs). rewrite Hsp.
  unfold x_sp1, x_sp0, LT_FRAME. lia. }
assert (Hspw : spZ (ms_regs ms) <= x_sp1 cx + LT_W) by (rewrite Hspc; unfold x_sp1, x_sp0, LT_FRAME, LT_W; lia).
assert (P3c : getr (ms_regs ms) 3 = w64 (as_gp B))
  by exact (eq_trans (HPR 3 ltac:(unfold acallee_saved; lia)) (eq_trans R3 Hgp0)).
assert (P4c : getr (ms_regs ms) 4 = w64 (as_tp B))
  by exact (eq_trans (HPR 4 ltac:(unfold acallee_saved; lia)) (eq_trans R4 Htp0)).
pose proof pa_B_ok as HBASEok. pose proof pa_base_lo as HBLO.
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (Hra4T : 4096 <= bv_unsigned (getr (ms_regs ms) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
assert (P10c : getr (ms_regs ms) 10 = w64 (x_sp1 cx + LT_W)).
{ rewrite P10. unfold w64, LT_W. f_equal. rewrite (ka_E_sp regs).
  change (bv_unsigned (getr regs 2)) with (spZ regs). rewrite Hsp. reflexivity. }
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS W (ms_regs ms) mem _ LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [] ly S mdv k CHECK_ARITY_STK [] EV_CHECK_ARITY (-256) (getr (ms_regs ms) 1)
    (fun ly2 S2 W2 regs2 mem2 md2 => Permutation (ablocks B ly2 S2) (ablocks B ly S) /\ ly2 = ly /\ S2 = S)
    HJ Hspc); [reflexivity | lia | unfold CHECK_ARITY_STK, ESTACK; lia
    | unfold CHECK_ARITY_STK, ESTACK, LTOI_STK, LLVMF_STK; lia | exact P3c | exact P4c | reflexivity | exact HraT
    | exact Hra4T | | ].
  - intros HPRE1. eapply SRr_mono.
    + exact (HCHECK_ARITY fx ly S W (ms_regs ms) mem mdv (x_sp1 cx + LT_W) (Z.of_nat (length ws)) arr (nth 0 wps 0)
        (if quit then 1 else 0) (Z.of_nat (length (r_calls R1))) (fst (nth 0 (r_calls R1) (0, []))) (nth 0 ws [])
        HPRE1 HROD HRO HVO0 P10c Hwp Hal8 Hspw Hhiw WN' Ht WA' Hww H14 HQ RQ C3c Hnc H17 HARITY HEVc).
    + cbv beta. unfold apost_base. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & Ec & HJ3 & HP3 & HQ3).
      exists ly3, S3, regs3, mem3, md3. split; [exact Ec|]. split; [exact HJ3|]. split; [exact HP3 | exact HQ3].
  - intros a (r0 & Hr0 & _). destruct Hr0. }
(* ---- back at 0x86a1c: the cut after check_arity ---- *)
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & Ec & HJ3 & HJc3 & HP3 & HPerm3 & Ely & ESS).
subst c3 ly3 S3.
assert (HPALL : aregs_preserved regs regs3) by exact (lt_pres_trans _ _ _ HPR HP3).
pose proof (lt_call_kept B HB LAWS IMG cx CHECK_ARITY_STK ly S W mem mdv ly S W3 mem3 md3 EV_CHECK_ARITY HJc3
  ltac:(unfold x_sp1, x_sp0, LT_FRAME in *; lia) ltac:(lia) (Permutation_refl _)) as KEEP.
destruct (lt_kcut_keep B cx ly S W regs mem md k ly S W3 regs3 mem3 md3 (k + EV_CHECK_ARITY) m r Rh R1 O1
  (if quit then 1 else 0) text copy arr wps HBODY HKR HW HREC HJ3 HPALL (Permutation_refl _) KEEP)
  as (HBODY3 & HKR3 & HW3 & HREC3).
assert (HBUD3 : lt_bud MT cx S (k + EV_CHECK_ARITY) acc (3 + EV_CHECK_WORDS + EV_CHECK_REFUSAL +
  EV_CHECK_ROUND_TRIP R1 ws + ev_from (31 - m) R1 (x_rest cx (lt_r' (x_pl cx) (x_n cx) r)))).
{ apply (lt_bud_eq MT cx S k acc _ _ _ HBUD); unfold EV_CHECK_ARITY; ring. }
pose proof (K2 fx cx ly S W3 regs3 mem3 md3 (k + EV_CHECK_ARITY) acc r Rh O1 text copy arr wps HBASE HFRM HBODY3 HKR3)
  as K2'.
cbv zeta in K2'. rewrite ERUN in K2'. cbv beta iota in K2'.
rewrite P1.
exact (K2' HW3 HREC3 HBUD3).
Qed.
End e.
End f.
End d.
