(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the segment of sup_instance_verb's ASan walk (plugin-hostd/fuzz_command) from the
   return of arg_line (0x8b468) through arg_i's call to its return (0x8b474), after
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (a segment that ends in a call, cl_callS, and passes on to the next) and the
   arg_i call of the sibling walk lib/A/Prog/sup_instance_info.v. *)
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

(* the layout once the slot's argument list grows by one block, on either arm of record() *)
Lemma sivL_slot_lay_snoc : forall Q0 R P pk,
Permutation (lay_blocks (slot_lay Q0 R (P ++ [pk]))) (lay_blocks (slot_lay Q0 R P) ++ [pk]).
Proof.
intros Q0 R P pk. unfold slot_lay. destruct (Nat.ltb (length (r_calls R)) 16);
[apply siv_lay_perm_lt | apply siv_lay_perm_full].
Qed.

(* the slot's nargs: the number of arguments the recorded call holds *)
Lemma sivL_nargs_of : forall bl rd R fn A Q0 P,
arep_at bl rd A_G_REC A_REC_SPILL (rec_record R fn A) (slot_lay Q0 R P) ->
aval_mem rd (siv_slot R + CALL_OFF_NARGS) 4 (Z.of_nat (length A)).
Proof.
intros bl rd R fn A Q0 P HR.
unfold siv_slot, slot_lay, rec_record in *.
destruct (Nat.ltb (length (r_calls R)) 16) eqn:E.
- destruct HR as (_ & _ & _ & (_ & C2 & _ & C4 & _) & _).
  cbn [set_calls r_calls l_calls] in C2, C4.
  rewrite !length_app in C2. cbn [length] in C2.
  assert (Hc : nth_error (r_calls R ++ [(fn, A)]) (length (r_calls R)) = Some (fn, A))
    by (rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity).
  assert (Hp : nth_error (l_calls Q0 ++ [P]) (length (r_calls R)) = Some P).
  { rewrite nth_error_app2 by lia. replace (length (r_calls R) - length (l_calls Q0))%nat with 0%nat by lia. reflexivity. }
  destruct (C4 _ _ _ Hc Hp) as ((_ & _ & _ & _ & H5 & _) & _). exact H5.
- destruct HR as (_ & _ & _ & (_ & _ & _ & _ & C5 & _) & _).
  cbn [set_spill r_spill l_spill] in C5.
  destruct C5 as (_ & _ & _ & _ & H5 & _). exact H5.
Qed.

(* the slot is an entry of g_rec's table or record.spill, in arg_i's form *)
Lemma sivL_slot_form : forall R,
(exists i, 0 <= i < REC_CALLS_MAX /\ siv_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ siv_slot R = A_REC_SPILL.
Proof.
intros R. unfold siv_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hl|Hl].
- left. exists (Z.of_nat (length (r_calls R))). unfold REC_CALLS_MAX. split; [lia | reflexivity].
- right. reflexivity.
Qed.

(* the footprint arg_i writes when the call holds m < 6 arguments: nargs and args[m] *)
Lemma sivL_fp : forall c m a, 0 <= m < REC_ARGS_MAX ->
inFP (if m <? REC_ARGS_MAX
      then [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * m, c + CALL_OFF_ARGS + 8 * m + 8)]
      else []) a ->
c + 4 <= a < c + 8 \/ c + 8 + 8 * m <= a < c + 16 + 8 * m.
Proof.
intros c m a Hm Ha. replace (m <? REC_ARGS_MAX) with true in Ha by (symmetry; apply Z.ltb_lt; lia).
destruct Ha as (r & Hr & Hra). destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra;
unfold CALL_OFF_NARGS, CALL_OFF_ARGS in Hra; lia.
Qed.

Lemma sivL_fp_closed : forall c m, 0 < c -> 0 <= m ->
~ YI16.sink_open_fp (if m <? REC_ARGS_MAX
      then [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * m, c + CALL_OFF_ARGS + 8 * m + 8)]
      else []).
Proof.
intros c m Hc Hm. apply sink_closed_pos. destruct (m <? REC_ARGS_MAX); [|apply Forall_nil].
apply Forall_cons; [cbn [fst]; unfold CALL_OFF_NARGS; lia|].
apply Forall_cons; [cbn [fst]; unfold CALL_OFF_ARGS; lia|].
apply Forall_nil.
Qed.

(* a byte of the slot is a byte of g_rec or of record.spill *)
Lemma sivL_slot_field : forall c a, rbs_slot_ok c -> c <= a < c + CALL_SIZE ->
(A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE).
Proof.
intros c a [(H1 & H2 & _) | ->] Ha; [left | right]; unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE, SC_SIZE in *; lia.
Qed.

Lemma sivL_slot_PG : forall c a, rbs_slot_ok c -> c <= a < c + CALL_SIZE -> Exists (in_zr a) recb_PG.
Proof.
intros c a Hc Ha. destruct (sivL_slot_field c a Hc Ha) as [Hz | Hz]; [apply recb_grec_in | apply recb_spill_in]; exact Hz.
Qed.

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

(* a live heap block lies apart from a range of image bytes *)
Lemma sivL_heap_apart : forall ly S (W : world SEGS) mem md p n g m,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < m ->
(forall a, g <= a < g + m -> in_img SEGS a) -> iv_apart p n g m.
Proof.
intros ly S W mem md p n g m HAR Hin Hm Himg. unfold iv_apart.
destruct (Z_le_gt_dec (p + n) g) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (g + m) p) as [H'|H']; [right; exact H'|]. exfalso.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [Hreq1 Hreq].
assert (Hab : p <= Z.max p g < p + req_size n) by lia.
assert (Hag : g <= Z.max p g < g + m) by lia.
exact (recb_heap_noimg_m B ly S W mem md p n (Z.max p g) HAR Hin Hab (Himg _ Hag)).
Qed.

Lemma siv_seg_L : siv_hyps B MT -> (forall fx1 : YK11.FPState, siv_A2_goal (fx := fx1) B MT) -> siv_L_goal B MT.
Proof.
intros HY GA2 ly S W regs mem md ch pl ledger line R O lyc Sc Wc memc mdc regs1 kk Q0 p1 k1 CX HFRM MID R9 R18.
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
assert (WA : ARG_I_STK = 16528) by (vm_compute; reflexivity).
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
destruct (siv_seed_mid B HB VOBJS SIV_L_RET sr_atoms lyc Sc Wc memc mdc regs regs1 sp0 n c (proj1 HJ)
  Hsp46 Hal16 Hn Hc Rsp HF ltac:(unfold siv_E; apply regs_ok_Eimg_Ereg)) as [HS SHOK].
pose proof (siv_env regs regs1 n c) as HE. pose proof HE as (HEI & _).
set (E := siv_E regs regs1 n c) in *.
assert (HAE : env_agree 32 (Ereg regs1 (rbs_extra regs n c)) E).
{ split; [intros k Hk; unfold E, siv_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
(* 0x8b468 .. 0x8b470: a0 = s0, a1 = s2, the call of arg_i *)
paj_run_tok RUN HS HJ SHOK siv_Bspan.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
pmkst HS.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ (ms_mem ?m2)) |- _ =>
  pose proof (siv_aview_eq (w_H Wc) memc (ms_mem m2) (siv_nowin E _ _ HFr)) as RDQ end.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
pose proof (aregs_preserved_of_st_ok SEGS (w_H Wc) E _ _ regs1 (rbs_extra regs n c) HS HAE ltac:(vm_compute; reflexivity)) as HPT.
cbn [ms_regs restrict] in HPT.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r) by (intros k r Hk; apply siv_E_reg; exact Hk).
assert (TP : forall r, acallee_saved r -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) by exact HPT.
assert (T2 : getr (ms_regs ms) 2 = getr regs1 2) by exact (TP 2 ltac:(unfold acallee_saved; lia)).
assert (Tsp : spZ (ms_regs ms) = sp0 + -48) by (unfold spZ; rewrite T2; fold (spZ regs1); lia).
assert (T3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by exact (eq_trans (TP 3 ltac:(unfold acallee_saved; lia)) Rgp).
assert (T4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by exact (eq_trans (TP 4 ltac:(unfold acallee_saved; lia)) Rtp).
assert (T8 : getr (ms_regs ms) 8 = w64 c) by exact (eq_trans (TP 8 ltac:(unfold acallee_saved; lia)) R8).
assert (T10 : getr (ms_regs ms) 10 = w64 c) by (rewrite P10, (EE 8%nat 8%bv eq_refl); exact R8).
assert (T11 : getr (ms_regs ms) 11 = w64 ledger) by (rewrite P11, (EE 18%nat 18%bv eq_refl); exact R18).
assert (Hcb : A_G_REC + OFF_CALLS <= c <= A_REC_SPILL) by (destruct (rbs_slot_bounds c Hc) as [H _]; exact H).
assert (Hc0 : 0 < c) by (unfold A_G_REC, OFF_CALLS in Hcb; lia).
assert (Hin_ai : In CS_arg_i cmd_prog_syms) by (unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right])).
rewrite (siv_sig CS_arg_i SIGP Hin_ai).
replace (cmd_af CS_arg_i) with AF_arg_i by (vm_compute; reflexivity).
pose proof (proj1 HJ) as HARc.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & Hnev & _).
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms)))
  by exact (siv_aro_kept B RRO RELRO ROPA ly S W mem md _ R O lyc Sc Wc (ms_mem ms) _ _ _ _ _ HAR HrepE HJ HROD).
assert (HROc : cmd_ro_ok (rdW Wc (ms_mem ms))) by exact (ROK lyc Sc Wc (ms_mem ms) _ HARc HRODc).
(* the slot holds one argument, the canonical line *)
assert (HNA1 : aval_mem (rdW Wc (ms_mem ms)) (c + CALL_OFF_NARGS) 4 1)
  by exact (aval_mem_kept _ _ _ _ _ (sivL_nargs_of _ _ R REC_INSTANCE_VERB [canon line] Q0 [(p1, k1)] HAREP) (fun k _ => RDQ _)).
(* the budgets at the call *)
assert (XA0 : 0 <= XM_ARG_I MT ledger) by (unfold XM_ARG_I, XM_XSTRDUP; apply (mo_malloc_nonneg MT MTL); lia).
assert (XN0 : 0 <= XM_ANSWER MT (snd (sup_instance_verb_m R line ledger))).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (sup_instance_verb_m R line ledger))) + 1) ltac:(lia)). lia. }
assert (HMOKa : mo_ok MT Sc (XM_ARG_I MT ledger)).
{ apply (mok_station MT S Sc _ _ _ MTL HMOK HMLE XA0). unfold XM_SUP_INSTANCE_VERB. lia. }
assert (HEVa : st_nev Sc + EV_ARG_I <= EV_MAX).
{ unfold EV_SUP_INSTANCE_VERB, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in HEV. unfold EV_ARG_I, EV_XSTRDUP in HEV |- *.
  clear - HEV Hnev Hkk. lia. }
assert (HLa : blocks_bytes Sc + LIVE_ARG_I ledger <= LIVE_MAX).
{ unfold LIVE_SUP_INSTANCE_VERB, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP in HLIVE. clear - HLIVE HLV. lia. }
(* 0x8b470: arg_i(c, ledger) *)
unfold siv_post.
eapply srr_after_callF.
{ eapply (cl_callS_wideF B LAWS Wc (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_arg_i)) SUP_INSTANCE_VERB_STK sp0
    (siv_FP O) ly S W mem md [] lyc Sc _ kk ARG_I_STK _ EV_ARG_I (-48) (getr (ms_regs ms) 1) [] _ HJ).
  - exact Tsp.
  - reflexivity.
  - lia.
  - rewrite WA. lia.
  - rewrite WA, WS. lia.
  - exact T3.
  - exact T4.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [unfold SIV_I_RET, AF_sup_instance_verb; lia | reflexivity].
  - rewrite P1, unsigned_lit_small by (unfold SIV_I_RET, AF_sup_instance_verb; lia). unfold SIV_I_RET, AF_sup_instance_verb. lia.
  - apply achain_low. unfold s0Z. rewrite T8. unfold w64. rewrite unsigned_lit_small by (unfold A_G_REC, A_REC_SPILL, OFF_CALLS in *; lia).
    unfold A_REC_SPILL in Hcb. lia.
  - intros HPRE1.
    exact (TARG_I fx lyc Sc Wc (ms_regs ms) (ms_mem ms) _ [] c ledger 1 HPRE1 HFRM
      ltac:(rewrite Hfrs; cbn [app]; exact HFR8) HRODc HROc T10 T11 Hled (sivL_slot_form R) HNA1
      ltac:(unfold REC_ARGS_MAX; lia) HEVa HLa HMOKa).
  - intros a Ha. right; right; right; right; left.
    pose proof (sivL_fp c 1 a ltac:(unfold REC_ARGS_MAX; lia) Ha) as Hx.
    assert (Hca : c <= a < c + CALL_SIZE) by (unfold CALL_SIZE; lia).
    split; [| split; [rewrite (recb_ts_prog_m B HB); exact (sivL_slot_PG c a Hc Hca) | exact (PIMG a (sivL_slot_PG c a Hc Hca))]].
    unfold siv_FP. apply inFP_cons. destruct (sivL_slot_field c a Hc Hca) as [Hz | Hz]; [left; exact Hz|].
    right. apply inFP_cons. left. exact Hz.
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
    pose proof (sivL_fp c 1 a ltac:(unfold REC_ARGS_MAX; lia) Ha) as Hx. rewrite WS in Hw. unfold A_REC_SPILL in Hcb.
    clear - Hx Hw Hcb Hceil Hslo Hstk0 C1. lia. }
cbv beta. intros fx1 ly2 S2 W2 regs2 mem2 md2 _ Hfx (HJ2 & HJ2i & HP2 & HK2).
cbv zeta in HK2.
destruct HK2 as (HBB2 & MLE2 & [(HM6 & _) | (_ & p & Hp4096 & HPerm2 & Hapart2 & HNA2 & HAP2 & HSTR2)]);
  [unfold REC_ARGS_MAX in HM6; lia|].
rewrite P1. change (Z_to_bv 64 (BASE + 20368)) with (Z_to_bv 64 (BASE + SIV_I_RET)).
set (kp := Z.of_nat (length (dec ledger)) + 1) in *.
pose proof (dec_length ledger Hled) as Hdec.
assert (Hkp : 2 <= kp <= 12) by (unfold kp; lia).
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2i as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _).
assert (Hp_in2 : In (p, kp) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPerm2)); left; reflexivity).
assert (HBL2 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2))
  by (intros pn Hpn; apply (Permutation_in pn (Permutation_sym HPerm2)); right; exact Hpn).
(* the new block: none of the blocks live at the call starts at p *)
assert (HpS : forall pn, In pn (ablocks B lyc Sc) -> fst pn <> p).
{ intros [b m] Hin Eb. cbn [fst] in Eb. subst b.
  pose proof (siv_block_start B ly2 S2 W2 mem2 md2 p m kp HAR2 (HBL2 _ Hin) Hp_in2) as ->.
  pose proof (proj1 (Forall_forall _ _) Hapart2 _ Hin) as Hap. cbn [fst snd] in Hap. unfold iv_apart in Hap. lia. }
assert (Hp_notc : ~ In (p, kp) (ablocks B lyc Sc)) by (intros Hin; exact (HpS _ Hin eq_refl)).
assert (I4 : forall pn, In pn (lay_blocks (slot_lay Q0 R [(p1, k1)])) -> In pn (ablocks B lyc Sc))
  by (intros pn Hpn; exact (rec_repA_in B lyc Sc _ _ _ (ex_intro _ _ (conj HAREP (fun x => iff_refl _))) pn Hpn)).
(* the memory after the call: the frame, g_rec / record.spill outside the two fields, the live blocks *)
assert (KEEPF : forall a, sp0 - 48 <= a < sp0 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. rewrite <- (RDQ a). apply G1; [lia | lia |].
  intros Hf. pose proof (sivL_fp c 1 a ltac:(unfold REC_ARGS_MAX; lia) Hf) as Hx. unfold A_REC_SPILL in Hcb. lia. }
assert (KEEPG : forall a, Exists (in_zr a) recb_PG -> ~ (c + 4 <= a < c + 8) -> ~ (c + 16 <= a < c + 24) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn1 Hn2. rewrite <- (RDQ a). destruct (siv_prog_unowned B HB a Ha) as [Hown Herr].
  apply G3; [exact (PIMG a Ha) | exact Hown | exact Herr |].
  apply fp_spares_closed; [exact (sivL_fp_closed c 1 Hc0 ltac:(lia))|].
  intros Hf. pose proof (sivL_fp c 1 a ltac:(unfold REC_ARGS_MAX; lia) Hf) as Hx. lia. }
assert (KEEPB : forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < m ->
  aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H Wc) memc (b + i)).
{ intros b m i Hbm Hi. rewrite <- (RDQ (b + i)).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARc Hbm) as (_ & _ & _ & _ & _ & _ & Hm).
  pose proof (req_size_pos m ltac:(lia)) as [_ Hreq].
  apply (G2 b m i Hbm (HBL2 _ Hbm)); [lia|].
  intros Hf. pose proof (sivL_fp c 1 (b + i) ltac:(unfold REC_ARGS_MAX; lia) Hf) as Hx.
  apply (recb_heap_noimg_m B lyc Sc Wc (ms_mem ms) _ b m (b + i) HARc Hbm ltac:(lia)).
  apply PIMG. apply (sivL_slot_PG c (b + i) Hc). unfold CALL_SIZE. lia. }
(* the recorder: arg_i's argument appended to the call record() made *)
assert (HAREP2 : arep_at (ablocks B ly2 S2) (rdW W2 mem2) A_G_REC A_REC_SPILL
  (rec_record R REC_INSTANCE_VERB [canon line; dec ledger]) (slot_lay Q0 R [(p1, k1); (p, kp)])).
{ refine (siv_arg_step (ablocks B lyc Sc) (rdW Wc memc) R REC_INSTANCE_VERB [canon line] Q0 [(p1, k1)]
    (ablocks B ly2 S2) (rdW W2 mem2) p kp (dec ledger) HAREP ltac:(cbn [length]; lia) _ Hp_in2 _ _ HNA2 HAP2 HSTR2
    ltac:(lia) _ _ _ _ _).
  - intros pn Hpn. exact (HBL2 _ (I4 _ Hpn)).
  - intros a Ha Hn1 Hn2. change (siv_slot R) with c in Hn1, Hn2.
    change (Z.of_nat (length [canon line])) with 1 in Hn2.
    assert (HPG : Exists (in_zr a) recb_PG)
      by (destruct Ha as [Ha | Ha]; [apply recb_grec_in | apply recb_spill_in]; exact Ha).
    apply (KEEPG a HPG); unfold CALL_OFF_NARGS, CALL_OFF_ARGS in *; lia.
  - intros [b m] i Hpn Hi. cbn [fst snd] in Hi |- *. exact (KEEPB b m i (I4 _ Hpn) Hi).
  - split; [unfold kp; lia | unfold LMAX; lia].
  - unfold LMAX. lia.
  - intros Hin. apply in_map_iff in Hin as (pn & Est & Hpn). exact (HpS pn (I4 pn Hpn) Est).
  - apply (sivL_heap_apart ly2 S2 W2 mem2 md2 p kp A_G_REC REC_SIZE HAR2 Hp_in2 ltac:(unfold REC_SIZE; lia)).
    intros a Ha. apply PIMG. apply recb_grec_in. exact Ha.
  - apply (sivL_heap_apart ly2 S2 W2 mem2 md2 p kp A_REC_SPILL SC_SIZE HAR2 Hp_in2 ltac:(unfold SC_SIZE; lia)).
    intros a Ha. apply PIMG. apply recb_spill_in. exact Ha. }
pose proof (sivL_slot_lay_snoc Q0 R [(p1, k1)] (p, kp)) as HPQ.
change ([(p1, k1)] ++ [(p, kp)]) with [(p1, k1); (p, kp)] in HPQ.
(* 0x8b474: the next segment's state *)
apply (GA2 fx1 ly S W regs mem md ch pl ledger line R O ly2 S2 W2 mem2 md2 regs2 (kk + EV_ARG_I)
  (slot_lay Q0 R [(p1, k1); (p, kp)]) CX (fxrel_frm0 fx fx1 HFRM Hfx)).
2: { exact (eq_trans (HP2 9 ltac:(unfold acallee_saved; lia)) (eq_trans (TP 9 ltac:(unfold acallee_saved; lia)) R9)). }
unfold siv_mid.
split; [exact HJ2|].
split; [unfold EV_ARG_I, EV_XSTRDUP; clear - Hkk; lia|].
split; [exact (siv_frame_kept (w_H Wc) (w_H W2) memc mem2 sp0 regs HF KEEPF)|].
split.
{ assert (U2 : getr regs2 2 = getr (ms_regs ms) 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
  split; [unfold spZ at 1; rewrite U2; exact Tsp|].
  split; [exact (eq_trans (HP2 3 ltac:(unfold acallee_saved; lia)) T3)|].
  split; [exact (eq_trans (HP2 4 ltac:(unfold acallee_saved; lia)) T4)|].
  split; [exact (eq_trans (HP2 8 ltac:(unfold acallee_saved; lia)) T8)|].
  intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)), (TP r ltac:(unfold acallee_saved; lia)). exact (Rhi r Hr). }
split; [exact HAREP2|].
split.
{ intros pn Hpn. apply (Permutation_in _ HPQ) in Hpn. apply in_app_iff in Hpn as [Hpn | [<- | []]].
  - exact (I1 pn Hpn).
  - destruct (siv_in_dec (p, kp) (ablocks B ly S)) as [Hin | Hnin]; [|right; exact Hnin].
    destruct (siv_in_dec (p, kp) O) as [Ho | Hno]; [left; exact Ho|].
    exfalso. exact (Hp_notc (I2 _ Hin Hno)). }
split; [intros pn Hpn Hno; exact (HBL2 _ (I2 pn Hpn Hno))|].
split.
{ intros pn Hpn. apply (Permutation_in _ HPerm2) in Hpn. destruct Hpn as [<- | Hpn].
  - right. apply (Permutation_in _ (Permutation_sym HPQ)). apply in_app_iff. right. left. reflexivity.
  - destruct (I3 pn Hpn) as [H | H]; [left; exact H|].
    right. apply (Permutation_in _ (Permutation_sym HPQ)). apply in_app_iff. left. exact H. }
split; [exact (mle_station MT S Sc S2 _ _ MTL HMLE MLE2)|].
clear - HLV HBB2. lia.
Qed.

End e.
End f.
End d.
