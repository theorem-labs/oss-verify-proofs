(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of sup_after_reply on plugin-hostd/fuzz_command's ASan+UBSan build
   (fuzz_command.asan-ubsan, entry 0x8c758 = BASE + AF_sup_after_reply, 120 instructions), proving a Theorem Labs lane's
   tsup_after_reply_spec (lib/B/Prog/sup_after_reply_c.v, statement from a Theorem Labs lane 0934cb146c3). Shape: the ASan walk of
   answer_code (lib/A/Prog/answer_code.v, a working branch 2ba4488ce71) - a side-stack frame taken by
   __asan_stack_malloc_0, its header and shadow, the snprintf wrapper, program callees through cl_callS_wide, the
   release by the flag store - over B's code. The snprintf wrapper is the one step that changes the FP state: the
   walk goes on at the FP state fx1 it returns (PaFx's aj_art_own_atF, srr_art_postF_of_pf, srr_after_artF), with
   the symbolic state moved to fx1 by PaFx's st_ok_pi_restrict_xfx.
   Calls: __asan_stack_malloc_0 (0x8c7c0, return BASE + AF_sup_after_reply + 0x6c), record (0x8c858, return + 0x104),
   the snprintf trampoline (0x8c87c, return + 0x128), arg_s twice (0x8c888 return + 0x134, 0x8c89c return + 0x148).
   s0 is the frame pointer (the entry sp) at every call, so each call's frame chain is afn_pre's chain pushed by the
   frame record the prologue stored (sar_chain_at, achain_push).
   No __asan_report_* call and no UBSan trap site (capstone over the pin's .symtab; a Theorem Labs lane's gen/traps.B.summary:49
   `sup_after_reply 0`, gen/funcs.tsv:50 `0` reports). The branches the walk prunes: 0x8c7b8 (the use-after-return
   flag, the record's const cell 1, read through sar_entry's region from al_const), 0x8c7d4 and 0x8c8ac (the side
   frame F is nonzero, the HPTR fact on its atom from frames_bounds). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00 YI0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YM05 YG05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdSyms CmdList CmdAddr CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaCallRun PaCall PaArt PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtPFShared RtPFCmd RtPFSx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c record_c arg_s_c sup_after_reply_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_after_reply_aux RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecRest CmdRecAns.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the program's writable statics are the record's TFIB_PROG_STATIC (lib/B/YF0m.v:4874; CmdBSyms' ts_prog), the form
   a Theorem Labs lane's record facts use (lib/B/Prog/CmdRecRest.v:56-73 on a working branch 6830f0bf032) *)

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PI c).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses (sup_after_reply_c.v, Section e; pass 4b: the callees' contracts at every FP
   state, so that the walk can use them at the fx' the snprintf wrapper returns at) *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis AFREE_LAW : astack_free_law SEGS B.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
@asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses of a Theorem Labs lane's RULING-STMT.md section 1 *)
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTLF : ameter_fs_laws MT.
Hypothesis SIGP : cmd_sig_prog.
(* the per-binary image facts, as ONE record in a Theorem Labs lane's own form (lib/B/Prog/CmdRecBase.v cmd_img_facts on
   a working branch 0934cb146c3): every named record fact this walk uses (cmd_prog_img, cmd_ro_prog_apart,
   cmd_ro_ok_of_aro, cmd_rec_cells, RELRO_IMG, cmd_fobj_tail, cmd_heap_tail_vis, cmd_rodata_kept,
   cmd_consts_view_snp) is a Theorem Labs lane's lemma over it, so the closing file discharges this one hypothesis *)
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> cmd_img_facts SEGS B0.
(* the side-stack frame's flag law (a Theorem Labs lane's CmdRecRest.cmd_frame_flag_law at the pinned image) *)
Hypothesis FFL : frame_flag_lawP SEGS B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let ML : model_laws (as_universe B) := model_laws_ok (as_universe B) (ts_universe B HB).
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
Let IMG : cmd_img_facts SEGS B := cmd_img_facts_tfib B HB.

(* a Theorem Labs lane's record lemmas at this walk's SEGS and B (lib/B/Prog/CmdRec{Ro,Img,Cells,Rest}.v), by exact *)
Let CPIMG := cmd_prog_img SEGS B LAWS HB IMG.
Let CROPA := cmd_ro_prog_apart SEGS B LAWS HB IMG.
Let CROOK := cmd_ro_ok_of_aro SEGS B LAWS HB IMG.
Let CCELLS := cmd_rec_cells SEGS B LAWS HB IMG.
Let CRELRO := RELRO_IMG SEGS B LAWS HB IMG.
Let CHEAPT := cmd_heap_tail_vis SEGS B LAWS HB.
Let CFOBJT := cmd_fobj_tail SEGS B LAWS HB.
Let CRODK := cmd_rodata_kept SEGS B LAWS HB IMG.
Let CCVS := cmd_consts_view_snp SEGS B LAWS HB IMG.
Lemma sar_in_PG : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros a [Ha | Ha]; apply Exists_exists; unfold TFIB_PROG_STATIC;
[exists (0x5e32c0, 960); split; [left; reflexivity|] | exists (0x5e3760, 56); split; [right; left; reflexivity|]];
unfold in_zr, A_G_REC, A_REC_SPILL, REC_SIZE, SC_SIZE in *; cbn [fst snd]; lia.
Qed.
Lemma sar_ts_prog : as_prog_static B = TFIB_PROG_STATIC.
Proof. exact (ts_prog B HB). Qed.


Theorem tsup_after_reply_holds : tsup_after_reply_spec B MT.
Proof.
unfold tsup_after_reply_spec.
intros ly S W regs mem md ch id pv verb R O HPRE HFRM HROD HRO H10 Hid H11 Hpv HVERB HREP Hfr8 Hev Hlive MOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : SUP_AFTER_REPLY_STK = 16672) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
set (FP := (A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O).
pose proof (sar_entry B TL TLF SUP_AFTER_REPLY_STK W ly S regs mem md ch ltac:(rewrite FS; lia) HPRE) as HS.
pose proof (ajournal_init SEGS B SUP_AFTER_REPLY_STK FP ly S W regs mem md ch HPRE) as HJ.
set (sp1 := 32 * ((spZ regs - 96) / 32)) in HS.
destruct (sar_sp1_facts (spZ regs) Hal16 ltac:(lia)) as (Hsp1 & Hsp1a & Hsp1b). fold sp1 in Hsp1, Hsp1a, Hsp1b.
remember (Eimg (Ereg regs (sar_extra (as_uar_cell B) sp1))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (sar_extra (as_uar_cell B) sp1)) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 sp1) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
clear HE.
assert (Esp : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite Esp; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = sp1) by (rewrite E34; apply unsigned_lit_small; lia).
pose proof (palf_uar_img B TLF) as Huar.
unfold cfg_at. change (w64 (BASE + AF_sup_after_reply)) with (Z_to_bv 64 (BASE + AF_sup_after_reply)).
(* run 1: the prologue, the realignment, the GOT words, and the call of __asan_stack_malloc_0 at 0x8c7c0 *)
paj_run_shc RUNP RUNC HS HJ.
{ unfold ss_sar0, sar_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP. cbn [ss_mem].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Usp; lia | cbn; rewrite FS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Usp; lia | cbn; rewrite FS; lia | cbn; lia |].
repeat (apply (awr_ok_cons_ro SEGS B); [cbn; lia|]). apply (awr_ok_nil SEGS B). }
rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
(* the call of __asan_stack_malloc_0 at 0x8c7c0 (a0 = 64; the use-after-return flag is the record's const cell 1, so
   the beqz at 0x8c7b8 is not taken and the real-stack fallback 0x8c7d8-0x8c7f0 is not reached) *)
pmkst HS.
sar_preg HS (2%bv : bv 5) R2. sar_preg HS (1%bv : bv 5) R1. sar_preg HS (3%bv : bv 5) R3. sar_preg HS (4%bv : bv 5) R4.
rewrite (sar_denot_and32 E 2 (spZ regs) Esp ltac:(lia)) in R2. fold sp1 in R2.
cbn [sv_denot] in R1. rewrite (img_env_codeptr E HEI 25236) in R1.
rewrite sar_denot_off0, (EE 3%nat 3%bv eq_refl) in R3. rewrite sar_denot_off0, (EE 4%nat 4%bv eq_refl) in R4.
sar_preg HS (9%bv : bv 5) R9.
rewrite sar_denot_add0, (sar_denot_and32 E 2 (spZ regs) Esp ltac:(lia)) in R9. fold sp1 in R9.
(* sp and s1 both hold the realigned sp: rebase them on its atom, so that the store at 0x8c7f4 resolves *)
lazymatch type of HS with st_ok ?sg ?Ev ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp sg Ev ssx msx (2%bv : bv 5) (SOff 34 0) HS eq_refl
ltac:(rewrite sar_denot_off0, E34; cbn [ms_regs restrict mkst]; rewrite R2; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok ?sg ?Ev ?ssx ?msx =>
pose proof (ast_ok_set_reg_fp sg Ev ssx msx (9%bv : bv 5) (SOff 34 0) HS eq_refl
ltac:(rewrite sar_denot_off0, E34; cbn [ms_regs restrict mkst]; rewrite R9; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS. sar_norm HS.
pose proof (palf_sm B TLF 0 ltac:(cbn; tauto)) as SM0. change (cs_stack_malloc 0) with CS___asan_stack_malloc_0 in SM0.
rewrite SM0.
assert (Qsp : spZ (ms_regs ms1) = spZ regs + (sp1 - spZ regs))
  by (unfold spZ at 1; rewrite R2, unsigned_lit_small by lia; lia).
eapply SRr_bind.
{ eapply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low (pal_env B TL) ML (CmdRecRest.cmd_stack_malloc_progress B) 0 (ASTACK_MALLOC0 fx) ltac:(lia)
W (ms_regs ms1) (ms_mem ms1) SUP_AFTER_REPLY_STK (spZ regs) FP ly S W mem md [] ly S _ 0 (sp1 - spZ regs)
(Z_to_bv 64 (BASE + 25236)) HJ);
[ exact Qsp | exact Hsp1b | lia | rewrite FS, Hes; lia | rewrite R3; exact Hgp | rewrite R4; exact Htp
| exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity]
| pose proof (count_cid_le_length 0 (frames S)); change (fs_frames 0) with 16384; lia ]. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJS & (fS2 & ES2)).
(* back at 0x8c7c4 with the frame F: keep the saved registers (the zero word at sp0 - 96 is dropped, the realigned
   stack word sp1 lies there), name F, its flag word and its shadow, and seat the frame's regions *)
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ2pres & _).
pose proof HK as (HK1 & HK2 & HK3 & HK4 & HK5 & HK6).
jafter_call_keep_hi HS 1024%nat regs2 (mrestrict (w_H W) mem2) HP2 [1]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
eapply sar_region_kept_hi2; [exact Usp | intros a Ha; apply HK1; lia | intros a Ha; apply HJ2pres; rewrite FS; lia]. }
rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
clear R1 R2 R3 R4 Qsp.
remember (havoc E 1024 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
assert (HAE1 : env_agree 32 (Ereg regs (sar_extra (as_uar_cell B) sp1)) E1) by (rewrite HE1; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]).
assert (OLD1 : forall n, (n < 1024)%nat -> ew E1 n = ew E n) by (intros n Hn; rewrite HE1; apply ew_havoc_old; exact Hn).
set (F := frame_addr ly 0 fpos) in *. set (FL := flag_addr ly 0 fpos) in *.
assert (E1028 : ew E1 1028 = Z_to_bv 64 F).
{ rewrite HE1. change 1028%nat with (1024 + 4)%nat. rewrite (ew_havoc_new E 1024 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
unfold CLOB. cbn [map nth]. exact Ha0. }
clear HE1.
pose proof (proj1 HJ2) as HAR2.
assert (Hfin : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin) as (HFal & HFapp & HFpres & HFSpres). fold F in HFal, HFapp, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR2 Hfin) as (HF4096 & HFceil & _). fold F in HF4096, HFceil.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR2 Hfin) as HFoff. fold F in HFoff. unfold off_img in HFoff.
destruct (frame_al64 SEGS B _ _ _ _ _ 0 fpos HAR2 Hfin) as (HF64 & _ & _). fold F in HF64.
destruct (FFL _ _ _ _ _ 0 fpos HAR2 Hfin) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLceil)).
fold FL in HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLceil.
change (fs_frame_bytes 0) with 64 in *. change (64 / 8) with 8 in *.
replace (F + 64 - 8) with (F + 56) in Hflag by lia.
assert (HFin : in_app F 64) by exact HFapp.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFin.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_havoc_hi 1040 Ev ssv msv [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(vm_compute; reflexivity)) as HS3 end.
clear HS. rename HS3 into HS.
remember (havoc E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) as E2 eqn:HE2 in HS.
assert (HAE2 : env_agree 32 (Ereg regs (sar_extra (as_uar_cell B) sp1)) E2) by (rewrite HE2; apply env_agree_havoc_ge; [lia | exact HAE1]).
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [exact HEI1 | unfold A_LIM; lia]).
assert (OLD2 : forall n, (n < 1024)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2, ew_havoc_old by lia; apply OLD1; exact Hn).
assert (E1040 : ew E2 1040 = Z_to_bv 64 FL) by (rewrite HE2; exact (ew_havoc_new E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E1041 : ew E2 1041 = Z_to_bv 64 (SB + F / 8)) by (rewrite HE2; exact (ew_havoc_new E1 1040 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (E2028 : ew E2 1028 = Z_to_bv 64 F) by (rewrite HE2, ew_havoc_old by lia; exact E1028).
clear HE2.
assert (E2_32 : ew E2 32 = Z_to_bv 64 SB) by (rewrite OLD2 by lia; exact E32).
assert (V2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
assert (V34 : bv_unsigned (ew E2 34) = sp1) by (rewrite OLD2 by lia; exact U34).
assert (V1028 : bv_unsigned (ew E2 1028) = F) by (rewrite E2028; apply unsigned_lit_small; lia).
assert (V1040 : bv_unsigned (ew E2 1040) = FL) by (rewrite E1040; apply unsigned_lit_small; lia).
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (HF8b : F / 8 <= 17592185978880) by (apply Z.div_le_upper_bound; lia).
assert (V1041 : bv_unsigned (ew E2 1041) = SB + F / 8) by (rewrite E1041; apply unsigned_lit_small; unfold SB; lia).
assert (HF8m : F mod 8 = 0) by (pose proof (Z.div_mod F 64 ltac:(lia)); rewrite HF64 in *; replace F with (64 * (F / 64)) by lia; replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia; apply Z_mod_mult).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_fact Ev ssv msv 1028 (HPTR 5) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite V1028; change (2 ^ 5) with 32;
pose proof (Z.div_mod F 64 ltac:(lia)); rewrite HF64 in *;
split; [lia|]; split; [replace F with (64 * (F / 64)) by lia; replace (64 * (F / 64)) with ((2 * (F / 64)) * 32) by lia; apply Z_mod_mult | lia])) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ ?msv =>
pose proof (st_ok_pi_add_alias Ev _ msv sar_shx_F (SOff 1041 0) HS (shadow_decl_ok Ev 1028 32 1041 F SB E2028 ltac:(lia) E2_32 E1041)) as HS3 end.
clear HS. rename HS3 into HS. sar_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv sar_sp1slot HS eq_refl
ltac:(unfold region_ok, sar_sp1slot; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite V34; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply HJ2pres; rewrite FS; lia)
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, sar_sp1slot; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite V34, V2; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. sar_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv sar_fr_hdr HS eq_refl
ltac:(unfold region_ok, sar_fr_hdr; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite V1028; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia))))
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, sar_fr_hdr, sar_sp1slot; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite V1028, V34, V2; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. sar_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv sar_fr_flg HS eq_refl
ltac:(unfold region_ok, sar_fr_flg; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite V1028; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Ev _ F 56 8 (SOff 1040 0) FL); [rewrite sar_denot_off0; exact E1040 | lia | lia |];
exact (val_mem_of_rdword SEGS _ _ _ _ Hflag))
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, sar_fr_flg, sar_fr_hdr, sar_sp1slot; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite V1028, V34, V2; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. sar_norm HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv sar_fr_shd HS eq_refl
ltac:(unfold region_ok, sar_fr_shd; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite V1041; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS);
replace (SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
apply (proj1 (HFSpres o ltac:(lia))))
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint, sar_fr_shd, sar_fr_flg, sar_fr_hdr, sar_sp1slot;
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite V1041, V1028, V34, V2; unfold SB; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. sar_norm HS.
(* run 2: the frame's header and shadow, the realigned stack word, and the call of record(19) at 0x8c858 *)
paj_run_shc RUNP RUNC HS HJ2.
{ eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 1041%nat); [reflexivity | exact V1041 |
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
right; unfold in_zr, shadow_addr; cbn [fst snd]; fold F; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia |].
apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 1028%nat); [reflexivity | exact V1028 |
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
left; unfold in_zr; cbn [fst snd]; fold F; change (fs_frame_bytes 0) with 64; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite V34; lia | cbn; rewrite FS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite V2; lia | cbn; rewrite FS; lia | cbn; lia |].
apply (awr_ok_nil SEGS B). }
rename ms into ms3, mat into mat3, HF into HF3, HFr into HFr3, HG into HG3.
(* where the recorder's state and its blocks lie: none of them in the frame, its shadow, its flag or the stack *)
set (KA := fun a : Z => (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
(exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n)).
assert (KIMG : forall a, KA a -> (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
(in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))).
{ intros a Ha. rewrite (ts_owned B HB), (ts_errno B HB). unfold TFIB_ERRNO.
destruct Ha as [Ha | [Ha | Ha]]; [right | right | left; exact Ha].
- split; [apply CPIMG; apply sar_in_PG; left; exact Ha|].
  split; [exact (sar_grec_not_owned a Ha) | unfold A_G_REC, REC_SIZE in Ha; lia].
- split; [apply CPIMG; apply sar_in_PG; right; exact Ha|].
  split; [exact (sar_spill_not_owned a Ha) | unfold A_REC_SPILL, SC_SIZE in Ha; lia]. }
assert (KLOC : forall a, KA a -> 0 <= a < alloc_ceiling /\ ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ a <> FL).
{ intros a Ha. destruct (KIMG a Ha) as [(p & n & Hpn & Hpa) | (Hi & _ & _)].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hpn) as (_ & Hp4096 & Hpceil & Hpapp & _ & _).
  assert (Hpn2 : In (p, n) (ablocks B ly S2)) by (rewrite Eab; exact Hpn).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR2 Hpn2) as (_ & _ & _ & _ & Hpres2 & _).
  pose proof (sep_block_frame SEGS B LAWS ly S2 W mem2 md2 p n 0 fpos HAR2 Hpn2 Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold F in Hd. change (fs_frame_bytes 0) with 64 in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
  split; [lia|]. split; [lia|]. split; [unfold SB; lia|].
  intros ->. exact (proj2 (Hpres2 FL ltac:(lia)) HFLo).
- pose proof (pa_img_range a Hi) as Hr.
  split; [lia|]. split; [lia|]. split; [unfold SB; lia|]. intros ->. exact (HFLimg Hi). }
assert (K01 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & _). apply (sar_aview_frame_pt E _ (w_H W) mem (ms_mem ms1) a HFr1); [lia|].
sar_nwin ltac:(fun H => rewrite ?Usp, ?U34 in H; lia). }
assert (K12 : forall a, KA a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem ms1) a).
{ intros a Ha. destruct (KIMG a Ha) as [(p & n & Hpn & Hpa) | (Hi & Ho & He)].
- replace a with (p + (a - p)) by lia. apply (HK2 p n (a - p) Hpn); [lia | intros []].
- exact (HK3 a Hi Ho He). }
assert (K23 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem2 a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & HnS & _).
apply (sar_aview_frame_pt E2 _ (w_H W) mem2 (ms_mem ms3) a HFr3); [lia|].
sar_nwin ltac:(fun H => rewrite ?V2, ?V34, ?V1028, ?V1041 in H; unfold SB in *; lia). }
assert (K03 : forall a, KA a -> aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a)
by (intros a Ha; rewrite (K23 a Ha), (K12 a Ha), (K01 a Ha); reflexivity).
(* the recorder's state and the read-only bytes at the record call *)
assert (HOB : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn Hpn; exact (sar_rec_repA_in B ly S _ R O HREP pn Hpn)).
assert (HREP3 : rec_repA B ly S2 (rdW W (ms_mem ms3)) R O).
{ apply (sar_rec_repA_kept B ly S (rdW W mem) ly S2 (rdW W (ms_mem ms3)) R O HREP).
- intros pn Hpn. rewrite Eab. exact (HOB pn Hpn).
- intros a Ha. apply K03. left. unfold REC_SIZE. exact Ha.
- intros a Ha. apply K03. right. left. unfold SC_SIZE. exact Ha.
- intros p n i Hpn Hi. apply K03. right. right. exists p, n.
  split; [exact (HOB (p, n) Hpn)|]. unfold req_size. destruct (Z.eqb_spec n 0); lia. }
assert (HFPKA : forall a, inFP FP a -> KA a).
{ intros a (r & Hr & Hrq). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hrq.
- left. exact Hrq.
- right. left. exact Hrq.
- right. right. destruct (inFP_ablocks_fp_inv O a (ex_intro _ r (conj Hr Hrq))) as (p & n & Hin & Hpa).
  exists p, n. split; [exact (HOB (p, n) Hin) | exact Hpa]. }
assert (HFPRO : forall a, in_roP SEGS RLO RHI a -> ~ inFP FP a).
{ intros a Hro Hf. destruct (CROPA a Hro) as [Hi Hpg].
  destruct (HFPKA a Hf) as [Ha | [Ha | (p & n & Hpn & Hpa)]].
  - exact (Hpg (sar_in_PG a (or_introl Ha))).
  - exact (Hpg (sar_in_PG a (or_intror Ha))).
  - exact (blk_img SEGS B LAWS ly S W mem md p n a HAR Hpn Hpa Hi). }
assert (HROD3 : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms3))).
{ apply (CRODK ly S W mem md ly S2 W (ms_mem ms3) _ SUP_AFTER_REPLY_STK (spZ regs) FP [(0, fpos)] 0 HAR HJ2); [|exact HROD].
  intros a Hf. destruct (HFPKA a Hf) as [Ha | [Ha | (p & n & Hpn & Hpa)]].
  - left. exact (sar_in_PG a (or_introl Ha)).
  - left. exact (sar_in_PG a (or_intror Ha)).
  - right. exists p, n. split; [apply in_or_app; left; exact Hpn | exact Hpa]. }
pose proof (CROOK ly S2 W (ms_mem ms3) _ (proj1 HJ2) HROD3) as HRO3.
(* the call of record(19) at 0x8c858, through trecord_spec and cl_callS_wide *)
assert (SIGREC : SIG CS_record = BASE + AF_record) by (exact (CmdRecAns.rca_sig_record SIGP)).
pmkst HS. rewrite SIGREC.
sar_preg HS (10%bv : bv 5) P10. sar_preg HS (1%bv : bv 5) P1. sar_preg HS (2%bv : bv 5) P2.
sar_preg HS (3%bv : bv 5) P3. sar_preg HS (4%bv : bv 5) P4. sar_preg HS (8%bv : bv 5) P8.
cbn [sv_denot] in P1, P10. rewrite (img_env_codeptr E2 HEI2 25388) in P1.
rewrite sar_denot_off0, (OLD2 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl) in P3.
rewrite sar_denot_off0, (OLD2 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl) in P4.
rewrite sar_denot_off0 in P2, P8.
assert (Qsp3 : spZ (ms_regs ms3) = spZ regs + (sp1 - spZ regs))
  by (unfold spZ at 1; rewrite P2, V34; lia).
(* the frame chain at record's entry: s0 is this call's frame pointer (the entry sp), whose frame record (ra at
   sp0 - 8, the caller's s0 at sp0 - 16) the prologue stored (achain_push on afn_pre's chain) *)
assert (WRA3 : rdword (rdW W (ms_mem ms3)) (spZ regs + -8) = Some (raZ regs)).
{ sar_wfind HS E2 (w_H W) ms3 2%nat;
  [ exact V2 | repeat (first [left; reflexivity | right])
  | rewrite sar_denot_off0, (OLD2 1%nat ltac:(lia)), (EE 1%nat 1%bv eq_refl); unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
  | unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr; exact Hr ]. }
assert (WS03 : rdword (rdW W (ms_mem ms3)) (spZ regs + -16) = Some (s0Z regs)).
{ sar_wfind HS E2 (w_H W) ms3 2%nat;
  [ exact V2 | repeat (first [left; reflexivity | right])
  | rewrite sar_denot_off0, (OLD2 8%nat ltac:(lia)), (EE 8%nat 8%bv eq_refl); unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
  | unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr; exact Hr ]. }
assert (HCH3 : exists ch3, achain ly (rdW W (ms_mem ms3)) (spZ regs + (sp1 - spZ regs)) (s0Z (ms_regs ms3)) ch3).
{ assert (Es03 : s0Z (ms_regs ms3) = spZ regs) by (unfold s0Z; rewrite P8; exact V2). rewrite Es03.
  apply (sar_chain_at ly (rdW W mem) _ (spZ regs) (s0Z regs) (raZ regs) ch);
  [ exact Hch | lia | lia
  | intros a Ha; apply (aview_above_of_journal (PI := PI) B SUP_AFTER_REPLY_STK (spZ regs) FP ly S W mem md _ ly S2 W
      (ms_mem ms3) _ 0 HJ2 a Ha);
    intros Hf; destruct (KLOC a (HFPKA a Hf)) as (Hb & _); unfold alloc_ceiling in *; lia
  | replace (spZ regs - 8) with (spZ regs + -8) by lia; exact WRA3
  | replace (spZ regs - 16) with (spZ regs + -16) by lia; exact WS03
  | exact Hra4 | lia | apply sar_mod_16_8; exact Hal16 | lia ]. }
destruct HCH3 as (ch3 & HCH3).
pose proof HREP as (Q0 & HA0 & HOQ0). pose proof HA0 as (_ & _ & _ & (Hlen16 & _) & _).
destruct (sar_slot_range R Hlen16) as (Hslot8 & Hslotr).
set (FPREC := (A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
(if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)).
assert (HFP1KA : forall a, inFP FPREC a -> KA a).
{ intros a (r & Hr & Hrq). unfold FPREC in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hrq.
  - left. unfold OFF_NCALLS, REC_SIZE in *. lia.
  - destruct Hslotr as [[Hlo Hhi] | Heq]; [left; unfold OFF_CALLS, CALL_SIZE in *; lia | right; left; rewrite Heq in Hrq; unfold SC_SIZE in *; lia].
  - destruct (Nat.ltb (length (r_calls R)) 16); [destruct Hr|].
    right. right. destruct (inFP_ablocks_fp_inv O a (ex_intro _ r (conj Hr Hrq))) as (p & n & Hin & Hpa).
    exists p, n. split; [exact (HOB (p, n) Hin) | exact Hpa]. }
assert (HNEV3 : st_nev S2 + EV_RECORD R <= EV_MAX).
{ rewrite Hnev2. unfold EV_SUP_AFTER_REPLY, EV_ARG_S, EV_XMALLOC in Hev. lia. }
assert (HMOKS2 : mo_ok MT S2 (XM_SUP_AFTER_REPLY MT R id verb))
  by (rewrite ES2; apply (mo_ok_set_fs MT MTLF); exact MOK).
assert (HXMnn : 0 <= XM_ARG_S MT (Some (dec id)) /\ 0 <= XM_ARG_S MT verb).
{ unfold XM_ARG_S, XM_XMALLOC, LIVE_XMALLOC. split;
  [ exact (mo_malloc_nonneg MT MTL (Z.max (Z.of_nat (length (sarg (Some (dec id)))) + 1) 1) ltac:(lia))
  | exact (mo_malloc_nonneg MT MTL (Z.max (Z.of_nat (length (sarg verb)) + 1) 1) ltac:(lia)) ]. }
assert (HMOK3 : mo_ok MT S2 (XM_RECORD MT R)).
{ apply (mo_ok_le MT MTL S2 _ (XM_SUP_AFTER_REPLY MT R id verb)); [exact HMOKS2|].
  unfold XM_SUP_AFTER_REPLY, XM_ARG_S, XM_XMALLOC, LIVE_XMALLOC.
  pose proof (mo_malloc_nonneg MT MTL (Z.max (Z.of_nat (length (sarg (Some (dec id)))) + 1) 1) ltac:(lia)).
  pose proof (mo_malloc_nonneg MT MTL (Z.max (Z.of_nat (length (sarg verb)) + 1) 1) ltac:(lia)). lia. }
assert (HRECSTK : RECORD_STK = 16560) by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W (ms_regs ms3) (ms_mem ms3) (Z_to_bv 64 (BASE + AF_record)) SUP_AFTER_REPLY_STK
(spZ regs) FP ly S W mem md [(0, fpos)] ly S2 _ 0 RECORD_STK FPREC (EV_RECORD R) (sp1 - spZ regs)
(getr (ms_regs ms3) 1) ch3 _ HJ2 Qsp3 Hsp1b);
[ lia | rewrite HRECSTK; lia | rewrite HRECSTK, FS; lia | rewrite P3; exact Hgp | rewrite P4; exact Htp | reflexivity
| rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]
| rewrite P1, unsigned_lit_small by lia; lia
| exact HCH3
| intros HPRE3; exact (TRECORD fx ly S2 W (ms_regs ms3) (ms_mem ms3) _ ch3 19 R O HPRE3 HROD3 P10
    ltac:(unfold REC_FN_COUNT; lia) HREP3 HNEV3 HMOK3)
| intros a Hf; pose proof Hf as (r & Hr & Hrq); unfold FPREC in Hr; cbn [In] in Hr;
  destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hrq;
  [ right; right; right; right; left;
    split; [exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity | cbn [fst snd]; unfold OFF_NCALLS, REC_SIZE in *; lia]|];
    rewrite sar_ts_prog;
    assert (Hg : A_G_REC <= a < A_G_REC + REC_SIZE) by (unfold OFF_NCALLS, REC_SIZE in *; lia);
    split; [exact (sar_in_PG a (or_introl Hg)) | exact (CPIMG a (sar_in_PG a (or_introl Hg)))]
  | right; right; right; right; left;
    destruct Hslotr as [[Hlo Hhi] | Heq];
    [ split; [exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity | cbn [fst snd]; unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia]|];
      rewrite sar_ts_prog;
      assert (Hg : A_G_REC <= a < A_G_REC + REC_SIZE) by (unfold OFF_CALLS, CALL_SIZE, REC_SIZE in *; lia);
      split; [exact (sar_in_PG a (or_introl Hg)) | exact (CPIMG a (sar_in_PG a (or_introl Hg)))]
    | rewrite Heq in Hrq;
      split; [exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split; [right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in *; lia]|];
      rewrite sar_ts_prog;
      assert (Hg : A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) by (unfold SC_SIZE in *; lia);
      split; [exact (sar_in_PG a (or_intror Hg)) | exact (CPIMG a (sar_in_PG a (or_intror Hg)))] ]
  | destruct (Nat.ltb (length (r_calls R)) 16); [destruct Hr|];
    destruct (inFP_ablocks_fp_inv O a (ex_intro _ r (conj Hr Hrq))) as (p & n & HinO & Hpa);
    right; left; split;
    [ destruct (inFP_ablocks_fp O p n (a - p) HinO ltac:(lia)) as (r2 & Hr2 & Hb2);
      exists r2; split; [right; right; exact Hr2 | replace (p + (a - p)) with a in Hb2 by lia; exact Hb2]
    | exists p, n; split; [rewrite Eab; exact (HOB (p, n) HinO) | exact Hpa] ] ]
| intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _; exfalso;
  destruct (KLOC a (HFP1KA a Ha)) as (Hb & _); rewrite FS in Hw; unfold alloc_ceiling in *; lia ]. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJ4c & HP4 & HKrec).
rewrite P1.
(* back at 0x8c85c with record's slot in a0: keep the frame, its shadow, its flag word, the realigned stack word
   and the saved registers across record's journal *)
pose proof (proj1 HJ4) as HAR4.
pose proof HJ4 as (_ & Hly4 & _ & _ & _ & Hfrs4 & _ & _ & _ & _ & _ & _ & _ & HJ4pres & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR Hly4) as (Eab4 & Efa4 & _).
assert (EFA4 : frame_addr ly4 0 fpos = F) by (rewrite Efa4; reflexivity).
pose proof HJ4c as (_ & _ & _ & _ & _ & Hfrs4c & _). cbn [app] in Hfrs4c.
assert (Hfin4 : In (0, fpos) (frames S4)) by (rewrite Hfrs4c; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
rewrite EFA4 in HFpres4, HFSpres4. change (fs_frame_bytes 0) with 64 in HFpres4, HFSpres4. change (64 / 8) with 8 in HFSpres4.
assert (HnFP1 : forall a, inFP FPREC a -> ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ 0 <= a < alloc_ceiling).
{ intros a Hf. destruct (KLOC a (HFP1KA a Hf)) as (Hb & HnF & HnS & _). split; [exact HnF | split; [exact HnS | exact Hb]]. }
jafter_call_keep_hi HS 1060%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0;1;2;3;4]%nat HS4.
match type of HS4 with ?tq -> _ => assert (HRK : tq); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
- eapply (region_kept_fshadow_sub B E2 RECORD_STK (spZ regs + (sp1 - spZ regs)) FPREC ly S2 W (ms_mem ms3) _ ly4 S4 W4 mem4 md4 _
    1041 (SB + F / 8) _ _ _ _ _ 0 fpos HJ4c V1041 Hfin);
  [ unfold shadow_addr; fold F; rewrite <- SB_SHADOW_OFF; lia
  | unfold shadow_addr; fold F; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia
  | intros a Ha HFa; destruct (HnFP1 a HFa) as (_ & HnS & _); unfold SB in *; lia
  | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
    apply (proj1 (HFSpres4 (a - (SB + F / 8)) ltac:(unfold SB in *; lia))) ].
- eapply (region_kept_frame_sub B E2 RECORD_STK (spZ regs + (sp1 - spZ regs)) FPREC ly S2 W (ms_mem ms3) _ ly4 S4 W4 mem4 md4 _
    1028 F _ _ _ _ _ 0 fpos HJ4c V1028 Hfin);
  [ fold F; lia | fold F; change (fs_frame_bytes 0) with 64; lia
  | intros a Ha HFa; destruct (HnFP1 a HFa) as (HnF & _); lia
  | intros a Ha; lia ].
- eapply (region_kept_frame_sub B E2 RECORD_STK (spZ regs + (sp1 - spZ regs)) FPREC ly S2 W (ms_mem ms3) _ ly4 S4 W4 mem4 md4 _
    1028 F _ _ _ _ _ 0 fpos HJ4c V1028 Hfin);
  [ fold F; lia | fold F; change (fs_frame_bytes 0) with 64; lia
  | intros a Ha HFa; destruct (HnFP1 a HFa) as (HnF & _); lia
  | intros a Ha; exact (proj1 (HFpres4 a ltac:(lia))) ].
- eapply (region_kept_stack_sub SEGS B E2 RECORD_STK (spZ regs + (sp1 - spZ regs)) FPREC ly S2 W (ms_mem ms3) _
    ly4 S4 W4 mem4 md4 _ 34 _ _ _ _ _ sp1 SUP_AFTER_REPLY_STK (spZ regs) FP ly S W mem md _ _ HJ4c HJ4 V34);
  [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (HnFP1 a HFa) as (_ & _ & Hb); unfold alloc_ceiling in *; lia].
- eapply (region_kept_stack_sub SEGS B E2 RECORD_STK (spZ regs + (sp1 - spZ regs)) FPREC ly S2 W (ms_mem ms3) _
    ly4 S4 W4 mem4 md4 _ 2 _ _ _ _ _ (spZ regs) SUP_AFTER_REPLY_STK (spZ regs) FP ly S W mem md _ _ HJ4c HJ4 V2);
  [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (HnFP1 a HFa) as (_ & _ & Hb); unfold alloc_ceiling in *; lia]. }
rewrite <- restrict_mkst_fx in HS4. clear HS. rename HS4 into HS.
clear P2 P3 P4 P8 P10.
remember (havoc E2 1060 (map (getr regs4) CLOB)) as E3 eqn:HE3 in HS.
assert (HAE3 : env_agree 32 (Ereg regs (sar_extra (as_uar_cell B) sp1)) E3) by (rewrite HE3; apply env_agree_havoc_ge; [lia | exact HAE2]).
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc_hi; [exact HEI2 | unfold A_LIM; lia]).
assert (OLD3 : forall n, (n < 1060)%nat -> ew E3 n = ew E2 n) by (intros n Hn; rewrite HE3; apply ew_havoc_old; exact Hn).
assert (E1064 : ew E3 1064 = Z_to_bv 64 (rec_slot R)).
{ rewrite HE3. change 1064%nat with (1060 + 4)%nat. rewrite (ew_havoc_new E2 1060 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
unfold CLOB. cbn [map nth]. cbv zeta in HKrec. destruct HKrec as (Frec & Orec & Ha0rec & _). exact Ha0rec. }
clear HE3.
assert (X2 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact V2).
assert (X34 : bv_unsigned (ew E3 34) = sp1) by (rewrite OLD3 by lia; exact V34).
assert (X1028 : bv_unsigned (ew E3 1028) = F) by (rewrite OLD3 by lia; exact V1028).
assert (X1040 : bv_unsigned (ew E3 1040) = FL) by (rewrite OLD3 by lia; exact V1040).
assert (X1041 : bv_unsigned (ew E3 1041) = SB + F / 8) by (rewrite OLD3 by lia; exact V1041).
(* run 3: s6 := the slot, b's shadow bytes := 0, the snprintf arguments, and the call at 0x8c87c *)
paj_run_shc RUNP RUNC HS HJ4.
{ eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 1041%nat); [reflexivity | exact X1041 |
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA4; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia |].
apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 1028%nat); [reflexivity | exact X1028 |
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
left; unfold in_zr; cbn [fst snd]; rewrite EFA4; change (fs_frame_bytes 0) with 64; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite X34; lia | cbn; rewrite FS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite X2; lia | cbn; rewrite FS; lia | cbn; lia |].
apply (awr_ok_nil SEGS B). }
rename ms into ms5, mat into mat5, HF into HF5, HFr into HFr5, HG into HG5.
(* the snprintf wrapper at 0x8c87c: snprintf(b, 16, "%d", id) with b = F + 32. It is the only step that changes the
   FP state, so the walk goes on at the fx1 it returns (PaFx's srr_after_artF) *)
pose proof (proj1 HJ4) as HAR5.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ5pres & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR5 Hfin4) as (_ & _ & HFpres5 & HFSpres5).
rewrite EFA4 in HFpres5, HFSpres5. change (fs_frame_bytes 0) with 64 in HFpres5, HFSpres5. change (64 / 8) with 8 in HFSpres5.
pmkst HS.
sar_preg HS (1%bv : bv 5) Q1. sar_preg HS (2%bv : bv 5) Q2. sar_preg HS (3%bv : bv 5) Q3.
sar_preg HS (4%bv : bv 5) Q4. sar_preg HS (10%bv : bv 5) Q10. sar_preg HS (11%bv : bv 5) Q11.
sar_preg HS (12%bv : bv 5) Q12. sar_preg HS (13%bv : bv 5) Q13.
cbn [sv_denot] in Q1, Q11. rewrite (img_env_codeptr E3 HEI3 25424) in Q1.
rewrite sar_denot_off0, (OLD3 3%nat ltac:(lia)), (OLD2 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl) in Q3.
rewrite sar_denot_off0, (OLD3 4%nat ltac:(lia)), (OLD2 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl) in Q4.
rewrite sar_denot_off0, (OLD3 10%nat ltac:(lia)), (OLD2 10%nat ltac:(lia)), (EE 10%nat 10%bv eq_refl) in Q13.
rewrite sar_denot_off0 in Q2.
assert (Qsp5 : spZ (ms_regs ms5) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite Q2, X34; lia).
assert (Qd : getr (ms_regs ms5) 10 = w64 (F + 32)).
{ rewrite Q10. cbn [sv_denot]. rewrite X1028. unfold w64. reflexivity. }
assert (Qn : getr (ms_regs ms5) 11 = w64 16) by (rewrite Q11; reflexivity).
assert (Qid : getr (ms_regs ms5) 13 = w64 id) by (rewrite Q13; exact H10).
set (T := PF.pf_dec id).
assert (HTlen : Z.of_nat (length T) <= 11) by (unfold T; rewrite (sar_dec_len id Hid); pose proof (dec_length id Hid); lia).
assert (Hw : RtPFShared.sn_len 15 T = Z.of_nat (length T) + 1).
{ unfold RtPFShared.sn_len, RtPFShared.sn_bytes. rewrite length_app, length_firstn. cbn [length]. lia. }
set (w := RtPFShared.sn_len 15 T) in *.
assert (HKs : RtPFCmd.CMD_SNP_K = 8192) by (vm_compute; reflexivity).
assert (HEb : forall a, F + 32 <= a < F + 32 + w -> awr_byte SEGS B SUP_AFTER_REPLY_STK (spZ regs) FP
  (ablocks B ly S) (ablocks B ly4 S4) (frames S) ly4 [(0, fpos)] a).
{ intros a Ha. right; right; right; left. exists 0, fpos. split; [left; reflexivity|].
  left. unfold in_zr. cbn [fst snd]. rewrite EFA4. change (fs_frame_bytes 0) with 64. lia. }
eapply srr_after_artF.
{ eapply (aj_art_own_atF SEGS B LAWS pa_segs_low RtPFCmd.CMD_SNP_K (fun a => F + 32 <= a < F + 32 + w)
(SIG CS___interceptor_trampoline_snprintf) W4 (ms_regs ms5) (ms_mem ms5) SUP_AFTER_REPLY_STK (spZ regs) FP ly S W mem md
[(0, fpos)] ly4 S4 _ _ (sp1 - spZ regs) (getr (ms_regs ms5) 1) _ HJ4 Qsp5 Hsp1b ltac:(lia)
ltac:(rewrite HKs; lia) ltac:(rewrite HKs, FS; lia) eq_refl HEb).
(* the read-only bytes and the recorder's state at the call *)
assert (HROD5 : arodata_okP SEGS RLO RHI B (rdW W4 (ms_mem ms5))).
{ apply (CRODK ly S W mem md ly4 S4 W4 (ms_mem ms5) _ SUP_AFTER_REPLY_STK (spZ regs) FP [(0, fpos)] _ HAR HJ4); [|exact HROD].
  intros a Hf. destruct (HFPKA a Hf) as [Ha | [Ha | (p & n & Hpn & Hpa)]].
  - left. exact (sar_in_PG a (or_introl Ha)).
  - left. exact (sar_in_PG a (or_intror Ha)).
  - right. exists p, n. split; [apply in_or_app; left; exact Hpn | exact Hpa]. }
pose proof (CROOK ly4 S4 W4 (ms_mem ms5) _ HAR5 HROD5) as HRO5.
destruct (CCELLS ly4 S4 W4 (ms_mem ms5) _ HAR5) as (_ & (Hgw & (cval & Hcv)) & _).
pose proof HFoff as HFlo. unfold off_img in HFlo.
(* the read-only words the chain reads: the two non-writable load segments (RtPFCmd.v CMD_SNP_CR), inside the image *)
assert (HCRB : Forall (fun r => 0x10000 <= fst r /\ fst r + snd r <= 0xa5000) RtPFCmd.CMD_SNP_CR)
  by (apply (sar_ranges_bnds _ 0x10000 0xa5000); vm_compute; reflexivity).
assert (HSNPD : Forall (fun r => Forall (zdisjoint r) (RtPFShared.snp_out RtPFCmd.CMD_SNP_K (spZ (ms_regs ms5)) (F + 32) w))
  RtPFCmd.CMD_SNP_CR).
{ apply Forall_impl with (2 := HCRB). intros r (Hlo & Hhi).
  apply RtPFSx.Forall_snp. unfold zdisjoint. cbn [fst snd]. rewrite Qsp5, HKs. destruct HFlo as [Hl | Hl]; split; lia. }
apply (srr_art_postF_of_pf SEGS B RtPFCmd.CMD_SNP_K ly4 S4 W4 (ms_regs ms5) (ms_mem ms5) _ _ (F + 32) w
(RtPFShared.sn_bytes 15 T) (Z.of_nat (length T)));
[ intros a Ha; apply HJ5pres; rewrite Qsp5, HKs in *; rewrite FS; lia |].
pose proof Hly4 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop4 & Eslo4 & Eshi4 & _).
assert (E292 : bv_unsigned (ew E3 (A_OBJ 51)) = 0x21f40)
  by (rewrite (HEI3 (A_OBJ 51) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); exact (sar_obj51 VOBJS)).
assert (Qf : getr (ms_regs ms5) 12 = w64 0x21f40).
{ rewrite Q12. cbn [sv_denot]. change 292%nat with (A_OBJ 51). rewrite E292, Z.add_0_r. reflexivity. }
(* b's shadow bytes (granules 4 and 5 of the frame) are zero: the run unpoisoned them at 0x8c860 *)
assert (ZS4 : rdW W4 (ms_mem ms5) (SB + F / 8 + 4) = Some 0).
{ sar_bfind HS E3 (w_H W4) ms5 1041%nat;
  [ exact X1041 | repeat (first [left; reflexivity | right]) | reflexivity | lia ]. }
assert (ZS5 : rdW W4 (ms_mem ms5) (SB + F / 8 + 5) = Some 0).
{ sar_bfind HS E3 (w_H W4) ms5 1041%nat;
  [ exact X1041 | repeat (first [left; reflexivity | right]) | reflexivity | lia ]. }
assert (HF64d : F mod 64 = 0) by exact HF64.
change (16 - 1) with 15. fold w.
apply (ASNPRINTF fx ly4 S4 W4 (ms_regs ms5) (ms_mem ms5) _ (F + 32) 16 0x21f40 []
(map (argZ (ms_regs ms5)) [3; 4; 5; 6; 7]) T cval).
- eapply (ecall_pre_at SEGS B SUP_AFTER_REPLY_STK (spZ regs) FP ly S W mem md [(0, fpos)] ly4 S4 W4
    (ms_mem ms5) _ _ (ms_regs ms5) (sp1 - spZ regs) HJ4 Qsp5 Hsp1b ltac:(lia) ltac:(rewrite FS; lia));
  [ rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity] | rewrite Q3; exact Hgp | rewrite Q4; exact Htp ].
- rewrite Qsp5, HKs, Eslo4. rewrite FS in Hslo. lia.
- intros a Ha. rewrite Qsp5, HKs in Ha. apply HJ5pres. rewrite FS. lia.
- exact Qd.
- exact Qn.
- exact Qf.
- exact (CCVS RLO RHI W4 (ms_mem ms5) HROD5).
- apply sar_ranges_bounded. vm_compute. reflexivity.
- exact HSNPD.
- exact Hgw.
- exact Hcv.
- lia.
- lia.
- lia.
- lia.
- change (16 - 1) with 15; fold w; unfold RtPFShared.snp_out; repeat apply Forall_cons; try apply Forall_nil;
  unfold zdisjoint; cbn [fst snd]; rewrite ?Qsp5, ?HKs; destruct HFlo as [Hl | Hl]; lia.
- change (16 - 1) with 15; fold w; unfold RtPFShared.snp_out; repeat apply Forall_cons; try apply Forall_nil;
  unfold zdisjoint; cbn [fst snd]; rewrite ?Qsp5, ?HKs; destruct HFlo as [Hl | Hl]; lia.
- split; [reflexivity | intros i Hi; cbn [length] in Hi; lia].
- cbn [length]. rewrite Qsp5. lia.
- change (16 - 1) with 15; fold w; unfold RtPFShared.snp_out; repeat apply Forall_cons; try apply Forall_nil;
  unfold zdisjoint; cbn [fst snd length]; rewrite ?Qsp5, ?HKs; destruct HFlo as [Hl | Hl]; lia.
- apply (RtPFCmd.FR_cmd_intro _ _ _ _ _ PAI.AI_FMT PAI.AI_PS [PF.AInt id]).
  + apply (sar_fmt_at B HB ly4 S4 W4 (ms_mem ms5) _ _ HAR5 HRO5).
    change (16 - 1) with 15; fold w; unfold RtPFShared.snp_out; repeat apply Forall_cons; try apply Forall_nil;
    cbn [fst snd]; rewrite ?Qsp5, ?HKs; destruct HFlo as [Hl | Hl]; lia.
  + exact PAI.ai_parse.
  + cbn [map RtPFCmd.arg_of RtPFShared.pf_args_asan]. split; [|exact I].
    cbn [RtPFShared.pf_arg_asan]. split; [exact Hid|].
    unfold argZ.
    replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
    rewrite Qid. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). symmetry. apply Znumtheory.Zmod_div_mod; [lia | lia | exists (2 ^ 32); reflexivity].
  + exact (PAI.ai_text id).
  + cbn. exact I.
  + vm_compute. reflexivity.
- lia.
- lia.
- change (16 - 1) with 15; fold w; lia.
- change (16 - 1) with 15; fold w; lia.
- change (16 - 1) with 15; fold w; unfold RtPFShared.snp_out; cbn [pairwise]; split; [|split; [apply Forall_nil | exact I]];
  repeat apply Forall_cons; try apply Forall_nil;
  unfold zdisjoint; cbn [fst snd]; rewrite ?Qsp5, ?HKs; destruct HFlo as [Hl | Hl]; lia.
- change (16 - 1) with 15; fold w; intros a Ha. split; [apply (apresent_writable SEGS); exact (proj1 (HFpres5 a ltac:(lia)))|].
  split; [exact (proj2 (HFpres5 a ltac:(lia)))|]. rewrite Qsp5. rewrite FS in Hslo. lia.
- change (16 - 1) with 15; fold w; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
- change (16 - 1) with 15; fold w; intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
  assert (Hq : x / 8 = F / 8 + 4 \/ x / 8 = F / 8 + 5) by (Z.div_mod_to_equations; lia).
  destruct Hq as [Hq | Hq]; rewrite Hq.
  + replace (SHADOW_OFF + (F / 8 + 4)) with (SB + F / 8 + 4) by (rewrite <- SB_SHADOW_OFF; lia). exact ZS4.
  + replace (SHADOW_OFF + (F / 8 + 5)) with (SB + F / 8 + 5) by (rewrite <- SB_SHADOW_OFF; lia). exact ZS5.
- change (16 - 1) with 15; fold w; apply (shadow_hull_vis_of_frame SEGS B LAWS ly4 S4 W4 (ms_mem ms5) _ 0 fpos (F + 32) w HAR5 Hfin4);
  [rewrite EFA4; lia | rewrite EFA4; change (fs_frame_bytes 0) with 64; lia | lia].
- change (16 - 1) with 15; fold w; unfold zdisjoint, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI. cbn [fst snd].
  destruct HFlo as [Hl | Hl]; lia.
- exact HFRM. }
(* back at 0x8c880 at the FP state fx1 the wrapper returned: the walk goes on there *)
intros fx1 regs6 mem6 md6 Hfx (HJ6 & HP6 & (HQ10 & HQby) & HFR6).
rewrite Q1.
pose proof (proj1 HJ6) as HAR6.
pose proof HJ6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ6pres & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR6 Hfin4) as (_ & _ & HFpres6 & HFSpres6).
rewrite EFA4 in HFpres6, HFSpres6. change (fs_frame_bytes 0) with 64 in HFpres6, HFSpres6. change (64 / 8) with 8 in HFSpres6.
pose proof (SRr_run_pi_AJ (L := cmd_listing) (fx := fx1) B LAWS) as RUNP1.
pose proof (SRr_run_pi_AJ_call (L := cmd_listing) (fx := fx1) B LAWS) as RUNC1.
jafter_call_keep_hi HS 1080%nat regs6 (mrestrict (w_H W4) mem6) HP6 [0;1;2;3;4]%nat HS6.
match type of HS6 with ?tq -> _ => assert (HRK : tq); [|specialize (HS6 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
- eapply sar_region_kept_hi2;
  [ exact X1041
  | intros a Ha; apply HFR6; [unfold SB in *; lia | rewrite ?Qsp5, HKs; unfold SB in *; lia | unfold SB in *; lia]
  | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
    exact (proj1 (HFSpres6 (a - (SB + F / 8)) ltac:(unfold SB in *; lia))) ].
- eapply sar_region_kept_hi2;
  [ exact X1028
  | intros a Ha; apply HFR6; [lia | rewrite ?Qsp5, HKs; lia | lia]
  | intros a Ha; lia ].
- eapply sar_region_kept_hi2;
  [ exact X1028
  | intros a Ha; apply HFR6; [lia | rewrite ?Qsp5, HKs; lia | lia]
  | intros a Ha; exact (proj1 (HFpres6 a ltac:(lia))) ].
- eapply sar_region_kept_hi2;
  [ exact X34
  | intros a Ha; apply HFR6; [lia | rewrite ?Qsp5, HKs; lia | lia]
  | intros a Ha; apply HJ6pres; rewrite FS; lia ].
- eapply sar_region_kept_hi2;
  [ exact X2
  | intros a Ha; apply HFR6; [lia | rewrite ?Qsp5, HKs; lia | lia]
  | intros a Ha; apply HJ6pres; rewrite FS; lia ]. }
rewrite <- restrict_mkst_fx in HS6.
pose proof (st_ok_pi_restrict_xfx fx fx1 _ _ _ _ _ _ _ _ _ HS6) as HS7. clear HS HS6. rename HS7 into HS.
remember (havoc E3 1080 (map (getr regs6) CLOB)) as E4 eqn:HE4 in HS.
assert (HAE4 : env_agree 32 (Ereg regs (sar_extra (as_uar_cell B) sp1)) E4) by (rewrite HE4; apply env_agree_havoc_ge; [lia | exact HAE3]).
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc_hi; [exact HEI3 | unfold A_LIM; lia]).
assert (OLD4 : forall n, (n < 1080)%nat -> ew E4 n = ew E3 n) by (intros n Hn; rewrite HE4; apply ew_havoc_old; exact Hn).
clear HE4.
assert (Y2 : bv_unsigned (ew E4 2) = spZ regs) by (rewrite OLD4 by lia; exact X2).
assert (Y34 : bv_unsigned (ew E4 34) = sp1) by (rewrite OLD4 by lia; exact X34).
assert (Y1028 : bv_unsigned (ew E4 1028) = F) by (rewrite OLD4 by lia; exact X1028).
assert (Y1040 : bv_unsigned (ew E4 1040) = FL) by (rewrite OLD4 by lia; exact X1040).
assert (Y1041 : bv_unsigned (ew E4 1041) = SB + F / 8) by (rewrite OLD4 by lia; exact X1041).
assert (Y1064 : ew E4 1064 = Z_to_bv 64 (rec_slot R)) by (rewrite OLD4 by lia; exact E1064).
(* run 4: a0 := the slot, a1 := b, and the call of arg_s at 0x8c888 *)
paj_run_shc RUNP1 RUNC1 HS HJ6.
{ eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 1041%nat); [reflexivity | exact Y1041 |
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA4; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia |].
apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 1028%nat); [reflexivity | exact Y1028 |
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
left; unfold in_zr; cbn [fst snd]; rewrite EFA4; change (fs_frame_bytes 0) with 64; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite Y34; lia | cbn; rewrite FS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Y2; lia | cbn; rewrite FS; lia | cbn; lia |].
apply (awr_ok_nil SEGS B). }
rename ms into ms7, mat into mat7, HF into HF7, HFr into HFr7, HG into HG7.
(* the facts the two arg_s calls need at this state *)
pose proof (proj1 HJ6) as HAR7.
pose proof HJ6 as (_ & Hly4b & _ & _ & _ & _ & Hnev7 & _ & _ & _ & _ & _ & _ & HJ7pres & _).
pose proof Hly4b as (_ & _ & _ & _ & _ & _ & _ & _ & Etop4b & Eslo4b & Eshi4b & _).
assert (K45 : forall a, KA a -> rdW W4 (ms_mem ms5) a = rdW W4 mem4 a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & HnS & _).
  apply (sar_aview_frame_pt E3 _ (w_H W4) mem4 (ms_mem ms5) a HFr5); [lia|].
  sar_nwin ltac:(fun H => rewrite ?X2, ?X34, ?X1028, ?X1041 in H; unfold SB in *; lia). }
assert (K56 : forall a, KA a -> rdW W4 mem6 a = rdW W4 (ms_mem ms5) a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & HnS & _).
  apply HFR6; [lia | rewrite ?Qsp5, HKs; lia | lia]. }
assert (K67 : forall a, KA a -> rdW W4 (ms_mem ms7) a = rdW W4 mem6 a).
{ intros a Ha. destruct (KLOC a Ha) as (Hb & HnF & HnS & _).
  apply (sar_aview_frame_pt E4 _ (w_H W4) mem6 (ms_mem ms7) a HFr7); [lia|].
  sar_nwin ltac:(fun H => rewrite ?Y2, ?Y34, ?Y1028, ?Y1041 in H; unfold SB in *; lia). }
assert (K47 : forall a, KA a -> rdW W4 (ms_mem ms7) a = rdW W4 mem4 a)
  by (intros a Ha; rewrite (K67 a Ha), (K56 a Ha); exact (K45 a Ha)).
cbv zeta in HKrec.
destruct HKrec as (Frec & O1 & Ha0rec & HpermF & HlenF & HFO & GREP & GO & GBB & GMLE).
assert (HO1O : forall pn, In pn O1 -> In pn O) by (intros pn Hpn; exact (proj1 (proj1 (GO pn) Hpn))).
assert (HO1b : forall pn, In pn O1 -> In pn (ablocks B ly4 S4)).
{ intros pn Hpn. destruct (proj1 (GO pn) Hpn) as (HinO & HnF).
  pose proof (HOB pn HinO) as Hin0. rewrite <- Eab in Hin0.
  pose proof (Permutation_in pn HpermF Hin0) as Hin1. apply in_app_iff in Hin1 as [H1 | H1]; [exact H1 | exfalso; exact (HnF H1)]. }
assert (HREP7 : rec_repA B ly4 S4 (rdW W4 (ms_mem ms7)) (rec_record R 19 []) O1).
{ apply (sar_rec_repA_kept B ly4 S4 (rdW W4 mem4) ly4 S4 (rdW W4 (ms_mem ms7)) _ O1 GREP HO1b).
  - intros a Ha. apply K47. left. unfold REC_SIZE. exact Ha.
  - intros a Ha. apply K47. right. left. unfold SC_SIZE. exact Ha.
  - intros p n i Hpn Hi. apply K47. right. right. exists p, n.
    split; [exact (HOB (p, n) (HO1O (p, n) Hpn))|]. unfold req_size. destruct (Z.eqb_spec n 0); lia. }
assert (HROD7 : arodata_okP SEGS RLO RHI B (rdW W4 (ms_mem ms7))).
{ apply (CRODK ly S W mem md ly4 S4 W4 (ms_mem ms7) _ SUP_AFTER_REPLY_STK (spZ regs) FP [(0, fpos)] _ HAR HJ6); [|exact HROD].
  intros a Hf. destruct (HFPKA a Hf) as [Ha | [Ha | (p & n & Hpn & Hpa)]].
  - left. exact (sar_in_PG a (or_introl Ha)).
  - left. exact (sar_in_PG a (or_intror Ha)).
  - right. exists p, n. split; [apply in_or_app; left; exact Hpn | exact Hpa]. }
pose proof (CROOK ly4 S4 W4 (ms_mem ms7) _ HAR7 HROD7) as HRO7.
(* b holds dec id, in the frame, with its word tail readable *)
assert (HBY7 : forall i, 0 <= i < Z.of_nat (length T) + 1 ->
  rdW W4 (ms_mem ms7) (F + 32 + i) = Some (nth (Z.to_nat i) (T ++ [0]) 0)).
{ intros i Hi. rewrite (sar_aview_frame_pt E4 _ (w_H W4) mem6 (ms_mem ms7) (F + 32 + i) HFr7);
  [ | lia | sar_nwin ltac:(fun H => rewrite ?Y2, ?Y34, ?Y1028, ?Y1041 in H; unfold SB in *; lia) ].
  rewrite (HQby i ltac:(lia)). f_equal.
  unfold RtPFShared.sn_bytes. rewrite firstn_all2 by lia. reflexivity. }
assert (HSTR7 : astr_atR (rdW W4 (ms_mem ms7)) (F + 32) (dec id))
  by (apply (sar_dec_bridge _ _ id Hid); exact HBY7).
assert (ZS4b : rdW W4 (ms_mem ms7) (SB + F / 8 + 4) = Some 0).
{ sar_bfind HS E4 (w_H W4) ms7 1041%nat; [exact Y1041 | repeat (first [left; reflexivity | right]) | reflexivity | lia]. }
assert (ZS5b : rdW W4 (ms_mem ms7) (SB + F / 8 + 5) = Some 0).
{ sar_bfind HS E4 (w_H W4) ms7 1041%nat; [exact Y1041 | repeat (first [left; reflexivity | right]) | reflexivity | lia]. }
assert (HRAB : range_addressable (rdW W4 (ms_mem ms7)) SHADOW_OFF (F + 32) (Z.of_nat (length (dec id)) + 1)).
{ intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
  pose proof (dec_length id Hid) as Hdl.
  assert (Hq : x / 8 = F / 8 + 4 \/ x / 8 = F / 8 + 5) by (Z.div_mod_to_equations; lia).
  destruct Hq as [Hq | Hq]; rewrite Hq;
  [ replace (SHADOW_OFF + (F / 8 + 4)) with (SB + F / 8 + 4) by (rewrite <- SB_SHADOW_OFF; lia); exact ZS4b
  | replace (SHADOW_OFF + (F / 8 + 5)) with (SB + F / 8 + 5) by (rewrite <- SB_SHADOW_OFF; lia); exact ZS5b ]. }
assert (HFOBJ : afobj SEGS B ly4 S4 W4 (ms_mem ms7) (F + 32) (Z.of_nat (length (dec id)) + 1)).
{ split; [|split; [| exact HRAB]].
  - exists 0, fpos. split; [exact Hfin4|]. split; [lia|]. rewrite EFA4.
    pose proof (dec_length id Hid) as Hdl. split; [exact HF8m|]. split; [lia | change (fs_frame_bytes 0) with 64; lia].
  - pose proof (dec_length id Hid). Z.div_mod_to_equations. lia. }
assert (HTAILB : atail_vis SEGS W4 (ms_mem ms7) (F + 32 + Z.of_nat (length (dec id))))
  by exact (CFOBJT ly4 S4 W4 (ms_mem ms7) _ (F + 32) (dec id) HAR7 HFOBJ HSTR7).
(* the call of arg_s(slot, b) at 0x8c888 *)
assert (SIGARG : SIG CS_arg_s = BASE + AF_arg_s) by (exact (sar_sig_arg_s SIGP)).
pmkst HS. rewrite SIGARG.
sar_preg HS (1%bv : bv 5) A1. sar_preg HS (2%bv : bv 5) A2. sar_preg HS (3%bv : bv 5) A3.
sar_preg HS (4%bv : bv 5) A4. sar_preg HS (8%bv : bv 5) A8. sar_preg HS (10%bv : bv 5) A10.
sar_preg HS (11%bv : bv 5) A11.
cbn [sv_denot] in A1. rewrite (img_env_codeptr E4 HEI4 25436) in A1.
rewrite sar_denot_off0, (OLD4 3%nat ltac:(lia)), (OLD3 3%nat ltac:(lia)), (OLD2 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl) in A3.
rewrite sar_denot_off0, (OLD4 4%nat ltac:(lia)), (OLD3 4%nat ltac:(lia)), (OLD2 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl) in A4.
rewrite sar_denot_off0 in A2, A8, A10.
assert (QspA : spZ (ms_regs ms7) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite A2, Y34; lia).
assert (QaA : getr (ms_regs ms7) 10 = w64 (rec_slot R)) by (rewrite A10, Y1064; reflexivity).
assert (QbA : getr (ms_regs ms7) 11 = w64 (F + 32)) by (rewrite A11; cbn [sv_denot]; rewrite Y1028; reflexivity).
assert (WRA7 : rdword (rdW W4 (ms_mem ms7)) (spZ regs + -8) = Some (raZ regs)).
{ sar_wfind HS E4 (w_H W4) ms7 2%nat;
  [ exact Y2 | repeat (first [left; reflexivity | right])
  | rewrite sar_denot_off0, (OLD4 1%nat ltac:(lia)), (OLD3 1%nat ltac:(lia)), (OLD2 1%nat ltac:(lia)), (EE 1%nat 1%bv eq_refl);
    unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
  | unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr; exact Hr ]. }
assert (WS07 : rdword (rdW W4 (ms_mem ms7)) (spZ regs + -16) = Some (s0Z regs)).
{ sar_wfind HS E4 (w_H W4) ms7 2%nat;
  [ exact Y2 | repeat (first [left; reflexivity | right])
  | rewrite sar_denot_off0, (OLD4 8%nat ltac:(lia)), (OLD3 8%nat ltac:(lia)), (OLD2 8%nat ltac:(lia)), (EE 8%nat 8%bv eq_refl);
    unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
  | unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr; exact Hr ]. }
assert (Hab7 : forall a, spZ regs <= a < 2 ^ 64 -> rdW W4 (ms_mem ms7) a = rdW W mem a).
{ intros a Ha. apply (aview_above_of_journal (PI := PI) B SUP_AFTER_REPLY_STK (spZ regs) FP ly S W mem md
    [(0, fpos)] ly4 S4 W4 (ms_mem ms7) _ _ HJ6 a Ha).
  intros Hf. destruct (KLOC a (HFPKA a Hf)) as (Hb & _). unfold alloc_ceiling in *. lia. }
assert (HCHA : exists chA, achain ly4 (rdW W4 (ms_mem ms7)) (spZ regs + (sp1 - spZ regs)) (s0Z (ms_regs ms7)) chA).
{ assert (Es0A : s0Z (ms_regs ms7) = spZ regs) by (unfold s0Z; rewrite A8; exact Y2). rewrite Es0A.
  destruct (sar_chain_at ly (rdW W mem) (rdW W4 (ms_mem ms7)) (spZ regs) (s0Z regs) (raZ regs) ch
    (spZ regs + (sp1 - spZ regs)) Hch ltac:(lia) ltac:(lia) Hab7
    ltac:(replace (spZ regs - 8) with (spZ regs + -8) by lia; exact WRA7)
    ltac:(replace (spZ regs - 16) with (spZ regs + -16) by lia; exact WS07)
    Hra4 ltac:(lia) ltac:(apply sar_mod_16_8; exact Hal16) ltac:(lia)) as (chA & HchA).
  exists chA. exact (achain_ly_top ly ly4 _ _ _ _ Etop4b HchA). }
destruct HCHA as (chA & HCHA).
set (FPA := if Z.of_nat (length (@nil (list byte))) <? REC_ARGS_MAX
            then [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
                  (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))),
                   rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))) + 8)]
            else []).
assert (HFPAgs : forall a, inFP FPA a ->
  (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE)).
{ intros a (r & Hr & Hrq). unfold FPA in Hr. cbn in Hr.
  destruct Hslotr as [[Hlo Hhi] | Heq];
  [ left; destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hrq;
    unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE, REC_SIZE, OFF_CALLS in *; lia
  | right; destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hrq;
    rewrite Heq in Hrq; unfold CALL_OFF_NARGS, CALL_OFF_ARGS, SC_SIZE in *; lia ]. }
assert (HFPAKA : forall a, inFP FPA a -> KA a)
  by (intros a Hf; destruct (HFPAgs a Hf) as [Ha | Ha]; [left; exact Ha | right; left; exact Ha]).
assert (HFPAwr : forall a, inFP FPA a -> awr_byte SEGS B SUP_AFTER_REPLY_STK (spZ regs) FP
  (ablocks B ly S) (ablocks B ly4 S4) (frames S) ly4 [(0, fpos)] a).
{ intros a Hf. right; right; right; right; left.
  destruct (HFPAgs a Hf) as [Ha | Ha].
  - split; [exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity | cbn [fst snd]; lia]|].
    rewrite sar_ts_prog. split; [exact (sar_in_PG a (or_introl Ha)) | exact (CPIMG a (sar_in_PG a (or_introl Ha)))].
  - split; [exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split; [right; left; reflexivity | cbn [fst snd]; lia]|].
    rewrite sar_ts_prog. split; [exact (sar_in_PG a (or_intror Ha)) | exact (CPIMG a (sar_in_PG a (or_intror Ha)))]. }
assert (HNEVA : st_nev S4 + EV_ARG_S <= EV_MAX).
{ unfold EV_SUP_AFTER_REPLY in Hev. unfold EV_ARG_S, EV_XMALLOC in *. lia. }
assert (HLIVEA : blocks_bytes S4 + LIVE_ARG_S (Some (dec id)) <= LIVE_MAX).
{ assert (EBB2 : blocks_bytes S2 = blocks_bytes S) by (rewrite ES2; reflexivity).
  unfold LIVE_SUP_AFTER_REPLY in Hlive. unfold LIVE_ARG_S, LIVE_XMALLOC in *. lia. }
assert (HMOKA : mo_ok MT S4 (XM_ARG_S MT (Some (dec id)))).
{ apply (mok_station MT S2 S4 (XM_SUP_AFTER_REPLY MT R id verb) (XM_RECORD MT R) (XM_ARG_S MT (Some (dec id))) MTL HMOKS2 GMLE);
  [exact (proj1 HXMnn) | unfold XM_SUP_AFTER_REPLY; pose proof (proj2 HXMnn); lia]. }
assert (HARGV : astr_argA B ly4 S4 (rdW W4 (ms_mem ms7)) (in_roP SEGS RLO RHI) [] (F + 32) (Some (dec id)) \/
  (exists x, Some (dec id) = Some x /\ astr_atR (rdW W4 (ms_mem ms7)) (F + 32) x /\
   Z.of_nat (length x) + 1 <= LMAX + 1 /\ afobj SEGS B ly4 S4 W4 (ms_mem ms7) (F + 32) (Z.of_nat (length x) + 1))).
{ right. exists (dec id). split; [reflexivity|]. split; [exact HSTR7|].
  split; [pose proof (dec_length id Hid); unfold LMAX; lia | exact HFOBJ]. }
assert (HARGT : forall x, Some (dec id) = Some x -> atail_vis SEGS W4 (ms_mem ms7) (F + 32 + Z.of_nat (length x)))
  by (intros x Hx; injection Hx as <-; exact HTAILB).
assert (HARGSTK : ARG_S_STK = 16464) by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callS_wide (fx := fx1) B LAWS W4 (ms_regs ms7) (ms_mem ms7) (Z_to_bv 64 (BASE + AF_arg_s))
SUP_AFTER_REPLY_STK (spZ regs) FP ly S W mem md [(0, fpos)] ly4 S4 _ _ ARG_S_STK FPA EV_ARG_S (sp1 - spZ regs)
(getr (ms_regs ms7) 1) chA _ HJ6 QspA Hsp1b);
[ lia | rewrite HARGSTK; lia | rewrite HARGSTK, FS; lia | rewrite A3; exact Hgp | rewrite A4; exact Htp | reflexivity
| rewrite A1; apply ret_ok_codeptr_v; [lia | reflexivity]
| rewrite A1, unsigned_lit_small by lia; lia
| exact HCHA
| intros HPREA; exact (TARG_S fx1 ly4 S4 W4 (ms_regs ms7) (ms_mem ms7) _ chA (rec_slot R) (F + 32) 19 []
    (Some (dec id)) R O1 HPREA HROD7 HRO7 QaA QbA eq_refl HREP7 HARGV HARGT HNEVA HLIVEA HMOKA)
| exact HFPAwr
| intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hwa _; exfalso;
  destruct (KLOC a (HFPAKA a Ha)) as (Hb & _); rewrite FS in Hwa; unfold alloc_ceiling in *; lia ]. }
cbv beta. intros W8 c8 Hwle8 (ly8 & S8 & regs8 & mem8 & md8 & -> & HJ8 & HJ8c & HP8 & HKarg1).
rewrite A1.
(* back at 0x8c88c: keep the frame, its shadow, its flag word, the realigned stack word and the saved registers
   across arg_s's journal *)
pose proof (proj1 HJ8) as HAR8.
pose proof HJ8 as (_ & Hly8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ8pres & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly8 HAR Hly8) as (Eab8 & Efa8 & _).
assert (EFA8 : frame_addr ly8 0 fpos = F) by (rewrite Efa8; reflexivity).
pose proof HJ8c as (_ & _ & _ & _ & _ & Hfrs8c & _). cbn [app] in Hfrs8c.
assert (Hfin8 : In (0, fpos) (frames S8)) by (rewrite Hfrs8c; exact Hfin4).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR8 Hfin8) as (_ & _ & HFpres8 & HFSpres8).
rewrite EFA8 in HFpres8, HFSpres8. change (fs_frame_bytes 0) with 64 in HFpres8, HFSpres8. change (64 / 8) with 8 in HFSpres8.
assert (HnFPA : forall a, inFP FPA a -> ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ 0 <= a < alloc_ceiling).
{ intros a Hf. destruct (KLOC a (HFPAKA a Hf)) as (Hb & HnF & HnS & _). split; [exact HnF | split; [exact HnS | exact Hb]]. }
jafter_call_keep_hi HS 1100%nat regs8 (mrestrict (w_H W8) mem8) HP8 [0;1;2;3;4]%nat HS8.
match type of HS8 with ?tq -> _ => assert (HRK : tq); [|specialize (HS8 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
- eapply (region_kept_fshadow_sub B E4 ARG_S_STK (spZ regs + (sp1 - spZ regs)) FPA ly4 S4 W4 (ms_mem ms7) _ ly8 S8 W8 mem8 md8 _
    1041 (SB + F / 8) _ _ _ _ _ 0 fpos HJ8c Y1041 Hfin4);
  [ unfold shadow_addr; rewrite EFA4; rewrite <- SB_SHADOW_OFF; lia
  | unfold shadow_addr; rewrite EFA4; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia
  | intros a Ha HFa; destruct (HnFPA a HFa) as (_ & HnS & _); unfold SB in *; lia
  | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
    apply (proj1 (HFSpres8 (a - (SB + F / 8)) ltac:(unfold SB in *; lia))) ].
- eapply (region_kept_frame_sub B E4 ARG_S_STK (spZ regs + (sp1 - spZ regs)) FPA ly4 S4 W4 (ms_mem ms7) _ ly8 S8 W8 mem8 md8 _
    1028 F _ _ _ _ _ 0 fpos HJ8c Y1028 Hfin4);
  [ rewrite EFA4; lia | rewrite EFA4; change (fs_frame_bytes 0) with 64; lia
  | intros a Ha HFa; destruct (HnFPA a HFa) as (HnF & _); lia
  | intros a Ha; lia ].
- eapply (region_kept_frame_sub B E4 ARG_S_STK (spZ regs + (sp1 - spZ regs)) FPA ly4 S4 W4 (ms_mem ms7) _ ly8 S8 W8 mem8 md8 _
    1028 F _ _ _ _ _ 0 fpos HJ8c Y1028 Hfin4);
  [ rewrite EFA4; lia | rewrite EFA4; change (fs_frame_bytes 0) with 64; lia
  | intros a Ha HFa; destruct (HnFPA a HFa) as (HnF & _); lia
  | intros a Ha; exact (proj1 (HFpres8 a ltac:(lia))) ].
- eapply (region_kept_stack_sub SEGS B E4 ARG_S_STK (spZ regs + (sp1 - spZ regs)) FPA ly4 S4 W4 (ms_mem ms7) _
    ly8 S8 W8 mem8 md8 _ 34 _ _ _ _ _ sp1 SUP_AFTER_REPLY_STK (spZ regs) FP ly S W mem md _ _ HJ8c HJ8 Y34);
  [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (HnFPA a HFa) as (_ & _ & Hb); unfold alloc_ceiling in *; lia].
- eapply (region_kept_stack_sub SEGS B E4 ARG_S_STK (spZ regs + (sp1 - spZ regs)) FPA ly4 S4 W4 (ms_mem ms7) _
    ly8 S8 W8 mem8 md8 _ 2 _ _ _ _ _ (spZ regs) SUP_AFTER_REPLY_STK (spZ regs) FP ly S W mem md _ _ HJ8c HJ8 Y2);
  [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (HnFPA a HFa) as (_ & _ & Hb); unfold alloc_ceiling in *; lia]. }
rewrite <- restrict_mkst_fx in HS8. clear HS. rename HS8 into HS.
clear A2 A3 A4 A8 A10 A11.
remember (havoc E4 1100 (map (getr regs8) CLOB)) as E5 eqn:HE5 in HS.
assert (HAE5 : env_agree 32 (Ereg regs (sar_extra (as_uar_cell B) sp1)) E5) by (rewrite HE5; apply env_agree_havoc_ge; [lia | exact HAE4]).
assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc_hi; [exact HEI4 | unfold A_LIM; lia]).
assert (OLD5 : forall n, (n < 1100)%nat -> ew E5 n = ew E4 n) by (intros n Hn; rewrite HE5; apply ew_havoc_old; exact Hn).
clear HE5.
assert (Z2 : bv_unsigned (ew E5 2) = spZ regs) by (rewrite OLD5 by lia; exact Y2).
assert (Z34 : bv_unsigned (ew E5 34) = sp1) by (rewrite OLD5 by lia; exact Y34).
assert (Z1028 : bv_unsigned (ew E5 1028) = F) by (rewrite OLD5 by lia; exact Y1028).
assert (Z1040 : bv_unsigned (ew E5 1040) = FL) by (rewrite OLD5 by lia; exact Y1040).
assert (Z1041 : bv_unsigned (ew E5 1041) = SB + F / 8) by (rewrite OLD5 by lia; exact Y1041).
assert (Z1064 : ew E5 1064 = Z_to_bv 64 (rec_slot R)) by (rewrite OLD5 by lia; exact Y1064).
(* run 5: b's shadow bytes := 0xf8 again, a0 := the slot, a1 := the verb, and the call of arg_s at 0x8c89c *)
paj_run_shc RUNP1 RUNC1 HS HJ8.
{ eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 1041%nat); [reflexivity | exact Z1041 |
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA8; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia |].
apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 1028%nat); [reflexivity | exact Z1028 |
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
left; unfold in_zr; cbn [fst snd]; rewrite EFA8; change (fs_frame_bytes 0) with 64; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 34%nat) (d := sp1 - spZ regs); [reflexivity | rewrite Z34; lia | cbn; rewrite FS; lia | cbn; lia |].
eapply (awr_ok_cons_stack_off SEGS B) with (n := 2%nat) (d := 0); [reflexivity | rewrite Z2; lia | cbn; rewrite FS; lia | cbn; lia |].
apply (awr_ok_nil SEGS B). }
rename ms into ms9, mat into mat9, HF into HF9, HFr into HFr9, HG into HG9.
(* arg_s's first post: one fresh block (dec id and its NUL), recorded as the call's first argument *)
cbv zeta in HKarg1.
destruct HKarg1 as (GBB8 & GMLE8 & [(Hc6 & _) | (_ & p1 & Hp1 & HPerm8 & HAp1 & GREP8)]);
  [ cbn [length Z.of_nat] in Hc6; unfold REC_ARGS_MAX in Hc6; lia | ].
set (n1 := Z.of_nat (length (sarg (Some (dec id)))) + 1) in *.
destruct HVERB as (xv & Hverb & (qv & kv & Hqv & Hqv1 & Hqv2) & HSTRV & HLENV & HAPV).
assert (Hqv4 : In (qv, kv) (ablocks B ly4 S4)).
{ assert (Hq0 : In (qv, kv) (ablocks B ly S2)) by (rewrite Eab; exact Hqv).
  pose proof (Permutation_in _ HpermF Hq0) as Hq1. apply in_app_iff in Hq1 as [H1 | H1]; [exact H1|].
  exfalso. pose proof (HFO _ H1) as HqO. rewrite Forall_forall in HAPV. specialize (HAPV _ HqO). unfold iv_apart in HAPV.
  cbn [fst snd] in HAPV. pose proof (dec_length id Hid). lia. }
assert (Hqv8 : In (qv, kv) (ablocks B ly8 S8)) by (apply (Permutation_in _ (Permutation_sym HPerm8)); right; exact Hqv4).
(* the call of arg_s(slot, verb) at 0x8c89c *)
pose proof (proj1 HJ8) as HAR9.
pose proof HJ8 as (_ & _ & _ & _ & _ & _ & Hnev9 & _ & _ & HJ8blk & _ & _ & _ & HJ9pres & _).
pose proof Hly8 as (_ & _ & _ & _ & _ & EF8 & _ & _ & Etop8 & Eslo8 & Eshi8 & _).
assert (EFL8 : flag_addr ly8 0 fpos = FL) by (unfold FL, flag_addr; rewrite EF8; reflexivity).
assert (Hp1b : In (p1, n1) (ablocks B ly8 S8))
  by (apply (Permutation_in _ (Permutation_sym HPerm8)); left; reflexivity).
set (KA2 := fun a : Z => (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
(exists p n, In (p, n) (ablocks B ly8 S8) /\ p <= a < p + req_size n)).
assert (KLOC2 : forall a, KA2 a -> 0 <= a < alloc_ceiling /\ ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ a <> FL).
{ intros a [Ha | [Ha | (p & n & Hpn & Hpa)]].
  - destruct (KLOC a (or_introl Ha)) as (H1 & H2 & H3 & H4). split; [exact H1 | split; [exact H2 | split; [exact H3 | exact H4]]].
  - destruct (KLOC a (or_intror (or_introl Ha))) as (H1 & H2 & H3 & H4). split; [exact H1 | split; [exact H2 | split; [exact H3 | exact H4]]].
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR9 Hpn) as (_ & Hp4096 & Hpceil & Hpapp & Hpres9 & _).
    pose proof (sep_block_frame SEGS B LAWS ly8 S8 W8 (ms_mem ms9) _ p n 0 fpos HAR9 Hpn Hfin8) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA8 in Hd. change (fs_frame_bytes 0) with 64 in Hd.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
    destruct (FFL _ _ _ _ _ 0 fpos HAR9 Hfin8) as (_ & HFLo9 & _ & _). rewrite EFL8 in HFLo9.
    split; [lia|]. split; [lia|]. split; [unfold SB; lia|].
    intros ->. exact (proj2 (Hpres9 FL ltac:(lia)) HFLo9). }
assert (K89 : forall a, KA2 a -> rdW W8 (ms_mem ms9) a = rdW W8 mem8 a).
{ intros a Ha. destruct (KLOC2 a Ha) as (Hb & HnF & HnS & _).
  apply (sar_aview_frame_pt E5 _ (w_H W8) mem8 (ms_mem ms9) a HFr9); [lia|].
  sar_nwin ltac:(fun H => rewrite ?Z2, ?Z34, ?Z1028, ?Z1041 in H; unfold SB in *; lia). }
assert (HREP9 : rec_repA B ly8 S8 (rdW W8 (ms_mem ms9)) (rec_record R 19 ([] ++ [sarg (Some (dec id))])) ((p1, n1) :: O1)).
{ apply (sar_rec_repA_kept B ly8 S8 (rdW W8 mem8) ly8 S8 (rdW W8 (ms_mem ms9)) _ ((p1, n1) :: O1) GREP8).
  - intros pn Hpn. destruct Hpn as [<- | Hpn]; [exact Hp1b|].
    apply (Permutation_in _ (Permutation_sym HPerm8)). right. exact (HO1b pn Hpn).
  - intros a Ha. apply K89. left. unfold REC_SIZE. exact Ha.
  - intros a Ha. apply K89. right. left. unfold SC_SIZE. exact Ha.
  - intros p n i Hpn Hi. apply K89. right. right. exists p, n. split.
    + destruct Hpn as [Hpn | Hpn]; [injection Hpn as <- <-; exact Hp1b|].
      apply (Permutation_in _ (Permutation_sym HPerm8)). right. exact (HO1b (p, n) Hpn).
    + unfold req_size. destruct (Z.eqb_spec n 0); lia. }
(* the verb's bytes and its tail at this state: its block is live and meets no footprint byte *)
assert (Hkvpos : 1 <= req_size kv /\ kv <= req_size kv).
{ destruct (al_blocks _ _ LAWS _ _ _ _ _ qv kv HAR Hqv) as (_ & _ & _ & _ & _ & Hk).
  apply req_size_pos. lia. }
assert (HqvnO : ~ In (qv, kv) O).
{ intros Hin. rewrite Forall_forall in HAPV. specialize (HAPV _ Hin). unfold iv_apart in HAPV. cbn [fst snd] in HAPV. lia. }
assert (HVFP : forall i, 0 <= i < Z.of_nat (length xv) + 1 -> ~ inFP FP (pv + i)).
{ intros i Hi (r & Hr & Hrq). cbn [In] in Hr. destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Hrq.
  - assert (Hg : A_G_REC <= pv + i < A_G_REC + REC_SIZE) by (unfold REC_SIZE in *; lia).
    assert (Hbnd : qv <= pv + i < qv + req_size kv) by lia.
    exact (blk_img SEGS B LAWS ly S W mem md qv kv (pv + i) HAR Hqv Hbnd
      (CPIMG (pv + i) (sar_in_PG (pv + i) (or_introl Hg)))).
  - assert (Hg : A_REC_SPILL <= pv + i < A_REC_SPILL + SC_SIZE) by (unfold SC_SIZE in *; lia).
    assert (Hbnd : qv <= pv + i < qv + req_size kv) by lia.
    exact (blk_img SEGS B LAWS ly S W mem md qv kv (pv + i) HAR Hqv Hbnd
      (CPIMG (pv + i) (sar_in_PG (pv + i) (or_intror Hg)))).
  - destruct (inFP_ablocks_fp_inv O (pv + i) (ex_intro _ r (conj Hr Hrq))) as (q2 & k2 & Hin2 & Hpa2).
    assert (Hne : (qv, kv) <> (q2, k2)) by (intros Heq; injection Heq as <- <-; exact (HqvnO Hin2)).
    assert (Hin2b : In (q2, k2) (ablocks B ly S)) by (exact (HOB (q2, k2) Hin2)).
    pose proof (sep_blocks SEGS B LAWS ly S W mem md qv kv q2 k2 HAR Hqv Hin2b Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (HSTRV9 : astr_atR (rdW W8 (ms_mem ms9)) pv xv).
{ destruct HSTRV as (HB1 & HB2). split; [|exact HB2].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  assert (Hib : 0 <= Z.of_nat i < Z.of_nat (length xv) + 1) by lia.
  assert (Hr8 : 0 <= pv + Z.of_nat i - qv < req_size kv) by lia.
  assert (Hnf : ~ inFP FP (qv + (pv + Z.of_nat i - qv))).
  { replace (qv + (pv + Z.of_nat i - qv)) with (pv + Z.of_nat i) by lia. exact (HVFP (Z.of_nat i) Hib). }
  pose proof (HJ8blk qv kv (pv + Z.of_nat i - qv) Hqv Hqv8 Hr8 Hnf) as Hkeep.
  replace (qv + (pv + Z.of_nat i - qv)) with (pv + Z.of_nat i) in Hkeep by lia.
  rewrite Hkeep. apply HB1. rewrite length_app. cbn [length]. lia. }
assert (HTAILV : atail_vis SEGS W8 (ms_mem ms9) (pv + Z.of_nat (length xv))).
{ assert (Hbnd : qv <= pv + Z.of_nat (length xv) < qv + req_size kv) by lia.
  exact (CHEAPT ly8 S8 W8 (ms_mem ms9) _ qv kv (pv + Z.of_nat (length xv)) HAR9 Hqv8 Hbnd). }
assert (HROD9 : arodata_okP SEGS RLO RHI B (rdW W8 (ms_mem ms9))).
{ apply (CRODK ly S W mem md ly8 S8 W8 (ms_mem ms9) _ SUP_AFTER_REPLY_STK (spZ regs) FP [(0, fpos)] _ HAR HJ8); [|exact HROD].
  intros a Hf. destruct (HFPKA a Hf) as [Ha | [Ha | (p & n & Hpn & Hpa)]].
  - left. exact (sar_in_PG a (or_introl Ha)).
  - left. exact (sar_in_PG a (or_intror Ha)).
  - right. exists p, n. split; [apply in_or_app; left; exact Hpn | exact Hpa]. }
pose proof (CROOK ly8 S8 W8 (ms_mem ms9) _ HAR9 HROD9) as HRO9.
pmkst HS. rewrite SIGARG.
sar_preg HS (1%bv : bv 5) D1. sar_preg HS (2%bv : bv 5) D2. sar_preg HS (3%bv : bv 5) D3.
sar_preg HS (4%bv : bv 5) D4. sar_preg HS (8%bv : bv 5) D8. sar_preg HS (10%bv : bv 5) D10.
sar_preg HS (11%bv : bv 5) D11.
cbn [sv_denot] in D1. rewrite (img_env_codeptr E5 HEI5 25456) in D1.
rewrite sar_denot_off0, (OLD5 3%nat ltac:(lia)), (OLD4 3%nat ltac:(lia)), (OLD3 3%nat ltac:(lia)), (OLD2 3%nat ltac:(lia)), (EE 3%nat 3%bv eq_refl) in D3.
rewrite sar_denot_off0, (OLD5 4%nat ltac:(lia)), (OLD4 4%nat ltac:(lia)), (OLD3 4%nat ltac:(lia)), (OLD2 4%nat ltac:(lia)), (EE 4%nat 4%bv eq_refl) in D4.
rewrite sar_denot_off0, (OLD5 11%nat ltac:(lia)), (OLD4 11%nat ltac:(lia)), (OLD3 11%nat ltac:(lia)), (OLD2 11%nat ltac:(lia)), (EE 11%nat 11%bv eq_refl) in D11.
rewrite sar_denot_off0 in D2, D8, D10.
assert (QspB : spZ (ms_regs ms9) = spZ regs + (sp1 - spZ regs)) by (unfold spZ at 1; rewrite D2, Z34; lia).
assert (QaB : getr (ms_regs ms9) 10 = w64 (rec_slot R)) by (rewrite D10, Z1064; reflexivity).
assert (QbB : getr (ms_regs ms9) 11 = w64 pv) by (rewrite D11; exact H11).
assert (WRA9 : rdword (rdW W8 (ms_mem ms9)) (spZ regs + -8) = Some (raZ regs)).
{ sar_wfind HS E5 (w_H W8) ms9 2%nat;
  [ exact Z2 | repeat (first [left; reflexivity | right])
  | rewrite sar_denot_off0, (OLD5 1%nat ltac:(lia)), (OLD4 1%nat ltac:(lia)), (OLD3 1%nat ltac:(lia)), (OLD2 1%nat ltac:(lia)), (EE 1%nat 1%bv eq_refl);
    unfold raZ; symmetry; apply Z_to_bv_bv_unsigned
  | unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr; exact Hr ]. }
assert (WS09 : rdword (rdW W8 (ms_mem ms9)) (spZ regs + -16) = Some (s0Z regs)).
{ sar_wfind HS E5 (w_H W8) ms9 2%nat;
  [ exact Z2 | repeat (first [left; reflexivity | right])
  | rewrite sar_denot_off0, (OLD5 8%nat ltac:(lia)), (OLD4 8%nat ltac:(lia)), (OLD3 8%nat ltac:(lia)), (OLD2 8%nat ltac:(lia)), (EE 8%nat 8%bv eq_refl);
    unfold s0Z; symmetry; apply Z_to_bv_bv_unsigned
  | unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hr; change (bv_modulus 64) with (2 ^ 64) in Hr; exact Hr ]. }
assert (Hab9 : forall a, spZ regs <= a < 2 ^ 64 -> rdW W8 (ms_mem ms9) a = rdW W mem a).
{ intros a Ha. apply (aview_above_of_journal (PI := PI) B SUP_AFTER_REPLY_STK (spZ regs) FP ly S W mem md
    [(0, fpos)] ly8 S8 W8 (ms_mem ms9) _ _ HJ8 a Ha).
  intros Hf. destruct (KLOC a (HFPKA a Hf)) as (Hb & _). unfold alloc_ceiling in *. lia. }
assert (HCHB : exists chB, achain ly8 (rdW W8 (ms_mem ms9)) (spZ regs + (sp1 - spZ regs)) (s0Z (ms_regs ms9)) chB).
{ assert (Es0B : s0Z (ms_regs ms9) = spZ regs) by (unfold s0Z; rewrite D8; exact Z2). rewrite Es0B.
  destruct (sar_chain_at ly (rdW W mem) (rdW W8 (ms_mem ms9)) (spZ regs) (s0Z regs) (raZ regs) ch
    (spZ regs + (sp1 - spZ regs)) Hch ltac:(lia) ltac:(lia) Hab9
    ltac:(replace (spZ regs - 8) with (spZ regs + -8) by lia; exact WRA9)
    ltac:(replace (spZ regs - 16) with (spZ regs + -16) by lia; exact WS09)
    Hra4 ltac:(lia) ltac:(apply sar_mod_16_8; exact Hal16) ltac:(lia)) as (chB & HchB).
  exists chB. exact (achain_ly_top ly ly8 _ _ _ _ Etop8 HchB). }
destruct HCHB as (chB & HCHB).
set (FPB := if Z.of_nat (length [sarg (Some (dec id))]) <? REC_ARGS_MAX
            then [(rec_slot R + CALL_OFF_NARGS, rec_slot R + CALL_OFF_NARGS + 4);
                  (rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length [sarg (Some (dec id))]),
                   rec_slot R + CALL_OFF_ARGS + 8 * Z.of_nat (length [sarg (Some (dec id))]) + 8)]
            else []).
assert (HFPBgs : forall a, inFP FPB a ->
  (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE)).
{ intros a (r & Hr & Hrq). unfold FPB in Hr. cbn in Hr.
  destruct Hslotr as [[Hlo Hhi] | Heq];
  [ left; destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hrq;
    unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE, REC_SIZE, OFF_CALLS in *; lia
  | right; destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hrq;
    rewrite Heq in Hrq; unfold CALL_OFF_NARGS, CALL_OFF_ARGS, SC_SIZE in *; lia ]. }
assert (HFPBKA : forall a, inFP FPB a -> KA a)
  by (intros a Hf; destruct (HFPBgs a Hf) as [Ha | Ha]; [left; exact Ha | right; left; exact Ha]).
assert (HFPBwr : forall a, inFP FPB a -> awr_byte SEGS B SUP_AFTER_REPLY_STK (spZ regs) FP
  (ablocks B ly S) (ablocks B ly8 S8) (frames S) ly8 [(0, fpos)] a).
{ intros a Hf. right; right; right; right; left.
  destruct (HFPBgs a Hf) as [Ha | Ha].
  - split; [exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity | cbn [fst snd]; lia]|].
    rewrite sar_ts_prog. split; [exact (sar_in_PG a (or_introl Ha)) | exact (CPIMG a (sar_in_PG a (or_introl Ha)))].
  - split; [exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split; [right; left; reflexivity | cbn [fst snd]; lia]|].
    rewrite sar_ts_prog. split; [exact (sar_in_PG a (or_intror Ha)) | exact (CPIMG a (sar_in_PG a (or_intror Ha)))]. }
assert (HARGVB : astr_argA B ly8 S8 (rdW W8 (ms_mem ms9)) (in_roP SEGS RLO RHI) [] pv (Some xv) \/
  (exists x, Some xv = Some x /\ astr_atR (rdW W8 (ms_mem ms9)) pv x /\
   Z.of_nat (length x) + 1 <= LMAX + 1 /\ afobj SEGS B ly8 S8 W8 (ms_mem ms9) pv (Z.of_nat (length x) + 1))).
{ left. cbn [astr_argA].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ qv kv HAR Hqv) as (_ & Hq4096 & _ & _ & _ & _).
  split; [lia|]. split; [exact HSTRV9|]. split; [exact HLENV|].
  left. split; [exists qv, kv; split; [exact Hqv8 | split; [lia | lia]] | apply Forall_nil]. }
assert (HARGTB : forall x, Some xv = Some x -> atail_vis SEGS W8 (ms_mem ms9) (pv + Z.of_nat (length x)))
  by (intros x Hx; injection Hx as <-; exact HTAILV).
assert (HNEVB : st_nev S8 + EV_ARG_S <= EV_MAX).
{ unfold EV_SUP_AFTER_REPLY in Hev. unfold EV_ARG_S, EV_XMALLOC in *. lia. }
assert (HLIVEB : blocks_bytes S8 + LIVE_ARG_S (Some xv) <= LIVE_MAX).
{ assert (EBB2 : blocks_bytes S2 = blocks_bytes S) by (rewrite ES2; reflexivity).
  rewrite Hverb in Hlive. unfold LIVE_SUP_AFTER_REPLY, LIVE_ARG_S, LIVE_XMALLOC in *. lia. }
assert (HMOKB : mo_ok MT S8 (XM_ARG_S MT (Some xv))).
{ rewrite <- Hverb. apply (mok_station MT S2 S8 (XM_SUP_AFTER_REPLY MT R id verb)
    (XM_RECORD MT R + XM_ARG_S MT (Some (dec id))) (XM_ARG_S MT verb) MTL HMOKS2);
  [ exact (mo_le_trans MT MTL S2 S4 S8 _ _ GMLE GMLE8)
  | exact (proj2 HXMnn) | unfold XM_SUP_AFTER_REPLY; lia ]. }
eapply SRr_bind.
{ eapply (cl_callS_wide (fx := fx1) B LAWS W8 (ms_regs ms9) (ms_mem ms9) (Z_to_bv 64 (BASE + AF_arg_s))
SUP_AFTER_REPLY_STK (spZ regs) FP ly S W mem md [(0, fpos)] ly8 S8 _ _ ARG_S_STK FPB EV_ARG_S (sp1 - spZ regs)
(getr (ms_regs ms9) 1) chB _ HJ8 QspB Hsp1b);
[ lia | rewrite HARGSTK; lia | rewrite HARGSTK, FS; lia | rewrite D3; exact Hgp | rewrite D4; exact Htp | reflexivity
| rewrite D1; apply ret_ok_codeptr_v; [lia | reflexivity]
| rewrite D1, unsigned_lit_small by lia; lia
| exact HCHB
| intros HPREB; exact (TARG_S fx1 ly8 S8 W8 (ms_regs ms9) (ms_mem ms9) _ chB (rec_slot R) pv 19
    [sarg (Some (dec id))] (Some xv) R ((p1, n1) :: O1) HPREB HROD9 HRO9 QaB QbB eq_refl HREP9 HARGVB HARGTB
    HNEVB HLIVEB HMOKB)
| exact HFPBwr
| intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hwb _; exfalso;
  destruct (KLOC a (HFPBKA a Ha)) as (Hb & _); rewrite FS in Hwb; unfold alloc_ceiling in *; lia ]. }
cbv beta. intros W10 c10 Hwle10 (ly10 & S10 & regs10 & mem10 & md10 & -> & HJ10 & HJ10c & HP10 & HKarg2).
rewrite D1.
(* arg_s's second post: one more fresh block (the verb's copy), recorded as the call's second argument *)
cbv zeta in HKarg2.
destruct HKarg2 as (GBB10 & GMLE10 & [(Hc6b & _) | (_ & p2 & Hp2 & HPerm10 & HAp2 & GREP10)]);
  [ cbn [length Z.of_nat] in Hc6b; unfold REC_ARGS_MAX in Hc6b; lia | ].
set (n2 := Z.of_nat (length (sarg (Some xv))) + 1) in *.
(* back at 0x8c8a0: keep the frame, its shadow, its flag word, the realigned stack word and the saved registers *)
pose proof (proj1 HJ10) as HAR10.
pose proof HJ10 as (_ & Hly10 & _ & _ & _ & _ & Hnev10 & _ & _ & _ & _ & _ & _ & HJ10pres & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly10 HAR Hly10) as (Eab10 & Efa10 & _).
assert (EFA10 : frame_addr ly10 0 fpos = F) by (rewrite Efa10; reflexivity).
pose proof Hly10 as (_ & _ & _ & _ & _ & EF10 & _ & _ & Etop10 & Eslo10 & Eshi10 & _).
assert (EFL10 : flag_addr ly10 0 fpos = FL) by (unfold FL, flag_addr; rewrite EF10; reflexivity).
pose proof HJ10c as (_ & _ & _ & _ & _ & Hfrs10c & _). cbn [app] in Hfrs10c.
assert (Hfin10 : In (0, fpos) (frames S10)) by (rewrite Hfrs10c; exact Hfin8).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR10 Hfin10) as (_ & _ & HFpres10 & HFSpres10).
rewrite EFA10 in HFpres10, HFSpres10. change (fs_frame_bytes 0) with 64 in HFpres10, HFSpres10. change (64 / 8) with 8 in HFSpres10.
destruct (FFL _ _ _ _ _ 0 fpos HAR10 Hfin10) as (HFLp10 & HFLo10 & _ & _). rewrite EFL10 in HFLp10, HFLo10.
assert (HnFPB : forall a, inFP FPB a -> ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ 0 <= a < alloc_ceiling).
{ intros a Hf. destruct (KLOC a (HFPBKA a Hf)) as (Hb & HnF & HnS & _). split; [exact HnF | split; [exact HnS | exact Hb]]. }
jafter_call_keep_hi HS 1140%nat regs10 (mrestrict (w_H W10) mem10) HP10 [0;1;2;3;4]%nat HS10.
match type of HS10 with ?tq -> _ => assert (HRK : tq); [|specialize (HS10 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
- eapply (region_kept_fshadow_sub B E5 ARG_S_STK (spZ regs + (sp1 - spZ regs)) FPB ly8 S8 W8 (ms_mem ms9) _ ly10 S10 W10 mem10 md10 _
    1041 (SB + F / 8) _ _ _ _ _ 0 fpos HJ10c Z1041 Hfin8);
  [ unfold shadow_addr; rewrite EFA8; rewrite <- SB_SHADOW_OFF; lia
  | unfold shadow_addr; rewrite EFA8; rewrite <- SB_SHADOW_OFF; change (fs_frame_bytes 0 / 8) with 8; lia
  | intros a Ha HFa; destruct (HnFPB a HFa) as (_ & HnS & _); unfold SB in *; lia
  | intros a Ha; replace a with (shadow_addr F + (a - (SB + F / 8))) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
    apply (proj1 (HFSpres10 (a - (SB + F / 8)) ltac:(unfold SB in *; lia))) ].
- eapply (region_kept_frame_sub B E5 ARG_S_STK (spZ regs + (sp1 - spZ regs)) FPB ly8 S8 W8 (ms_mem ms9) _ ly10 S10 W10 mem10 md10 _
    1028 F _ _ _ _ _ 0 fpos HJ10c Z1028 Hfin8);
  [ rewrite EFA8; lia | rewrite EFA8; change (fs_frame_bytes 0) with 64; lia
  | intros a Ha HFa; destruct (HnFPB a HFa) as (HnF & _); lia
  | intros a Ha; lia ].
- eapply (region_kept_frame_sub B E5 ARG_S_STK (spZ regs + (sp1 - spZ regs)) FPB ly8 S8 W8 (ms_mem ms9) _ ly10 S10 W10 mem10 md10 _
    1028 F _ _ _ _ _ 0 fpos HJ10c Z1028 Hfin8);
  [ rewrite EFA8; lia | rewrite EFA8; change (fs_frame_bytes 0) with 64; lia
  | intros a Ha HFa; destruct (HnFPB a HFa) as (HnF & _); lia
  | intros a Ha; exact (proj1 (HFpres10 a ltac:(lia))) ].
- eapply (region_kept_stack_sub SEGS B E5 ARG_S_STK (spZ regs + (sp1 - spZ regs)) FPB ly8 S8 W8 (ms_mem ms9) _
    ly10 S10 W10 mem10 md10 _ 34 _ _ _ _ _ sp1 SUP_AFTER_REPLY_STK (spZ regs) FP ly S W mem md _ _ HJ10c HJ10 Z34);
  [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (HnFPB a HFa) as (_ & _ & Hb); unfold alloc_ceiling in *; lia].
- eapply (region_kept_stack_sub SEGS B E5 ARG_S_STK (spZ regs + (sp1 - spZ regs)) FPB ly8 S8 W8 (ms_mem ms9) _
    ly10 S10 W10 mem10 md10 _ 2 _ _ _ _ _ (spZ regs) SUP_AFTER_REPLY_STK (spZ regs) FP ly S W mem md _ _ HJ10c HJ10 Z2);
  [lia | rewrite FS; lia | lia | lia | lia | intros a Ha HFa; destruct (HnFPB a HFa) as (_ & _ & Hb); unfold alloc_ceiling in *; lia]. }
rewrite <- restrict_mkst_fx in HS10. clear HS. rename HS10 into HS.
clear D2 D3 D4 D8 D10 D11.
remember (havoc E5 1140 (map (getr regs10) CLOB)) as E6 eqn:HE6 in HS.
assert (HAE6 : env_agree 32 (Ereg regs (sar_extra (as_uar_cell B) sp1)) E6) by (rewrite HE6; apply env_agree_havoc_ge; [lia | exact HAE5]).
assert (HEI6 : img_env VAL A_LIM E6) by (rewrite HE6; apply img_env_havoc_hi; [exact HEI5 | unfold A_LIM; lia]).
assert (OLD6 : forall n, (n < 1140)%nat -> ew E6 n = ew E5 n) by (intros n Hn; rewrite HE6; apply ew_havoc_old; exact Hn).
clear HE6.
assert (U2b : bv_unsigned (ew E6 2) = spZ regs) by (rewrite OLD6 by lia; exact Z2).
assert (U34b : bv_unsigned (ew E6 34) = sp1) by (rewrite OLD6 by lia; exact Z34).
assert (U1028 : bv_unsigned (ew E6 1028) = F) by (rewrite OLD6 by lia; exact Z1028).
assert (U1040 : bv_unsigned (ew E6 1040) = FL) by (rewrite OLD6 by lia; exact Z1040).
assert (U1041 : bv_unsigned (ew E6 1041) = SB + F / 8) by (rewrite OLD6 by lia; exact Z1041).
assert (HFLnS : ~ (SB + F / 8 <= FL < SB + F / 8 + 8)).
{ intros Hx. apply (proj2 (HFSpres10 (FL - (SB + F / 8)) ltac:(lia))).
  replace (shadow_addr F + (FL - (SB + F / 8))) with FL by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia). exact HFLo10. }
assert (HFLnF : ~ (F <= FL < F + 64)) by (intros Hx; exact (proj2 (HFpres10 FL Hx) HFLo10)).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv (YP09.mkRegion (Some 1040%nat) 0 1 0 1 []) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite U1040; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLp10)
ltac:(cbn [all_disjoint ss_mem]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite U1040, U1041, U1028, U2b, U34b; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. sar_norm HS.
(* run 6: the frame's magic retired, its shadow := 0xf5, its flag byte := 0 (the release), the saved registers
   back, and the return at 0x8c934 *)
pose (RUNF := aj_flag_store_pi (fx := fx1) B LAWS ML AFREE_LAW FFL).
paj_run_flag_sh RUNF HS HJ10.
- lia.
- intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  destruct Hin as [<- | Hin];
  [right; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite U1040 in Hr; rewrite EFL10; lia|]. left.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  rewrite ?U1041, ?U1028, ?U2b, ?U34b in Hr;
  first [ exfalso; unfold SB in *; lia | left; rewrite FS; lia
  | right; right; right; left; exists 0, fpos; split; [left; reflexivity|];
    first [ left; unfold in_zr; cbn [fst snd]; rewrite EFA10; change (fs_frame_bytes 0) with 64; lia
    | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite EFA10, <- SB_SHADOW_OFF;
      change (fs_frame_bytes 0 / 8) with 8; lia ] ] |]).
  destruct Hin.
- intros msr HSr. rewrite EFL10.
  pose proof (st_ok_pi_region_nth E6 _ _ 0 _ HSr eq_refl) as HR0.
  pose proof (field_of_region E6 _ 1040 FL _ 0 1 0 1 0 1%N (SLit 0) 0 HR0 U1040 ltac:(cbn [In]; tauto) eq_refl ltac:(lia) ltac:(lia)) as HV.
  specialize (HV 0%nat ltac:(lia)). rewrite !Z.add_0_r in HV. rewrite HV. reflexivity.
-
rename ms into ms11, mat into mat11, HF into HF11, HFr into HFr11, HG into HG11.
(* the recorder's state, its blocks and the meters at the return *)
assert (EAB11 : ablocks B ly10 (stack_free_state 0 fpos S10) = ablocks B ly10 S10)
  by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
assert (HO2b : forall pn, In pn ((p2, n2) :: (p1, n1) :: O1) -> In pn (ablocks B ly10 S10)).
{ intros pn [<- | [<- | Hpn]].
  - apply (Permutation_in _ (Permutation_sym HPerm10)). left. reflexivity.
  - apply (Permutation_in _ (Permutation_sym HPerm10)). right.
    apply (Permutation_in _ (Permutation_sym HPerm8)). left. reflexivity.
  - apply (Permutation_in _ (Permutation_sym HPerm10)). right.
    apply (Permutation_in _ (Permutation_sym HPerm8)). right. exact (HO1b pn Hpn). }
assert (KLOC3 : forall p n a, In (p, n) (ablocks B ly10 S10) -> p <= a < p + req_size n ->
  0 <= a < alloc_ceiling /\ ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ a <> FL).
{ intros p n a Hpn Hpa.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR10 Hpn) as (_ & Hp4096 & Hpceil & Hpapp & Hpres10 & _).
  pose proof (sep_block_frame SEGS B LAWS ly10 S10 W10 mem10 md10 p n 0 fpos HAR10 Hpn Hfin10) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA10 in Hd. change (fs_frame_bytes 0) with 64 in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
  split; [lia|]. split; [lia|]. split; [unfold SB; lia|].
  intros ->. exact (proj2 (Hpres10 FL ltac:(lia)) HFLo10). }
assert (K1011 : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
  (exists p n, In (p, n) (ablocks B ly10 S10) /\ p <= a < p + req_size n) ->
  rdW W10 (ms_mem ms11) a = rdW W10 mem10 a).
{ intros a Ha.
  assert (Hb : 0 <= a < alloc_ceiling /\ ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\ a <> FL).
  { destruct Ha as [Ha | [Ha | (p & n & Hpn & Hpa)]];
    [ destruct (KLOC a (or_introl Ha)) as (H1 & H2 & H3 & H4); split; [exact H1 | split; [exact H2 | split; [exact H3 | exact H4]]]
    | destruct (KLOC a (or_intror (or_introl Ha))) as (H1 & H2 & H3 & H4); split; [exact H1 | split; [exact H2 | split; [exact H3 | exact H4]]]
    | exact (KLOC3 p n a Hpn Hpa) ]. }
  destruct Hb as (Hb1 & Hb2 & Hb3 & Hb4).
  apply (sar_aview_frame_pt E6 _ (w_H W10) mem10 (ms_mem ms11) a HFr11); [lia|].
  sar_nwin ltac:(fun H => rewrite ?U2b, ?U34b, ?U1028, ?U1040, ?U1041 in H; unfold SB in *; lia). }
assert (HREPF : rec_repA B ly10 (stack_free_state 0 fpos S10) (rdW W10 (ms_mem ms11))
  (rec_record R 19 ([sarg (Some (dec id))] ++ [sarg (Some xv)])) ((p2, n2) :: (p1, n1) :: O1)).
{ apply (sar_rec_repA_kept B ly10 S10 (rdW W10 mem10) ly10 (stack_free_state 0 fpos S10) (rdW W10 (ms_mem ms11)) _ _ GREP10).
  - intros pn Hpn. rewrite EAB11. exact (HO2b pn Hpn).
  - intros a Ha. apply K1011. left. unfold REC_SIZE. exact Ha.
  - intros a Ha. apply K1011. right. left. unfold SC_SIZE. exact Ha.
  - intros p n i Hpn Hi. apply K1011. right. right. exists p, n.
    split; [exact (HO2b (p, n) Hpn)|]. unfold req_size. destruct (Z.eqb_spec n 0); lia. }
(* the blocks: p1 and p2 are fresh, the record's freed blocks were the recorder's own *)
pose proof (sar_ablocks_nodup B ly S W mem md HAR) as NDS.
assert (NDS2 : List.NoDup (ablocks B ly4 S4 ++ Frec)).
{ apply (Permutation_NoDup (l := ablocks B ly S2)); [exact HpermF | rewrite Eab; exact NDS]. }
assert (HFrecO : forall pn, In pn Frec -> In pn O) by exact HFO.
assert (Hp1nS : ~ In (p1, n1) (ablocks B ly4 S4)).
{ intros Hin. rewrite Forall_forall in HAp1. specialize (HAp1 _ Hin). unfold iv_apart in HAp1. cbn [fst snd] in HAp1.
  unfold n1 in *. cbn [sarg] in *. pose proof (dec_length id Hid). lia. }
assert (Hp2nS8 : ~ In (p2, n2) (ablocks B ly8 S8)).
{ intros Hin. rewrite Forall_forall in HAp2. specialize (HAp2 _ Hin). unfold iv_apart in HAp2. cbn [fst snd] in HAp2.
  unfold n2 in *. cbn [sarg] in *. lia. }
assert (Hp2nS4 : ~ In (p2, n2) (ablocks B ly4 S4))
  by (intros Hin; apply Hp2nS8; apply (Permutation_in _ (Permutation_sym HPerm8)); right; exact Hin).
assert (HSS4 : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly4 S4)).
{ intros pn Hpn Hpo. assert (Hpn2 : In pn (ablocks B ly S2)) by (rewrite Eab; exact Hpn).
  pose proof (Permutation_in _ HpermF Hpn2) as Hin. apply in_app_iff in Hin as [H1 | H1]; [exact H1|].
  exfalso. exact (Hpo (HFrecO pn H1)). }
eapply (paj_ret_at (PL := PL_cmd) (PI := PI) (fx := fx1) W10 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
sar_preg HS (1%bv : bv 5) RR1.
rewrite sar_denot_off0, (OLD6 1%nat ltac:(lia)), (OLD5 1%nat ltac:(lia)), (OLD4 1%nat ltac:(lia)),
  (OLD3 1%nat ltac:(lia)), (OLD2 1%nat ltac:(lia)), (EE 1%nat 1%bv eq_refl) in RR1.
pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'.
replace (v_jalr (getr (ms_regs ms11) 1) 0) with (getr regs 1) by (rewrite RR1; symmetry; exact Hra').
apply (apost_baseF_intro (fx := fx1) SEGS fx1 B SUP_AFTER_REPLY_STK FP regs ly S W mem md (EV_SUP_AFTER_REPLY R) _ W10
  ly10 (stack_free_state 0 fpos S10) (ms_regs ms11) (ms_mem ms11) _ (fxrel_refl fx1)).
+ eapply (ajournal_mono_k SEGS B);
  [ apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ10
  | unfold EV_SUP_AFTER_REPLY; lia ].
+ eapply (aregs_preserved_of_st_ok SEGS (w_H W10) E6 _ ms11 regs (sar_extra (as_uar_cell B) sp1) HS HAE6).
  vm_compute. reflexivity.
+ cbv beta. exists ((p2, n2) :: (p1, n1) :: O1).
  split.
  { rewrite (sar_model R id verb). rewrite Hverb. rewrite <- app_assoc. cbn [app]. exact HREPF. }
  split.
  { intros pn [<- | [<- | QHpn]].
    - destruct (List.in_dec sar_pair_eq_dec (p2, n2) (ablocks B ly S)) as [QHin | QHnin]; [|right; exact QHnin].
      destruct (List.in_dec sar_pair_eq_dec (p2, n2) O) as [QHo | QHno]; [left; exact QHo|].
      exfalso. exact (Hp2nS4 (HSS4 (p2, n2) QHin QHno)).
    - destruct (List.in_dec sar_pair_eq_dec (p1, n1) (ablocks B ly S)) as [QHin | QHnin]; [|right; exact QHnin].
      destruct (List.in_dec sar_pair_eq_dec (p1, n1) O) as [QHo | QHno]; [left; exact QHo|].
      exfalso. exact (Hp1nS (HSS4 (p1, n1) QHin QHno)).
    - left. exact (HO1O pn QHpn). }
  split.
  { intros pn QHpn QHpo. rewrite EAB11.
    apply (Permutation_in _ (Permutation_sym HPerm10)). right.
    apply (Permutation_in _ (Permutation_sym HPerm8)). right. exact (HSS4 pn QHpn QHpo). }
  split.
  { intros pn QHpn. rewrite EAB11 in QHpn.
    pose proof (Permutation_in _ HPerm10 QHpn) as QH1. cbn [In] in QH1. destruct QH1 as [<- | QH1]; [right; left; reflexivity|].
    pose proof (Permutation_in _ HPerm8 QH1) as QH2. cbn [In] in QH2. destruct QH2 as [<- | QH2]; [right; right; left; reflexivity|].
    destruct (List.in_dec sar_pair_eq_dec pn O1) as [QHo1 | QHno1]; [right; right; right; exact QHo1|].
    left. split.
    - rewrite <- Eab. apply (Permutation_in _ (Permutation_sym HpermF)). apply in_or_app. left. exact QH2.
    - intros QHo. apply QHno1. apply GO. split; [exact QHo|].
      intros QHF. exact (list_nodup_app_disj (ablocks B ly4 S4) Frec pn NDS2 QH2 QHF). }
  split.
  { assert (QEBB11 : blocks_bytes (stack_free_state 0 fpos S10) = blocks_bytes S10) by reflexivity.
    assert (QEBB2 : blocks_bytes S2 = blocks_bytes S) by (rewrite ES2; reflexivity).
    rewrite QEBB11. rewrite Hverb in Hlive |- *.
    unfold LIVE_SUP_AFTER_REPLY, LIVE_ARG_S, LIVE_XMALLOC in *. lia. }
  unfold XM_SUP_AFTER_REPLY, stack_free_state. apply (mo_le_set_fs_r MT MTLF).
  rewrite Hverb.
  replace (XM_RECORD MT R + XM_ARG_S MT (Some (dec id)) + XM_ARG_S MT (Some xv))
    with ((XM_RECORD MT R + XM_ARG_S MT (Some (dec id))) + XM_ARG_S MT (Some xv)) by lia.
  apply (mo_le_trans MT MTL S S8 S10); [|exact GMLE10].
  apply (mo_le_set_fs_l MT MTLF S S8 fS2). rewrite <- ES2.
  exact (mo_le_trans MT MTL S2 S4 S8 _ _ GMLE GMLE8).
Qed.
End e.
End f.
End d.
Check tsup_after_reply_holds.
Print Assumptions tsup_after_reply_holds.
