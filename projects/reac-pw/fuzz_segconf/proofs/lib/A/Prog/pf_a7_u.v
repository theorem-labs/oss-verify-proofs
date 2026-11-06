(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_pool_config (plugin-hostd/fuzz_command, image
   fuzz_command.asan-ubsan, entry BASE + AF_sup_pool_config = 0x8bed0, 127 instructions): it proves a Theorem Labs lane's
   `tsup_pool_config_spec` (lib/B/Prog/sup_pool_config_c.v, a working branch 707acd856cb; the same text as at
   f490061c104) in the form of
   cgif_file_fuzzer's per-function walks: afn_pre at the entry, the symbolic executor over the position-abstract
   listing up to each call, the runtime's rules at the runtime calls (__asan_stack_malloc_0, the snprintf wrapper,
   the frame's release by its flag byte), the callee contracts record_c, arg_s_c, rec_shape_of_c and answer_c at the
   program calls (through cl_callS_wide / cl_callS_na), the return through paj_ret_at, and apost_base at the end.

   It is the B re-walk of the A walk lib/A/Prog/sup_pool_config.v (a working branch c4f188792bb),
   whose B code differs: B calls record() and arg_s() where A inlined record() and called xstrdup, and B inlines
   arg_i, so this function owns arg_i's class-0 side-stack frame (64 bytes, b = frame + 32) and its snprintf. The
   frame code (prologue, realignment `andi sp,sp,-32`, __asan_stack_malloc_0, header and shadow f1 f1 f1 f1 | f8 f8 |
   f3 f3, b unpoisoned around the snprintf and the second arg_s, the release through the flag byte) is arg_i's ASan
   walk's (lib/A/Prog/arg_i.v, a working branch 12dc52bfe84) and answer_code's ASan walk's
   (lib/A/Prog/answer_code.v, a working branch 2ba4488ce71); the B kit usage is socket_send's B walk
   (lib/B/Prog/socket_send.v, a working branch a470f91dbfb).

   Report and trap edges: none. The function has no `jal __asan_report_*`, no `unimp`, no UBSan handler call
   (capstone over the pin's .symtab, gen/traps.B.summary row `sup_pool_config 0`). Its branches: 0x8bf30 `beqz a2`
   on the use-after-return flag, read through the GOT word 0xa5fa8 at the record's const cell 0xb0c40 (= 1, lib/B/YF0m.v
   z4 (ANum 0xb0c40) 0x1, AR's const-cell law al_const; the executor decides it not taken); 0x8bf4c `bnez s2` and
   0x8c040 `beqz s2` on the side-stack frame (nonzero, __asan_stack_malloc_0's post; decided by the frame atom's
   fact), so the real-stack fallback 0x8bf50-0x8bf68 with its page probe and the real-stack release 0x8c074-0x8c090
   are not reached. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_pool_config.v, with its module paths and module names changed; 234 of its 315 lines of code are new or changed and 1983 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s10k.v, with its module paths and module names changed; 170 of its 199 lines of code are new or changed and 286 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the piece UNK of segment A7 of reac_segconf_parse_file's walk,
   `a7_u : A7_S_UNK B` (lib/A/Prog/pf_a7_m.v). Segment A7's proof (piece UNK), 2026-10-30.

   UNK 0x880e4 (BASE + A7_UNK) is the F_unknown refusal site of the header branch:
     0x880e4 auipc a0, 0xfff99 ; 0x880e8 addi a2, a0, 0x3dc   a2 = 0x214c0 = seg_litA_rc F_unknown (listing
                                                              object 42, .str.7)
     0x880ec mv a0, s8 (c)     ; 0x880f0 mv a1, s10 (lineno = ln + 1) ; 0x880f4 mv a3, s3 (the body)
     0x880f8 jal refuse        -- returns at 0x880fc, which is the cut CLR (pf_pieces.v), so H_CLR at the FP
                                  state refuse returned ends the piece.
   Six instructions, one program call, no inline check.

   The walk: pf_a7_q.v's seed at UNK with no writable region (bw = false: the five instructions before the call
   write no memory, so the call state's memory is the cut's); one plain run to the jal (PaCallRun.v
   paj_run_shc); the call through PaFx.v's cl_callSF with refuse_contract at BASE + AF_refuse (the listing's
   call target pa_sigma SS_refuse, by SegObj.v's seg_sig_prog); refuse_contract's premises from pf_a7_s.v's
   closed site lemma a7_refuse_site_880f8_body (VERIFY rule 1j-bis; the body is a free list there, as INV_UNK
   carries it, with f = F_unknown and args = [AS body]); the frame chain at the call from
   pf_a5_k.v's a5_chain; after the call, pf_base at the returned FP state from pf_a6_k.v's a6_keeps_refuse and
   a6_base_move, cur_name from a6_nm_move, the counter room from pf_a7_f.v's a7_cnt_refuse_next, and the
   registers (all callee-saved) from the run's and the call's aregs_preserved; the post is lifted from that FP
   state by PaFx.v's srr_apost_baseF_lift, and it matches H_CLR's because INV_UNK carries the r_header equation.

   Section hypotheses:
     REF   refuse_contract at BASE + AF_refuse, STK_refuse, RLO_A, RHI_A, seg_litA_rc, gotwA, guardA, at every FP
           state (pf_pieces.v's segment list, A7's callee)
     SIGP  SegObj.seg_sig_prog (the call target pa_sigma SS_refuse is BASE + AF_refuse)
     OBJ   SegObj.seg_val_objs (the auipc / addi pair's object atom A_OBJ 42 is seg_litA_rc F_unknown)
     VRO   SegObj.seg_val_relro, and
     SSPX  the stack-protector cells at every AR state (reac_segconf_parse.v's shape): both FORCED by
           pf_a6_k.v's a6_base_move after the refuse call, and used nowhere else. refuse's post gives only its
           journal, which keeps an image byte only when it is not one of `as_owned_static B` (YCbq.v:479);
           whether the GOT word 0xa36d8 and the guard 0x5ff078 are owned statics is a record fact of listing
           stage 2 (SegRecCells.seg_rec_cells, after the image-A owner's AF0m), which discharges SSPX; arodata_okP
           after refuse needs pa_relro_img over RLO_A .. RHI_A, which is VRO (the pinned instance gives it by
           computation). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  pf_pieces pf_a5_k pf_a6_k pf_a7_f pf_a7_d pf_a7_m pf_a7_q pf_a7_s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the run before the call writes nothing: no region of a7_ss _ false has a write window (as pf_a7_cr.v's a7c_awr) *)
Local Ltac a7u_awr :=
  unfold a7_ss, a7_regions; cbn [ss_mem];
  repeat (apply awr_ok_cons_ro; [unfold a7_saved_r, a7_slot_r, a7_sh_r, a7_buf_r; cbn [YP09.r_wlo YP09.r_whi]; lia|]);
  apply awr_ok_nil.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the program callee (pf_pieces.v's segment list for A7), at image A's numbers, at every FP state *)
Hypothesis REF : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
(* the listing's facts over the walk's abstract instance (SegObj.v; the pinned instance gives each by
   computation): the call target, the object atoms, the read-only range *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
(* FORCED by pf_a6_k.v's a6_base_move after the refuse call, used nowhere else (see the head comment) *)
Hypothesis VRO : seg_val_relro (PI := PI).
(* the stack-protector cells at every AR state: the image-A owner's route A, the shape of
   lib/A/Prog/reac_segconf_parse.v; discharged by SegRecCells.seg_rec_cells when listing stage 2 compiles. FORCED by
   a6_base_move after the refuse call (refuse's journal keeps no owned static), used nowhere else. *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

(* the literal a2 holds at the call: listing object 42 is .str.7, F_unknown's text (SegInstA.v's map) *)
Lemma a7u_lit : forall E, img_env VAL A_LIM E -> ew E (A_OBJ 42) = w64 (seg_litA_rc F_unknown).
Proof.
intros E HE. rewrite (img_env_atomP E (A_OBJ 42) HE) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
rewrite (OBJ 42%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

Section s.
Context {fx : YK11.FPState}.

Lemma a7u_unk : forall n, (forall f1 : YK11.FPState, H_CLR (fx := f1) B n) -> H_UNK (fx := fx) B n.
Proof.
intros n HCLR. unfold H_UNK.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d bp body HINV.
destruct HINV as (HB & HMID & HST & HSTR & HINB & HRH & HRG).
rewrite HRH.
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hfin & G & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
pose proof (a7_st_of_base B v pos lyc Sc Wc rX memc mdc HB) as HA7.
destruct (a5_chain B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as [ch1 HCH].
pose proof HB as (HCX & (HJ & Hly' & HFS & HPERM & HSV & HFL & HFRM & _) & HOBJ & HSL & HFSH).
pose proof HOBJ as (_ & _ & _ & _ & HCH0 & _).
destruct HST as (HRC & HNM & HCNT).
pose proof HMID as (Ho & _ & _).
pose proof STK_values as (_ & SRF & _ & SPF & _).
pose proof (a6_s1 (pf_sp0 v) G3) as (S1a & S1b & S1c & S1d). rewrite <- a6_s1_eq in S1a, S1b, S1c, S1d.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR HCH0
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & Hinc & Hc1 & Hc2 & _).
(* the registers the cut names *)
assert (R24 : getr rX 24 = w64 (p_c v))
  by (exact (a5_rg_get rX _ 24 _ HRG ltac:(cbn [PF_RM app In]; tauto))).
assert (R26 : getr rX 26 = w64 (ln + 1))
  by (exact (a5_rg_get rX _ 26 _ HRG ltac:(cbn [PF_RM app In]; tauto))).
assert (R19 : getr rX 19 = w64 bp)
  by (exact (a5_rg_get rX _ 19 _ HRG ltac:(cbn [PF_RM app In]; tauto))).
(* the seed at UNK, no region writable *)
pose proof (a7_seed B v pos lyc Sc Wc rX memc mdc A7_UNK false HB) as HS.
assert (HEI : img_env VAL A_LIM (a7_E rX v pos)) by apply a7_E_img.
change (cfg_at SEGS (BASE + A7_UNK) rX memc mdc)
  with (mkCfg (mkst rX (Z_to_bv 64 (BASE + A7_UNK)) memc (seg_rom SEGS)) mdc).
(* 0x880e4 .. 0x880f8: a2 = F_unknown's literal, a0 = c, a1 = lineno, a3 = the body, the call *)
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
{ a7u_awr. }
assert (Hmem : ms_mem ms = memc).
{ apply functional_extensionality. intros x. unfold frame_of in HF. rewrite HF; [reflexivity|].
  intros (r & Hr & Ha). unfold a7_ss, a7_regions in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]];
    unfold a7_saved_r, a7_slot_r, a7_sh_r, a7_buf_r in Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
pmkst HS. rewrite Hmem in HJ |- *.
clear HF HFr HG.
(* the callee-saved registers are the cut's *)
pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ rX (a7_extra v pos) HS (a7_E_agree rX v pos)
  ltac:(vm_compute; reflexivity)) as HPR.
assert (C2 : getr (ms_regs ms) 2 = w64 (pf_s1 v)).
{ transitivity (getr rX 2); [exact (HPR 2 ltac:(unfold acallee_saved; lia))|].
  exact (a5_rg_get rX _ 2 _ HFI ltac:(cbn [a5_FI In]; tauto)). }
assert (C3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ transitivity (getr rX 3); [exact (HPR 3 ltac:(unfold acallee_saved; lia))|].
  exact (a5_rg_get rX _ 3 _ HFI ltac:(cbn [a5_FI In]; tauto)). }
assert (C4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ transitivity (getr rX 4); [exact (HPR 4 ltac:(unfold acallee_saved; lia))|].
  exact (a5_rg_get rX _ 4 _ HFI ltac:(cbn [a5_FI In]; tauto)). }
assert (C8 : getr (ms_regs ms) 8 = w64 (pf_sp0 v)).
{ transitivity (getr rX 8); [exact (HPR 8 ltac:(unfold acallee_saved; lia))|].
  exact (a5_rg_get rX _ 8 _ HFI ltac:(cbn [a5_FI In]; tauto)). }
assert (Csp : spZ (ms_regs ms) = pf_s1 v).
{ unfold spZ. rewrite C2. unfold w64. apply unsigned_lit_small. lia. }
(* the call's registers *)
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
assert (C1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + PF_CLR)).
{ rewrite Q1. unfold PF_CLR, AF_reac_segconf_parse_file. reflexivity. }
assert (C10 : getr (ms_regs ms) 10 = w64 (p_c v)).
{ rewrite Q10, (a7_ew_reg rX v pos 24 24%bv eq_refl). exact R24. }
assert (C11 : getr (ms_regs ms) 11 = w64 (ln + 1)).
{ rewrite Q11, (a7_ew_reg rX v pos 26 26%bv eq_refl). exact R26. }
assert (C12 : getr (ms_regs ms) 12 = w64 (seg_litA_rc F_unknown)).
{ rewrite Q12. change 283%nat with (A_OBJ 42). exact (a7u_lit _ HEI). }
assert (C13 : getr (ms_regs ms) 13 = w64 bp).
{ rewrite Q13, (a7_ew_reg rX v pos 19 19%bv eq_refl). exact R19. }
(* the cut's facts at the call state: its memory is the cut's, its journal the run's *)
assert (HA7c : a7_st B v pos lyc Sc Wc memc mdq).
{ destruct HA7 as [X1 X2 X3 X4 X5 X6]. constructor; [exact X1 | exact HJ | exact X3 | exact X4 | exact X5 | exact X6]. }
assert (HBc : pf_base B v pos lyc Sc Wc (ms_regs ms) memc mdq PF_SC_LINE).
{ split; [exact HCX|]. split; [|exact (conj HOBJ (conj HSL HFSH))].
  refine (conj HJ (conj Hly' (conj HFS (conj HPERM (conj HSV (conj HFL (conj HFRM _))))))).
  exact (a5_rg_pres rX (ms_regs ms) (a5_FI B v) HPR (a5_FI_cs B v) HFI). }
(* VERIFY rule 1j-bis at 0x880f8: refuse_contract's premises besides afn_pre, pf_a7_s.v's closed site lemma *)
pose proof (a7_refuse_site_880f8_body B v pos lyc Sc Wc memc mdq (ms_regs ms) cf o ln d n bp body HA7c HRC
  (a7_cnt_zero cf (p_s v) o Ho HCNT) HMID HFRM C10 C11 C12 C13 HSTR HINB)
  as (ROD & _ & Hc64 & _ & Hl64 & _ & Hf64 & RPRE & ROOM & EV).
rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callSF (fx := fx) B LAWS Wc (ms_regs ms) memc _ STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdq 0
    STK_refuse (refuse_W (p_c v) cf) EV_refuse (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + PF_CLR)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       sa_rconf (rdW W2 mem2) (p_c v) (refuse cf (ln + 1) F_unknown [AS body]) /\ sa_noalloc B lyc Sc ly2 S2) HJ).
  - rewrite Csp. lia.
  - exact S1d.
  - lia.
  - rewrite SRF. lia.
  - rewrite SRF, SPF. lia.
  - exact C3.
  - exact C4.
  - exact C1.
  - apply ret_ok_codeptr_v; [unfold PF_CLR, AF_reac_segconf_parse_file; lia | reflexivity].
  - rewrite unsigned_lit_small by (unfold PF_CLR, AF_reac_segconf_parse_file; lia).
    unfold PF_CLR, AF_reac_segconf_parse_file. lia.
  - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
    unfold s0Z. rewrite C8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH.
  - intros HPRE1. eapply SRr_mono.
    { exact (REF fx lyc Sc Wc (ms_regs ms) memc mdq ch1 (p_c v) (ln + 1) (seg_litA_rc F_unknown) (ln + 1) cf
        F_unknown [AS body] HPRE1 ROD C10 Hc64 C11 Hl64 C12 Hf64 RPRE ROOM EV). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. split; [rewrite C1; reflexivity|].
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. left. split; [exact (a6_refuse_W_sub _ _ a Ha)|].
    apply a6_refuse_W_in_block in Ha. exists bc, mc. split; [exact Hinc|].
    unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE in *. lia. }
(* back at 0x880fc = CLR, at the FP state fx1 refuse returned *)
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx1 & -> & HJ2 & HJc2 & HP2 & (HRC2 & HNA2)).
unfold pf_postm, PF_POSTr.
eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HJc2 by lia.
replace (0 + EV_refuse) with 0 in HJ2 by (unfold EV_refuse; lia).
destruct HNA2 as (HP2b & Hly2 & HS2).
pose proof (a6_keeps_refuse B v pos lyc Sc Wc (ms_regs ms) memc mdq PF_SC_LINE cf ly2 S2 W2 mem2 md2 EV_refuse
  HBc HJc2 HP2b) as HK.
(* pf_base at the returned state: the heap facts re-derived from AR there (a6_base_move) *)
assert (HB2 : pf_base (fx := fx1) B v pos ly2 S2 W2 regs2 mem2 md2 PF_SC_LINE).
{ apply (a6_base_move (fx := fx) B VRO SSPX fx1 v pos lyc Sc Wc (ms_regs ms) memc mdq PF_SC_LINE ly2 S2 W2 regs2
    mem2 md2 HBc Hfx1 HJ2 Hly2 HS2 HP2b HK).
  intros r Hr. apply HP2. unfold acallee_saved. cbn [In] in Hr. lia. }
assert (HPR2 : aregs_preserved rX regs2) by exact (aregs_preserved_trans _ _ _ HPR HP2).
assert (HINV2 : INV_CLR (fx := fx1) B n v pos ly2 S2 W2 regs2 mem2 md2 (refuse cf (ln + 1) F_unknown [AS body])
  nm o ln d).
{ split; [exact HB2|]. split; [exact HMID|]. split.
  - split; [exact HRC2|]. split.
    + destruct HK as (_ & _ & _ & K4). apply (a6_nm_move v pos (rdW Wc memc) _ nm HNM).
      intros a Ha. apply K4. left. exact Ha.
    + exact (a7_cnt_refuse_next cf (ln + 1) F_unknown [AS body] (p_s v) o Ho HCNT).
  - apply (a5_rg_incl regs2 ([(18, 0x23); (24, p_c v); (27, pf_SH v pos); (19, bp)] ++ PF_RM v o ln)).
    + intros x Hx. unfold PF_RM in *. cbn [app In] in Hx |- *. tauto.
    + apply (a5_rg_pres rX regs2 _ HPR2); [|exact HRG].
      unfold PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. }
exact (HCLR fx1 v pos ly2 S2 W2 regs2 mem2 md2 (refuse cf (ln + 1) F_unknown [AS body]) nm o ln d HINV2).
Qed.

End s.

(** ** The piece pf_a7.v's a7_assemble applies *)
Theorem a7_u : A7_S_UNK B.
Proof. intros f0 n HCLR. exact (a7u_unk (fx := f0) n HCLR). Qed.

End e.
End f.
End d.
