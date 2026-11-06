(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 135 of its 172 lines of code are new or changed and 5016 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the bad-role
   refusal piece of segment B10b of reac_segconf_parse_file's walk, pb10_r_ok : PB10_R B
   (lib/B/Prog/pf_seg_B10b_k.v: HA_JOIN n -> H_BAD n). The B10b segment lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk, piece PB10_R of segment B10b;
   the function's reuse search and CONFIRM are the rule-24 lookup record,
   the rule-24 checker 2026-10-30T16:55:47Z, reuse verdict none).
   ADAPTED from a working branch's lib/A/Prog/pf_a7_u.v (the one-call piece UNK of image A's segment A7:
   seed, plain run to the jal, cl_callSF with refuse_contract, the cut rebuilt at the FP state refuse returned
   at, srr_apost_baseF_lift) and a working branch's lib/A/Prog/pf_a10b_b3.v (the same call on image A,
   0x884e8), re-derived on image B's code and registers.

   THE CODE (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s; BAD = BASE + PF_BAD = 0x88960), 8
   instructions, one program call, no inline check, no UBSan trap branch:
     0x88960 auipc a0,0xfff99
     0x88964 addi  a2,a0,-480      a2 = 0x21780 = seg_litA_rc F_badrole (listing object A_OBJ 60, .str.15)
     0x88968 ld    a0,200(s1)      a0 = c          (slot 0xc8, pf_pieces.pf_fi)
     0x8896c mv    a1,s6           a1 = ln + 1     (PF_RM)
     0x88970 ld    a3,64(s1)       a3 = cur_name = F + 0x20 (slot 0x40, PF_SL)
     0x88974 ld    a4,112(s1)      a4 = val's pointer vp in buf (slot 0x70, INV_BAD)
     0x88978 jal   refuse          -> 0x892f8 = BASE + AF_refuse (SIGP rewrites pa_sigma SS_refuse);
                                      returns at 0x8897c = BASE + PF_BADRET
     0x8897c j     0x88dc8         -> JOIN = BASE + PF_JOIN
   Counts against the kit's list for BAD (0x88960 .. 0x8897c): 7 instructions in the run to the call plus the
   `j` after it = 8 of segment B10b's 89; inline checks 0 of 0; UBSan trap sites 0 of 0 (T30 is B10b's ROLEV
   piece, 0x88d74).

   THE PROOF: the seed at BAD (pf_seg_B10b_rj.b10r_seed: every register its own atom, three read-only one-word
   regions on s1's atom for the slots 0x40, 0x70 and 0xc8, with the extra atoms 32 = c, 33 = cur_name, 34 = vp);
   one plain run (PaCallRun.paj_run_shc) to the jal, which writes no memory; the call through PaFx.cl_callSF with
   refuse_contract at BASE + AF_refuse and its premises from the closed site lemma
   pf_seg_B10b_rk.b10r_refuse_site (VERIFY rule 1j-bis); then, at the FP state fx1 refuse returned at, the cut
   JOIN rebuilt and the `j` walked (pf_seg_B10b_rj.b10r_after: pf_seg_B10b_rk.b10r_keeps_refuse and
   b10r_base_move, pfA_facts.pf_cnt_refuse with pf_next_skipn_lt for the counters, SegModel.refuse_proj for cur,
   the callee-saved registers by aregs_preserved, b10r_jump); the post is lifted to the ambient FP state by
   PaFx.srr_apost_baseF_lift and matches H_BAD's because pf_seg_B10b_f.b10b_step_none rewrites pf_role_step's
   None arm to the refusal.

   SECTION HYPOTHESES (the segment's piece list, section 3):
     REF   refuse_contract at BASE + AF_refuse, STK_refuse, RLO_A, RHI_A, seg_litA_rc, gotwA, guardA, at every
           FP state (pf_pieces.v's callee list for B10b)
     SIGP  SegObj.seg_sig_prog   (the call target pa_sigma SS_refuse is BASE + AF_refuse)
     OBJ   SegObj.seg_val_objs   (the auipc / addi pair's object atom A_OBJ 60 is seg_litA_rc F_badrole)
     VRO   SegObj.seg_val_relro  and
     SSPX  the stack-protector cells at every AR state: both FORCED by b10r_base_move after the call (refuse's
           journal keeps an image byte only when it is not an owned static, so arodata_okP needs the read-only
           window and sa_ssp needs the pinned cells), used nowhere else.
   No image fact beyond these; no IMG record hypothesis (this piece calls no printf wrapper itself). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0d_tail.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B10b_k pf_seg_B10b_f
pf_seg_B10b_rk pf_seg_B10b_rj.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac b10r_awr :=
  unfold b10r_ss, b10r_regions; cbn [ss_mem];
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.
(* the register reader, for both shapes of the symbolic state (a plain run leaves st_ok_pi, the state at a call
   is st_ok) *)
Local Ltac b10r_rreg2 HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* the program callee (pf_pieces.v's callee list for B10b), at image B's numbers, at every FP state *)
Hypothesis REF : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
(* the listing's facts over the walk's abstract instance (SegObj.v) *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
(* the stack-protector cells at every AR state (the image-A owner's route A, image B's cells) *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

Section x.
Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let b10r_RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let b10r_RUNC := SRr_run_pi_AJ_call (fx := fx) B LAWS.

Lemma b10r_bad : forall n, HA_JOIN B n -> H_BAD (fx := fx) B n.
Proof.
intros n JOIN v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HINV.
pose proof HINV as (HB & HMID & HST & HVS & HVI & HSL70 & HRH & HRG).
rewrite (b10b_step_none cf gi nm (ln + 1) val HRH).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b10r_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & Hin & EF & Hfrs & HAR & Hceil).
pose proof HGEO as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & Fapp & _).
pose proof HFI as (HJ & Hly & HFS & HPERM & HSV & HFL & HFRM & HTF & HC8 & HRG0).
pose proof asan_consts as (C1 & _).
pose proof STK_values as (_ & SRF & _ & SPF & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct HVI as [HV1 HV2].
(* the seed and the run to the jal *)
pose proof (b10r_seed B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HINV) as HS.
set (E := b10r_E rX v pos vp) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply b10r_E_img).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; apply b10r_ew_reg; exact Hk).
unfold cfg_at. change (w64 (BASE + PF_BAD)) with (Z_to_bv 64 (BASE + PF_BAD)).
paj_run_shc b10r_RUNP b10r_RUNC HS HJ.
{ b10r_awr. }
assert (Hmem : ms_mem ms = memc).
{ apply functional_extensionality. intros x. unfold frame_of in HF. rewrite HF; [reflexivity|].
  intros (r & Hr & Ha). unfold b10r_ss, b10r_regions in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
pmkst HS. rewrite Hmem in HJ |- *.
clear HF HFr HG.
(* the registers at the call *)
pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ rX (b10r_extra v pos vp) HS (b10r_E_agree rX v pos vp)
  ltac:(vm_compute; reflexivity)) as HPR.
assert (C1r : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + PF_BADRET))
  by (b10r_rreg2 HS; apply (codeptr_val _ PF_BADRET HEI)).
assert (C10 : getr (ms_regs ms) 10 = w64 (p_c v))
  by (b10r_rreg2 HS; rewrite b10r_den_atom0; subst E; apply b10r_ew_c).
assert (C11 : getr (ms_regs ms) 11 = w64 (ln + 1)).
{ b10r_rreg2 HS. rewrite b10r_den_atom0, (EE 22%nat (Z_to_bv 5 22) eq_refl).
  apply (b10r_rg rX _ 22 _ HRG). unfold PF_RL, PF_RM. b10r_in. }
assert (C12 : getr (ms_regs ms) 12 = w64 (seg_litA_rc F_badrole)).
{ b10r_rreg2 HS. rewrite b10r_den_atom0. change 301%nat with (A_OBJ 60). exact (b10r_lit_atom OBJ _ HEI). }
assert (C13 : getr (ms_regs ms) 13 = w64 (pf_F v pos + PF_O_CN))
  by (b10r_rreg2 HS; rewrite b10r_den_atom0; subst E; apply b10r_ew_cn).
assert (C14 : getr (ms_regs ms) 14 = w64 vp)
  by (b10r_rreg2 HS; rewrite b10r_den_atom0; subst E; apply b10r_ew_vp).
assert (C2 : getr (ms_regs ms) 2 = w64 (pf_s1 v)).
{ b10r_rreg2 HS. rewrite b10r_den_atom0, (EE 2%nat (Z_to_bv 5 2) eq_refl).
  apply (b10r_rg rX _ 2 _ HRG0). b10r_in. }
assert (C3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ b10r_rreg2 HS. rewrite b10r_den_atom0, (EE 3%nat (Z_to_bv 5 3) eq_refl).
  apply (b10r_rg rX _ 3 _ HRG0). b10r_in. }
assert (C4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ b10r_rreg2 HS. rewrite b10r_den_atom0, (EE 4%nat (Z_to_bv 5 4) eq_refl).
  apply (b10r_rg rX _ 4 _ HRG0). b10r_in. }
assert (C8 : getr (ms_regs ms) 8 = w64 (pf_sp0 v)).
{ b10r_rreg2 HS. rewrite b10r_den_atom0, (EE 8%nat (Z_to_bv 5 8) eq_refl).
  apply (b10r_rg rX _ 8 _ HRG0). b10r_in. }
assert (Csp : spZ (ms_regs ms) = pf_s1 v) by (unfold spZ; rewrite C2; apply b10r_w64_u; lia).
assert (Cs0 : s0Z (ms_regs ms) = pf_sp0 v) by (unfold s0Z; rewrite C8; apply b10r_w64_u; lia).
(* the cut's facts at the call state *)
assert (HBc : pf_base B v pos lyc Sc Wc (ms_regs ms) memc mdq PF_SC_LOW).
{ split; [exact HCX|]. split; [|exact (conj HOBJ (conj HSL HFSH))].
  refine (conj HJ (conj Hly (conj HFS (conj HPERM (conj HSV (conj HFL (conj HFRM (conj HTF (conj HC8 _))))))))).
  exact (b10r_rg_pres rX (ms_regs ms) _ HPR (b10r_FI_cs B v) HRG0). }
(* VERIFY rule 1j-bis at 0x88978 *)
destruct (b10r_refuse_site B n v pos lyc Sc Wc (ms_regs ms) memc mdq cf nm o ln d gi vp val (ms_regs ms)
  HBc HMID HST HVS (conj HV1 HV2) C10 C11 C12 C13 C14)
  as ((ch1 & HCH) & ROD & Hc64 & Hl64 & Hf64 & RPRE & ROOM & EV & HFPsub).
rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callSF (fx := fx) B LAWS Wc (ms_regs ms) memc _ STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdq 0
    STK_refuse (refuse_W (p_c v) cf) EV_refuse (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + PF_BADRET)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       sa_rconf (rdW W2 mem2) (p_c v) (refuse cf (ln + 1) F_badrole [AS nm; AS val]) /\
       sa_noalloc B lyc Sc ly2 S2) HJ).
  - rewrite Csp. lia.
  - apply b10r_m16; [exact S6 | exact S3].
  - lia.
  - rewrite SRF. lia.
  - rewrite SRF, SPF. lia.
  - exact C3.
  - exact C4.
  - exact C1r.
  - apply ret_ok_codeptr_v; [unfold PF_BADRET, AF_reac_segconf_parse_file; lia | vm_compute; reflexivity].
  - rewrite unsigned_lit_small by (unfold PF_BADRET, AF_reac_segconf_parse_file; lia).
    unfold PF_BADRET, AF_reac_segconf_parse_file. lia.
  - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia. rewrite Cs0. exact HCH.
  - intros HPRE1. eapply SRr_mono.
    { exact (REF fx lyc Sc Wc (ms_regs ms) memc mdq ch1 (p_c v) (ln + 1) (seg_litA_rc F_badrole) (ln + 1) cf
        F_badrole [AS nm; AS val] HPRE1 ROD C10 Hc64 C11 Hl64 C12 Hf64 RPRE ROOM EV). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. split; [rewrite C1r; reflexivity|].
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - exact HFPsub. }
(* back at 0x8897c, at the FP state fx1 refuse returned *)
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2' & regs2 & mem2 & md2 & Hfx1 & -> & HJ2 & HJc2 & HP2 & (HRC2 & HNA2)).
unfold pf_postm, PF_POSTr.
eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HJc2 by lia.
replace (0 + EV_refuse) with 0 in HJ2 by (unfold EV_refuse; lia).
exact (b10r_after B VRO SSPX fx1 n (JOIN fx1) v pos lyc Sc Wc rX (ms_regs ms) memc mdq cf nm o ln d gi val
  ly2 S2' W2 regs2 mem2 md2 HBc HMID HST HRG HPR Hfx1 HJ2 HJc2 HP2 HRC2 HNA2).
Qed.
End x.

(* the piece of pf_seg_B10b_k.v at every ambient FP state *)
Theorem pb10_r_ok : PB10_R B.
Proof. intros f0 n JOIN. exact (b10r_bad (fx := f0) n JOIN). Qed.
End d.
