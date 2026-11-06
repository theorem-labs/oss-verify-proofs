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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 240 of its 289 lines of code are new or changed and 5004 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): segment B1 of
   reac_segconf_parse_file's walk, the theorem S_B1_holds : S_B1 B of lib/B/Prog/pf_pieces.v (ENTRY -> FTAKEN).
   The B1 segment lane of the image-B G3 walk owner, 2026-10-30.
   proves function reac_segconf_parse_file (segment B1; reuse search and CONFIRM:
   the rule-24 lookup record, the rule-24 checker 2026-10-30T16:55:47Z; reuse verdict: none
    released; ADAPTED from the image-A G3 walk owner's image-A segment walks (the image-A A1 segment lane's working branch had no A1 file when this was
   written; the segment form is its A2 lane's lib/A/Prog/pf_a2.v) and the unit owner's UBSan piece walks, re-derived on
   image B's code).
   THE CODE (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s, 0x87e38 .. 0x87edc, 41 instructions; plan
   PLAN-pf-asanubsan.md section 5.2 row B1 and section 1.2):
     0x87e38 .. 0x87e7c  frame 352, probe, 13 saves (ra .. s11 at sp0 - 8 .. sp0 - 104), s0 = sp0, the realignment
                         `andi sp,sp,-32`, s1 = sp
     0x87e80, 0x87e84    s3 = label, s11 = text
     0x87e88 .. 0x87e9c  the GOT words 0xa3210 (shadow base cell) and 0xa3268 (use-after-return flag), the flag,
                         s4 = the shadow base
     0x87ea0             c to slot s1 + 0xc8
     0x87ea4             beqz a2 (flag 0): not taken, the flag is AR's constant 1 (decided by the executor)
     0x87ea8, 0x87eac    li a0,1152; jal frame_alloc_5 = __asan_stack_malloc_5 (the class-5 take)
     0x87eb0, 0x87eb8    j 0x87eb8; mv a3,a0
     0x87ebc             bnez a0,0x87edc: taken, a0 = F >= 4096 (the kit's astack_malloc_realizes returns the frame)
   Dead under the premises: 0x87eb4 (li a0,0: the flag is 1) and the real-stack fallback 0x87ec0 .. 0x87ed8 (a0 <> 0).
   COUNTS against the plan's row B1 (41 instructions, 3 conditional branches, 1 call, no check, no trap): instructions
   walked 33 of 41 (0x87e38 .. 0x87eac by the first run, 0x87eb0 / 0x87eb8 / 0x87ebc by the second; the 8 dead ones
   0x87eb4, 0x87ec0 .. 0x87ed8 are excluded by the two decided branches); conditional branches decided 2 of 3 on the
   live path (beqz 0x87ea4, bnez 0x87ebc; the probe loop's blt 0x87ed4 is in the dead fallback); calls 1 of 1
   (frame_alloc_5 0x87eac); instrumented checks 0 of 0; UBSan trap sites 0 of 0.
   THE PROOF: a plain run of the symbolic executor from the seed b1_entry (lib/B/Prog/pf_seg_B1_e.v) to the call; the
   call by PaCall.v aj_stack_malloc_atS (the Section hypothesis ASM5 at the listing's call target, through PaLibF.v's
   palf_sm); a plain run from a fresh seed at the return 0x87eb0 (a0 = F with F's range as a fact) to FTAKEN 0x87edc; at
   FTAKEN, INV_FTAKEN from: the journal of the runs and the call, the saved registers and c's slot read off the first
   run's stack regions and kept by the call (they lie above its window [s1 - ESTACK, s1)), the frame facts of the
   stack-malloc post, and the cut's objects re-given at the new reader by lib/B/Prog/pf_seg_B1_k.v.
   SECTION HYPOTHESES: ASM5 and SMP (pf_pieces.v's frame take for B1: astack_malloc_realizes 5 at every FP state,
   stack_malloc_progressP); TL, TLF (the listing's runtime records PALib / PALibF: the GOT words, the cells, the
   stack-malloc call targets); VRO (the listing's read-only range, SegObj.v); SSPX (the stack-protector cells at every
   AR state, as lib/B/Prog/reac_segconf_parse.v takes it). The model's laws aj_stack_malloc_atS asks are not a
   hypothesis: YG05.model_laws_ok gives them from the entry AR's universe_ok (ARm's am_universe).
   POSITIONAL NAMES: listing objects 0, 1, 12 (the shadow GOT word 0xa3210, the flag GOT word 0xa3268, the shadow cell)
   are B's (B's SegList.v slots at 0x87e88 .. 0x87e94 name A_OBJ 0 / A_OBJ 1; PALib's pal_got_shadow / pal_cell and
   PALibF's palf_got_uar tie them to the record); the call target SS___asan_stack_malloc_5 is B's SegList.v slot at
   0x87eac; the cut pcs are pf_pieces.v's (pf_cut_pcs). No region letter or STK row of an A table is used. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q YG05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B1_e pf_seg_B1_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small facts and tactics (pf_a2.v's, B1 names) ---------- *)
Lemma b1_den0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma b1_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr r = v -> getr rr (Z_to_bv 5 k) = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned. exact H. Qed.
Lemma b1_m16 : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof. intros a b Ha Hb. rewrite Zminus_mod, Ha, Hb. reflexivity. Qed.
Ltac b1_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
Ltac b1_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
Ltac b1_in := solve [cbn [In app]; repeat first [left; reflexivity | right]].

(* the fresh state at frame_alloc_5's return 0x87eb0: every register its own atom, a0 (atom 10) = F in the class-5
   frame's range, no memory region (j, mv, bnez touch no memory) *)
Definition b1_ss1 : sstate := mkSS B1_SM_RET sr_atoms [] None (mkFacts [(10%nat, mkAF 4096 (2 ^ 47) 5)] [] []).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* pf_pieces.v's frame take for B1, at every FP state: __asan_stack_malloc_5 (the call target pa_sigma
   SS___asan_stack_malloc_5 is pc_stack_malloc 5 by PALibF's palf_sm) *)
Hypothesis ASM5 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 5.
Hypothesis SMP : stack_malloc_progressP B.
(* the listing's runtime records at image B (lib/B/Prog/SegPaLib.v PALib, PaLibF.v PALibF) *)
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* the listing's read-only range (B's SegObj.v) *)
Hypothesis VRO : seg_val_relro (PI := PI).
(* SSPX (the image-A G3 walk owner's hypothesis, image B's cells; lib/B/Prog/reac_segconf_parse.v takes it too): the
   stack-protector cells at every AR state, which the allocator record pins *)
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

(* a word a symbolic region holds (pf_a2.v's pa2_word_of_region) *)
Lemma b1_word_of_region : forall E H m n b lo hi wlo whi cs od e v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H m) (b + od) = Some v.
Proof.
intros E H m n b lo hi wlo whi cs od e v HR Hb Hin He Hv.
pose proof (field_of_region_any (segs := SEGS) E (mrestrict H m) n b cs lo hi wlo whi od 8 e HR Hb Hin
  ltac:(cbn; lia)) as HV.
rewrite He, unsigned_lit_small in HV by lia. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in HV.
rewrite Z.mod_small in HV by lia. change (N.to_nat 8) with 8%nat in HV.
apply rdword_of_val_mem; [exact HV | exact Hv].
Qed.

Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let errno_low := pal_env B TL.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNTO := SRr_run_to_pi_AJ B LAWS.

Lemma b1_main : HA_FTAKEN B -> H_ENTRY B.
Proof.
intros HFT v HCX HFRM.
pose proof HCX as (HPRE & HROD & H10 & Hc64 & H11 & Ht64 & H12 & Hl64 & (fe0 & HPF) & Hroom & HEV).
pose proof HPF as (HRP & _).
pose proof HRP as (C0 & C16 & _ & _ & _ & _ & _ & _ & _ & _ & LS & _).
(* fe0 is the entry's FP state inside pf_cx's existential; drop it so that no implicit FP state resolves to it *)
clear HPF HRP fe0.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the model's laws for the record's trace universe, from the entry AR (aj_stack_malloc_atS asks them) *)
pose proof (YG05.model_laws_ok (as_universe B) (am_universe _ _ _ _ (proj1 HAR))) as ML.
pose proof STK_values as (_ & _ & _ & ESTK & _).
pose proof pa_B_ok as HBASE.
pose proof (b1_entry (fx := fx) B LAWS TL TLF STK_reac_segconf_parse_file (p_W v) (p_ly v) (p_S v) (p_regs v)
  (p_mem v) (p_md v) (p_ch v) HPRE ltac:(rewrite ESTK; lia)) as HS.
pose proof (ajournal_init SEGS B STK_reac_segconf_parse_file (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
  (p_regs v) (p_mem v) (p_md v) (p_ch v) HPRE) as HJ.
set (sp0 := spZ (p_regs v)) in *.
destruct (b1sp1_facts sp0 Hal16) as (Hs1al & Hs1).
set (s1 := b1sp1 sp0) in *.
set (E := Eimg (Ereg (p_regs v) (b1_extra sp0 (as_uar_cell B)))) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (p_regs v) r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (p_regs v) _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 s1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra (p_regs v) _ 1)).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (U33 : bv_unsigned (ew E 33) = s1) by (rewrite E33; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 (BASE + PF_ENTRY)) with (Z_to_bv 64 (BASE + AF_reac_segconf_parse_file)).
(* ---- the prologue: 0x87e38 .. the call of frame_alloc_5 at 0x87eac ---- *)
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hr & Ha). unfold ss_b0, b1_regions0 in Hr. cbn [ss_mem In] in Hr.
  left. rewrite ESTK.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]];
    unfold b1_stk_lo, b1_stk_hi, b1_stk_c, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP in Ha;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?Usp, ?U33 in Ha; lia. }
b1_clear_md.
(* what the run kept: every byte outside its stack slots, so every byte below alloc_ceiling *)
assert (KL : forall a, 0 <= a < alloc_ceiling -> rdW (p_W v) (ms_mem ms) a = rdW (p_W v) (p_mem v) a).
{ intros a Ha.
  apply (kept_of_frame (segs:=SEGS) E (ss_mem ss_b0) (w_H (p_W v)) (p_mem v) (ms_mem ms)
    (fun a => sp0 - 368 <= a < sp0) HFr); [| lia | lia].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin'];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?U33 in Hrr; lia |]).
  destruct Hin'. }
clear HF HFr HG.
(* the regions of the saved registers and of c's slot *)
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H (p_W v)) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H (p_W v)) msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as HR2 end.
cbn [ms_mem restrict] in HR1, HR2.
(* the registers at the call *)
assert (Q1 : getr (ms_regs ms) 1%bv = Z_to_bv 64 (BASE + B1_SM_RET)) by (b1_rreg HS; apply (codeptr_val _ B1_SM_RET HEI)).
assert (Q2 : getr (ms_regs ms) 2%bv = Z_to_bv 64 s1) by (b1_rreg HS; rewrite b1_den0; exact E33).
assert (Q3 : getr (ms_regs ms) 3%bv = w64 (as_gp B)) by (b1_rreg HS; rewrite b1_den0, (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (Q4 : getr (ms_regs ms) 4%bv = w64 (as_tp B)) by (b1_rreg HS; rewrite b1_den0, (EE 4%nat 4%bv eq_refl); exact Htp).
assert (QK : forall k val, In (k, val) [(2, s1); (3, as_gp B); (4, as_tp B); (8, sp0); (9, s1); (19, p_lp v);
    (20, SHADOW_OFF); (27, p_t v)] -> getr (ms_regs ms) (Z_to_bv 5 k) = w64 val).
{ intros k val Hk. cbn [In] in Hk.
  repeat (destruct Hk as [Hk | Hk]; [injection Hk as <- <-; b1_rreg HS; rewrite b1_den0 |]); [..|destruct Hk].
  - exact E33.
  - rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl). exact (b1_bvr _ 3%bv 3 _ eq_refl Hgp).
  - rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl). exact (b1_bvr _ 4%bv 4 _ eq_refl Htp).
  - rewrite (EE 2%nat (Z_to_bv 5 2) eq_refl). unfold w64, sp0, spZ. rewrite (b1_bvr _ 2%bv 2 _ eq_refl eq_refl).
    symmetry. apply Z_to_bv_bv_unsigned.
  - exact E33.
  - rewrite (EE 12%nat (Z_to_bv 5 12) eq_refl). exact (b1_bvr _ 12%bv 12 _ eq_refl H12).
  - exact E32.
  - rewrite (EE 11%nat (Z_to_bv 5 11) eq_refl). exact (b1_bvr _ 11%bv 11 _ eq_refl H11). }
(* ---- the call of __asan_stack_malloc_5 (0x87eac, a0 = 0x480, return 0x87eb0) at sp = s1 ---- *)
pmkst HS.
assert (Hsm : pa_sigma SS___asan_stack_malloc_5 = pc_stack_malloc (as_code B) 5)
  by exact (palf_sm B TLF 5 ltac:(right; right; right; left; reflexivity)).
rewrite Hsm.
pose proof (count_cid_le_length 5 (frames (p_S v))) as Hcnt.
assert (HFS : 9 <= fs_frames 5) by (vm_compute; discriminate).
unfold sa_room_n in Hroom.
eapply SRr_bind.
{ eapply (aj_stack_malloc_atS SEGS B LAWS pa_segs_low errno_low ML SMP 5 (ASM5 fx) ltac:(lia) (p_W v) (ms_regs ms)
    (ms_mem ms) STK_reac_segconf_parse_file sp0 (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v)
    (p_md v) [] (p_ly v) (p_S v) _ 0 (s1 - sp0) _ HJ).
  - unfold spZ at 1. rewrite Q2, unsigned_lit_small by lia. lia.
  - apply b1_m16; [|exact Hal16]. apply Z.mod_divide in Hs1al as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 32) with ((2 * q) * 16) by lia. apply Z_mod_mult.
  - lia.
  - rewrite ESTK. unfold ESTACK. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [unfold B1_SM_RET, AF_reac_segconf_parse_file; lia | reflexivity].
  - lia. }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2
  & Hbb2 & Hz & Hflag & HK & HJ1 & (fS2 & ES2)).
pose proof (proj1 HJ2) as HAR2.
assert (Hfin2 : In (5, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 5 pos HAR2 Hfin2) as (HF32 & _ & _ & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 5 pos HAR2 Hfin2) as (HF4096 & HFceil & _).
change (fs_frame_bytes 5) with 2048 in HFceil, Hz, Hflag.
set (F := frame_addr (p_ly v) 5 pos) in *.
(* the stack slots above s1 are kept by the call *)
assert (KS : forall a, s1 <= a < sp0 -> rdW (p_W v) mem2 a = rdW (p_W v) (ms_mem ms) a).
{ intros a Ha. apply (proj1 HK); [rewrite ESTK in Hslo; lia | unfold ESTACK; lia]. }
(* ---- 0x87eb0 j; 0x87eb8 mv a3,a0; 0x87ebc bnez a0 (taken: a0 = F) to FTAKEN 0x87edc ---- *)
set (E2 := Eimg (Ereg regs2 [])).
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
  by (intros n r Hn; subst E2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U10 : bv_unsigned (ew E2 10) = F)
  by (rewrite (EE2 10%nat 10%bv eq_refl), Ha0; unfold w64; apply unsigned_lit_small; lia).
assert (HS2 : st_ok_pi SEGS VAL E2 b1_ss1
  (restrict (w_H (p_W v)) (mkst regs2 (Z_to_bv 64 (BASE + B1_SM_RET)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold b1_ss1. apply pa_entry_st_ok_full.
  - subst E2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U10. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
paj_run_to_sh RUNTO HS2 HJ2 PF_FTAKEN.
{ intros a (r & Hr & _). unfold b1_ss1 in Hr. cbn [ss_mem In] in Hr. destruct Hr. }
match goal with HS2 : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms3 end.
match goal with H : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => rename H into HFr3 end.
cbn [ms_mem mkst] in HFr3.
b1_clear_md.
(* the run touched no memory *)
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> rdW (p_W v) (ms_mem ms3) a = rdW (p_W v) mem2 a).
{ intros a Ha.
  apply (kept_of_frame (segs:=SEGS) E2 (ss_mem b1_ss1) (w_H (p_W v)) mem2 (ms_mem ms3) (fun _ => False) HFr3);
    [| exact Ha | intros []].
  intros b wlo whi a' Hin' _. vm_compute in Hin'. destruct Hin'. }
(* the registers at FTAKEN *)
assert (G3 : forall k, In k [2; 3; 4; 8; 9; 19; 20; 27] ->
  getr (ms_regs ms3) (Z_to_bv 5 k) = getr (ms_regs ms) (Z_to_bv 5 k)).
{ intros k Hk. cbn [In] in Hk.
  repeat (destruct Hk as [Hk | Hk];
    [subst k; rewrite <- HP2 by (unfold acallee_saved; lia); b1_rreg HS2; rewrite b1_den0; apply EE2; reflexivity |]).
  destruct Hk. }
assert (G10 : getr (ms_regs ms3) (Z_to_bv 5 10) = w64 F).
{ b1_rreg HS2. rewrite b1_den0, (EE2 10%nat (Z_to_bv 5 10) eq_refl). exact (b1_bvr _ 10%bv 10 _ eq_refl Ha0). }
assert (G13 : getr (ms_regs ms3) (Z_to_bv 5 13) = w64 F).
{ b1_rreg HS2. rewrite b1_den0, (EE2 10%nat (Z_to_bv 5 10) eq_refl). exact (b1_bvr _ 10%bv 10 _ eq_refl Ha0). }
pmkst HS2.
lazymatch goal with |- SRr _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (BASE + ?p)) _ _; cfg_model := _ |} _ =>
  change (Z_to_bv 64 (BASE + p)) with (w64 (BASE + PF_FTAKEN)) end.
pose proof (proj1 HJ2) as HAR3.
assert (Hfr : forall cid p0, In (cid, p0) (frames (p_S v)) -> In (cid, p0) (frames S2))
  by (intros cid p0 Hin; rewrite Hfrs2; right; exact Hin).
assert (KK : b1_K B (p_ly v) (p_S v) (rdW (p_W v) (p_mem v)) (rdW (p_W v) (ms_mem ms3)))
  by exact (b1_K_chain B (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) (ms_mem ms) mem2 (ms_mem ms3) _ _ HAR KL HK K3).
(* ---- FTAKEN ---- *)
apply (HFT fx v pos (p_ly v) S2 (p_W v)).
split; [exact HCX|].
split.
{ split; [exact HJ2|]. split; [reflexivity|]. split; [exists fS2; exact ES2|].
  split; [rewrite Eab; apply Permutation_refl|].
  split.
  { (* the saved registers: the first run's region 1, kept by the call and the second run *)
    intros j rr Hj.
    do 13 (destruct j as [|j]; [cbn [nth_error PF_SAVED] in Hj; injection Hj as <-;
      lazymatch goal with |- rdword _ (_ - 8 - 8 * Z.of_nat ?k) = Some (bv_unsigned (getr (p_regs v) (Z_to_bv 5 ?r))) =>
        let off := eval cbv in (- 8 - 8 * Z.of_nat k) in
        let kr := eval cbv in (Z.to_nat r) in
        replace (pf_sp0 v - 8 - 8 * Z.of_nat k) with (sp0 + off) by (unfold sp0, pf_sp0; cbn; lia);
        rewrite (rdword_ext (rdW (p_W v) (ms_mem ms)) (rdW (p_W v) (ms_mem ms3)))
          by (intros q Hq; rewrite K3 by lia; apply KS; lia);
        apply (b1_word_of_region E (w_H (p_W v)) (ms_mem ms) 2 sp0 _ _ _ _ _ off (SOff kr 0) _ HR1 Usp);
        [ b1_in
        | rewrite b1_den0, (EE kr (Z_to_bv 5 r)) by reflexivity; symmetry; apply Z_to_bv_bv_unsigned
        | apply (bv_unsigned_in_range 64) ] end |]).
    cbn in Hj. destruct j; discriminate. }
  split.
  { (* the flag word of the frame, the stack-malloc post *)
    unfold pf_F, pf_FL. fold F. change (fs_frame_bytes 5) with 2048.
    rewrite (rdword_ext (rdW (p_W v) mem2) (rdW (p_W v) (ms_mem ms3))) by (intros q Hq; apply K3; lia).
    exact Hflag. }
  split; [exact HFRM|].
  split.
  { unfold pf_tf, pf_F. fold F. change (fs_frame_bytes 5) with 2048.
    split; [exact C0|]. split; [exact C16|]. split; [exact HF4096|]. split; [lia | exact LS]. }
  split.
  { (* c in slot 0xc8: the first run's region 2 *)
    apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. change (pf_s1 v) with s1.
    rewrite (rdword_ext (rdW (p_W v) (ms_mem ms)) (rdW (p_W v) (ms_mem ms3)))
      by (intros q Hq; rewrite K3 by lia; apply KS; lia).
    apply (b1_word_of_region E (w_H (p_W v)) (ms_mem ms) 33 s1 _ _ _ _ _ 200 (SOff 10 0) (p_c v) HR2 U33);
      [b1_in | rewrite b1_den0, (EE 10%nat 10%bv eq_refl); exact H10 | exact Hc64]. }
  repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    first [ rewrite (G3 2) by b1_in; exact (QK 2 _ ltac:(b1_in))
          | rewrite (G3 3) by b1_in; exact (QK 3 _ ltac:(b1_in))
          | rewrite (G3 4) by b1_in; exact (QK 4 _ ltac:(b1_in))
          | rewrite (G3 8) by b1_in; exact (QK 8 _ ltac:(b1_in))
          | rewrite (G3 9) by b1_in; exact (QK 9 _ ltac:(b1_in))
          | rewrite (G3 20) by b1_in; exact (QK 20 _ ltac:(b1_in)) ]. }
split; [eapply b1_keep_obj; eassumption|].
split; [eapply b1_keep_lab; eassumption|].
split; [eapply b1_keep_rconf; eassumption|].
split.
{ unfold zero_shadow, pf_F. fold F. change (fs_frame_bytes 5) with 2048. intros i Hi.
  rewrite K3; [exact (Hz i Hi) |]. unfold shadow_of_addr, SHADOW_OFF.
  pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)). assert (F / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
  first [ exact G10 | exact G13
        | rewrite (G3 19) by b1_in; exact (QK 19 _ ltac:(b1_in))
        | rewrite (G3 27) by b1_in; exact (QK 27 _ ltac:(b1_in)) ].
Qed.
End x.

(* the segment statement of pf_pieces.v at every FP state *)
Theorem S_B1_holds : S_B1 B.
Proof. intros f0 HF. exact (b1_main (fx := f0) HF). Qed.
End d.
