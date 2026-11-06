(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/RPgCheckStr.v at 77f59d02b01 (the call in the middle of a walk: the run
   to the jal, the callee's contract through SRr_bind, a fresh entry state at the return pc; L_ANS_cs as tl_L4_cs and
   ch_L_cs) for the MATCH HALF of reac-pw/fuzz_role's image-A segment M02: the tail and the two checks, proved
   against lib/A/RPgSeg.v's rs_piece_W11b_tail_stmt and rs_piece_W11b_checks_stmt on lib/A/Img0.v rsegs. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgM02Tail.v, with its module paths, module names, addresses and numbers changed; 283 of its 388 lines of code are new or changed and 852 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW14Tail.v and the parts of
   proofs/reac-pw/fuzz_rate/lib/A/RtPgW14Base.v it uses, at 2d46ab19875e, for image B (fuzz_rate.asan-ubsan): image B's
   pcs, callee entries, tables and literals; C4 reads s3 (not s4) and the real-frame cells R+0x10 / 0x18 / 0x60 / 0x148 /
   0x168 / 0x178; the frame for locals is a class-4 frame whose shadow at C4 is rsb_PB (88 bytes); the two u64 tables'
   zone moves into image B's first writable segment; the M02 layer is lib/AU/RtPgM02BaseB.v's. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, whose loaded code bytes are the pin's). Proves no
   function (kind: segment lemma): the piece W14-tail of LLVMFuzzerTestOneInput's segment M02, whose statement is
   lib/AU/RtPgSegB.v's rsb_piece_W14_tail_stmt; nothing here restates a cut.

   THE TAIL (rsb_cut_T2 at T2 0x82f8c -> rsb_cut_C4 at C4 0x82f9c), fuzz_rate.c:270 check_code(reac_rate_refuse_code(4), 4):
     0x82f8c addi a0,zero,4; 0x82f90 jal 0x841b4 reac_rate_refuse_code (ra 0x82f94);
     0x82f94 addi a1,zero,4; 0x82f98 jal 0x8360c check_code (ra 0x82f9c = C4).
   - w14t_s1: a run 0x82f8c .. the callee's entry from an entry state with no region (the code between the cut and
     the call only sets a0), reac_rate_refuse_code's contract (the Section hypothesis REFUSE) through SRr_bind with
     RtPgM02BaseB.m2b_pre_call for its rt_cpre and m2b_core_call for rsb_core at the return: a0 = codes[4] = 0x21680
     (rt_refuse at r = 4).
   - w14t_s2: the run 0x82f94 .. check_code's entry, check_code's contract (CODE) with s = 0x21680 and r = 4: the
     text at 0x21680 is rt_refuse_txt 4, the table switch.table.check_code (0x9bf40) and its four strings and the
     literal "none" (0x215c0) are w14t_strs at the call's memory; m2b_core_call at the return C4.
   - What C4 reads (hi_L4 = RtPgSegB's rsb_L_dec: s0 = S, s1 = R, s3 = the frame's shadow base, and the six
     real-frame cells R+0x10, 0x18, 0x60, 0x148, 0x168, 0x178) is carried from the T2 cut: the three registers are
     callee-saved and not written by the tail, and no byte outside the callees' stack [R - T_SEG_STK, R) is written;
     the frame's shadow (rsb_PB, 88 bytes) lies below the allocator's ceiling, so it is kept too (w14t_cut_C4).
   - w14t_tz: the two 8-byte tables switch.table.check_code (0x9bf40, 4 entries) and reac_rate_refuse_code.codes
     (0x9bf80, 5 entries), both in .data.rel.ro inside image B's first writable PT_LOAD [0x9b998, 0x9d000), lie in the
     zone [0x9bc00, 0x9c000); with its shadow bytes no byte of the zone is in M02's write set (hi_w2) or in the callees'
     stack (w14t_tz_ok), so the tables read the same at every cut (w14t_u64_kept).
   Both callees return at the float state they are called at, so every state of the tail is at the cut's own float
   state fx2; the walk lemmas are stated at the configurations' float state (Section w) and used at fx2.

   SECTION HYPOTHESES of rt_w14_tail_B (Section m): MTL : ameter_laws MT; REFUSE : reac_rate_refuse_code's contract
   rt_refuse_code_specX at 0x841b4 (table 0x9bf80, cov 0x21600, codes 0x21600 .. 0x21680) at every float state;
   CODE : check_code's contract rt_check_code_specX at 0x8360c (table 0x9bf40, lnone 0x215c0, strings 0x21540 ..
   0x215a0) at every float state. The frame's laws are the kernel theorem YG0q.AR_laws_ok. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgSegB RtPgMemB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgCheck RtPgM02BaseB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require RtPgStepsB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================= the image ======================================= *)
Definition W14T_T2 : Z := 0x82f8c.
Definition W14T_T2R : Z := 0x82f94.         (* reac_rate_refuse_code's return address *)
Definition W14T_C4 : Z := 0x82f9c.
Definition W14T_REFUSE : Z := 0x841b4.      (* reac_rate_refuse_code *)
Definition W14T_CODE : Z := 0x8360c.        (* check_code *)
Definition W14T_RF_TBL : Z := 0x9bf80.      (* reac_rate_refuse_code.codes *)
Definition W14T_RF_COV : Z := 0x21600.
Definition W14T_RF_CS : list Z := [0x21600; 0x21620; 0x21640; 0x21660; 0x21680].
Definition W14T_CC_TBL : Z := 0x9bf40.      (* switch.table.check_code *)
Definition W14T_CC_LNONE : Z := 0x215c0.
Definition W14T_CC_CS : list Z := [0x21540; 0x21560; 0x21580; 0x215a0].

(* the 4 words 0x82f8c .. 0x82f98 (the tail) *)
Definition w14t_tbl : ctable := Eval vm_compute in (build_table rsegs W14T_T2 4 TEmpty).
Lemma w14t_tbl_eq : w14t_tbl = build_table rsegs W14T_T2 4 TEmpty.
Proof. vm_cast_no_check (eq_refl w14t_tbl). Qed.
Lemma w14t_tbl_ok : table_ok rsegs w14t_tbl.
Proof. rewrite w14t_tbl_eq. apply build_table_ok0. unfold W14T_T2. lia. Qed.

(* No instrumented check lies in the range, so the runs are the plain engine's (YCbq aj_run): no shadow entry and no
   static shadow check. *)
Ltac w14t_run awr :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
aj_run w14t_tbl_ok HS HJ; [awr | ] end.

(* sp / gp / tp kept by a run that leaves their atoms in place *)
Lemma w14t_r234 : forall r1 r2, cs_eq [2; 3; 4]%bv r1 r2 ->
forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr r2 (Z_to_bv 5 r) = getr r1 (Z_to_bv 5 r).
Proof.
intros r1 r2 H r Hr; destruct Hr as [Hr|[Hr|Hr]]; subst r; apply H; cbv [In];
repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.
Lemma w14t_sp234 : forall r1 r2, cs_eq [2; 3; 4]%bv r1 r2 -> spZ r2 = spZ r1.
Proof. intros r1 r2 H. apply (m2b_sp_of_cs [2; 3; 4]%bv r1 r2); [cbv [In]; left; reflexivity | exact H]. Qed.

(* ======================================= the two tables ======================================= *)
(* [0x9bc00, 0x9c000) holds switch.table.check_code [0x9bf40, 0x9bf60) and reac_rate_refuse_code.codes
   [0x9bf80, 0x9bfa8); its shadow bytes are SHADOW_OFF + [0x13780, 0x13800) *)
Definition w14t_tz (a : Z) : Prop :=
(0x9bc00 <= a < 0x9c000) \/ (SHADOW_OFF + 0x13780 <= a < SHADOW_OFF + 0x13800).

(* [0x9bc00, 0x9c000) lies inside image B's first writable PT_LOAD [0x9b998, 0x9d000) *)
Lemma w14t_tz_img : forall a, 0x9bc00 <= a < 0x9c000 -> in_img rsegs a.
Proof.
intros a Ha.
assert (H1 : existsb (fun s : Segment => (Z.of_N (seg_base s) <=? 0x9bc00) &&
  (0x9c000 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in H1. destruct H1 as (sg & Hin & Hb).
apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
exists sg. split; [exact Hin | lia].
Qed.

(* the registers the C4 cut reads (hi_L4): s0, s1, s3, all callee-saved and not written by the tail *)
Definition w14t_L4 : list (bv 5) := [8; 9; 19]%bv.
Lemma w14t_L4_cs : forall r, In r w14t_L4 -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. cbv [w14t_L4 In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia | ]).
destruct Hr.
Qed.
Ltac w14t_cs_get Hcs r :=
etransitivity; [exact (Hcs r ltac:(cbv [w14t_L4 In]; repeat (first [left; apply bv_eq; reflexivity | right])))|].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* No byte of the zone is in M02's write set or in the callees' stack: its image bytes by m2b_keep_img; the shadow
   byte of hi_w2 at shadow_addr F + 0x54 in the zone would put F + 0x2a0, a byte of F, in the image. *)
Lemma w14t_tz_ok : forall cx : rsb_scx rsegs, rsb_pre rsegs B cx ->
In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
forall a, w14t_tz a ->
0 <= a < 2 ^ 64 /\ ~ (spZ (x_regs rsegs cx) - T_SEG_STK <= a < spZ (x_regs rsegs cx)) /\ ~ rsb_E2 rsegs cx a.
Proof.
intros cx Hpre Hpod a [Ha|Ha]; [exact (m2b_keep_img B cx Hpre Hpod a (w14t_tz_img a Ha))|].
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2b_stack B cx Hpre) as (HR & _ & _ & _ & Hc & H46 & _).
pose proof (m2b_frameF B cx Hpre) as (F32 & F4096 & Fceil & Fapp & Fimg).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
pose proof Hpre as Hpre'. unfold rsb_pre, rt_seg_pre in Hpre'. destruct Hpre' as (HJ & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpod) as (_ & P4096 & Pceil & Papp & _).
assert (Hreq : q_len (x_e rsegs cx) <= req_size (q_len (x_e rsegs cx)))
by (unfold req_size; destruct (Z.eqb_spec (q_len (x_e rsegs cx)) 0); lia).
assert (HF8 : q_F (x_e rsegs cx) = 8 * (q_F (x_e rsegs cx) / 8)).
{ pose proof (Z.div_mod (q_F (x_e rsegs cx)) 8 ltac:(lia)) as D.
  assert (q_F (x_e rsegs cx) mod 8 = 0)
    by (rewrite <- (Z.mod_mod_divide _ 32 8) by (exists 4; lia); rewrite F32; reflexivity).
  lia. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp, Papp.
rewrite HR. unfold T_SEG_STK, ASTACK. unfold SHADOW_OFF in Ha.
split; [lia|]. split; [lia|].
unfold rsb_E2, rt_inw. cbn [hi_w2 rate_himg_B]. intros [Hw|Hw].
- rewrite !Exists_cons, Exists_nil in Hw. cbn [rt_xv fst snd] in Hw.
  destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[]]]]]]];
  try unfold shadow_addr in Hw; try unfold SHADOW_OFF in Hw;
  first
  [ lia
  | (apply (Fimg (q_F (x_e rsegs cx) + 0x2a0)); [lia | apply w14t_tz_img; lia]) ].
- lia.
Qed.
End d.

(* a table of the zone whose bytes and shadow bytes read the same in another world and memory is the same table *)
Lemma w14t_u64_kept : forall H H' (m m' : word -> option byte) t vs,
(forall x, w14t_tz x -> aview rsegs H' m' x = aview rsegs H m x) ->
0x9bc00 <= t -> t + 8 * Z.of_nat (length vs) <= 0x9c000 ->
rt_u64tab rsegs H m t vs -> rt_u64tab rsegs H' m' t vs.
Proof.
intros H H' m m' t vs HK Ht Hb (Himg & Hal & Hvs & Hv & Hra).
split; [exact Himg|]. split; [exact Hal|]. split; [exact Hvs|].
split.
- intros i Hi. eapply (val_mem_kept rsegs); [|exact (Hv i Hi)]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
  apply HK. left. lia.
- apply (rtmb_ra_kept rsegs H m H' m'); [exact Hra|]. intros x Hx. apply HK. right.
  unfold shadow_of_addr, SHADOW_OFF.
  assert (0x13780 <= x / 8 < 0x13800) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  lia.
Qed.

Section d2.
Variable B : asyms.
Variable MT : ameter_ops.

(* the premises reac_rate_refuse_code and check_code read, at a cut's memory *)
Lemma w14t_strs : forall (cx : rsb_scx rsegs) ly2 S2 W2 regs2 mem2 md2,
rsb_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
rt_u64tab rsegs (w_H W2) mem2 W14T_RF_TBL W14T_RF_CS /\
rt_u64tab rsegs (w_H W2) mem2 W14T_CC_TBL W14T_CC_CS /\
(forall i, 0 <= i < 4 -> rt_cstr rsegs (w_H W2) mem2 (nth (Z.to_nat i) W14T_CC_CS 0) (rt_code_of_txt (i + 1))) /\
rt_cstr rsegs (w_H W2) mem2 W14T_CC_LNONE (rt_code_of_txt 0) /\
rt_cstr rsegs (w_H W2) mem2 0x21680 (rt_refuse_txt 4).
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore.
assert (HK : forall x, m2b_kz x -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx) x).
{ intros x Hx. destruct (m2b_kz_ok B cx Hpre Hpod x Hx) as (Hx64 & Hstk & HE).
  destruct Hcore as (_ & _ & _ & _ & _ & _ & HKc). exact (HKc x Hx64 Hstk HE). }
assert (HT : forall x, w14t_tz x -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx) x).
{ intros x Hx. destruct (w14t_tz_ok B cx Hpre Hpod x Hx) as (Hx64 & Hstk & HE).
  destruct Hcore as (_ & _ & _ & _ & _ & _ & HKc). exact (HKc x Hx64 Hstk HE). }
pose proof Hpre as Hpre'. unfold rsb_pre in Hpre'.
destruct (m2b_site_strs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre')
as (SC & SN & SR & _ & _ & _ & _ & _ & _ & _ & _ & UC & UR).
split; [apply (w14t_u64_kept _ _ _ _ _ _ HT);
  [unfold W14T_RF_TBL; lia | unfold W14T_RF_TBL, W14T_RF_CS; simpl; lia | exact UR]|].
split; [apply (w14t_u64_kept _ _ _ _ _ _ HT);
  [unfold W14T_CC_TBL; lia | unfold W14T_CC_TBL, W14T_CC_CS; simpl; lia | exact UC]|].
split.
{ intros i Hi. specialize (SC i Hi). unfold W14T_CC_CS.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as C by lia.
  destruct C as [->|[->|[->| ->]]];
  (apply (m2b_cstr_kept _ _ _ _ _ _ HK); [vm_compute; congruence | vm_compute; reflexivity | exact SC]). }
split; [apply (m2b_cstr_kept _ _ _ _ _ _ HK); [vm_compute; congruence | vm_compute; reflexivity | exact SN]|].
specialize (SR 4 ltac:(lia)). change (rt_refuse [0x21600; 0x21620; 0x21640; 0x21660; 0x21680] 0x21600 4) with 0x21680 in SR.
apply (m2b_cstr_kept _ _ _ _ _ _ HK); [vm_compute; congruence | vm_compute; reflexivity | exact SR].
Qed.
End d2.
End b.

(* ======================================= the walk ======================================= *)
(* the enter step of a run that starts at a cut with no memory access before its next call: the registers as
   atoms, no region, no fact *)
Ltac w14t_enter :=
lazymatch goal with |- SRr rsegs ?W (cfg_at rsegs ?pc ?regs ?mem ?md) _ =>
let HS := fresh "HS" in
pose proof (m2b_entry pc [] [] (mkFacts [] [] []) W regs [] mem (Forall_nil _) eq_refl (Forall_nil _) I
  ltac:(repeat split)) as HS;
let E := fresh "E" in let HE := fresh "HE" in
remember (Ereg regs []) as E eqn:HE;
let HAE := fresh "HAE" in assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; apply env_agree_refl);
let KE := fresh "KE" in
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ False -> aview rsegs (w_H W) mem a = aview rsegs (w_H W) mem a)
by (intros; reflexivity);
unfold cfg_at; change (w64 pc) with (Z_to_bv 64 pc)
end.

(* the common steps of a stage: the entry, the run to the callee, the kept registers, the goal in the mkCfg form
   at the callee's entry pc *)
Ltac w14t_stage regs2 pcC :=
let HJ := fresh "HJ" in
lazymatch goal with Hcore : rsb_core _ _ _ _ _ _ _ _ regs2 _ _ |- _ => pose proof (proj1 Hcore) as HJ end;
w14t_enter;
w14t_run m2b_awr; ck_keep kwr_stk;
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
let CL4 := fresh "CL4" in let C234 := fresh "C234" in
pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ w14t_L4 HS HAE ltac:(vm_compute; reflexivity)) as CL4;
pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
replace (ss_pc ss) with pcC by (vm_compute; reflexivity)
end.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis REFUSE : rt_refuse_code_specX rsegs B MT W14T_REFUSE W14T_RF_TBL W14T_RF_COV W14T_RF_CS.
Hypothesis CODE : rt_check_code_specX rsegs B MT W14T_CODE W14T_CC_TBL W14T_CC_LNONE W14T_CC_CS.

(* rsb_core and sp at the callee's entry *)
Ltac w14t_coreT regs2 :=
lazymatch goal with
| Hcore : rsb_core _ _ _ ?cx ?E2 ?ly2 ?S2 ?W2 regs2 ?mem2 ?md2, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _,
  C234 : cs_eq _ regs2 (ms_regs ?ms), KE : forall a, _ -> ~ _ -> aview _ _ (ms_mem ?ms) a = _,
  Hsp : spZ regs2 = _ |- _ =>
  let HcoreT := fresh "HcoreT" in let HspT := fresh "HspT" in
  assert (HspT : spZ (ms_regs ms) = q_R (x_e rsegs cx)) by (rewrite (w14t_sp234 _ _ C234); exact Hsp);
  assert (HcoreT : rsb_core rsegs B MT cx E2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT)
  by (apply (m2b_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ
        (w14t_r234 _ _ C234) eq_refl (Permutation_refl _)); [m2b_io | apply (mo_le_refl MT MTL) |];
      intros a Ha _ _; exact (KE a Ha (fun x => x)))
end.
Ltac w14t_pre T :=
lazymatch goal with HcoreT : rsb_core _ _ _ ?cx _ _ _ _ _ _ _, Hpre : rsb_pre _ _ ?cx, R1' : getr _ 1 = w64 _,
  HspT : spZ _ = _ |- _ =>
apply (m2b_pre_call B MT cx _ _ _ _ _ _ _ T Hpre HcoreT);
[ rewrite R1'; vm_compute; reflexivity
| unfold raZ; rewrite R1'; unfold w64; rewrite unsigned_lit_small by lia; lia
| exact HspT | unfold T_cmp_STK, T_check_STK, T_SEG_STK, ASTACK, ESTACK; lia ]
end.
Ltac w14t_kept Hkept3 KE Hkept :=
let a := fresh "a" in let Ha := fresh "Ha" in let Hs := fresh "Hs" in
intros a Ha Hs; rewrite (Hkept3 a Ha ltac:(unfold T_cmp_STK, T_check_STK, T_SEG_STK, ASTACK, ESTACK in *; lia)
  (fun x => x));
rewrite (KE a Ha (fun x => x)); exact (Hkept a Ha Hs).

(* what reaching C4 from the tail means: rsb_core, the three registers of w14t_L4 as in regs0, every byte outside
   the callees' stack as in (W0, mem0) *)
Definition w14t_K (cx : rsb_scx rsegs) (POST : world rsegs -> config -> Prop) (regs0 : bvmap 5 word)
(W0 : world rsegs) (mem0 : word -> option byte) : Prop :=
forall ly3 S3 W3 regs3 mem3 md3,
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> cs_eq w14t_L4 regs0 regs3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W0) mem0 a) ->
SRr rsegs W3 (cfg_at rsegs W14T_C4 regs3 mem3 md3) POST.

(* 0x82f94: a0 = codes[4] = 0x21680; addi a1,zero,4; jal check_code -> C4 *)
Lemma w14t_s2 : forall (cx : rsb_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2,
rsb_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = q_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 10) = w64 0x21680 ->
cs_eq w14t_L4 regs0 regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W0) mem0 a) ->
w14t_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs W14T_T2R regs2 mem2 md2) POST.
Proof using MTL CODE.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore Hsp H10 HL4 Hkept HK.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
w14t_stage regs2 W14T_CODE.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82f9c) by exact R1.
assert (R11' : getr (ms_regs ms) 11 = w64 4) by exact R11.
assert (E10 : ew E 10 = getr regs2 (Z_to_bv 5 10)) by (subst E; apply ew_Ereg_nat; reflexivity).
w14t_coreT regs2.
destruct (w14t_strs B MT cx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ Hpre Hpod HcoreT) as (_ & UC & SC & SN & SR).
eapply SRr_bind.
{ apply (CODE (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
    (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _
    (x_k rsegs cx) (ms_regs ms) 0x21680).
  - w14t_pre T_cmp_STK.
  - etransitivity; [exact R10|]. rewrite E10. exact H10.
  - rewrite R11'. vm_compute. congruence.
  - rewrite R11'. change (rt_cstr rsegs (w_H W2) (ms_mem ms) 0x21680 (rt_refuse_txt 4)). exact SR.
  - reflexivity.
  - exact UC.
  - exact SC.
  - exact SN. }
intros W3 c3 _ Hpost.
destruct (m2b_core_call B MT MTL cx (rsb_E2 rsegs cx) (fun _ => False) T_cmp_STK ly2 S2 W2 (ms_regs ms) (ms_mem ms) _
  _ _ _ W3 c3 Hpre HcoreT HspT ltac:(unfold T_cmp_STK, T_SEG_STK, ASTACK, ESTACK; lia) ltac:(intros a Hf; destruct Hf)
  Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & _ & Hcore3 & Hpres3 & Hkept3 & _).
subst fx3 c3. rewrite R1'.
apply (HK ly3 S3 W3 regs3 mem3 md3 Hcore3).
- exact (cs_eq_trans _ _ _ _ (cs_eq_trans _ _ _ _ HL4 CL4) (cs_eq_of_pres w14t_L4 _ _ w14t_L4_cs Hpres3)).
- w14t_kept Hkept3 KE Hkept.
Qed.

(* T2 0x82f8c: addi a0,zero,4; jal reac_rate_refuse_code (a0 = 4) -> 0x82f94 *)
Lemma w14t_s1 : forall (cx : rsb_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2,
rsb_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = q_R (x_e rsegs cx) ->
cs_eq w14t_L4 regs0 regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W0) mem0 a) ->
w14t_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs W14T_T2 regs2 mem2 md2) POST.
Proof using MTL REFUSE CODE.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore Hsp HL4 Hkept HK.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof ck_wx as Hwx. pose proof ck_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
w14t_stage regs2 W14T_REFUSE.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82f94) by exact R1.
assert (R10' : getr (ms_regs ms) 10 = w64 4) by exact R10.
w14t_coreT regs2.
destruct (w14t_strs B MT cx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ Hpre Hpod HcoreT) as (UR & _).
eapply SRr_bind.
{ apply (REFUSE (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
    (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _
    (x_k rsegs cx) (ms_regs ms)).
  - w14t_pre T_check_STK.
  - reflexivity.
  - unfold W14T_RF_COV. lia.
  - exact UR. }
intros W3 c3 _ Hpost.
destruct (m2b_core_call B MT MTL cx (rsb_E2 rsegs cx) (fun _ => False) T_check_STK ly2 S2 W2 (ms_regs ms) (ms_mem ms) _
  _ _ _ W3 c3 Hpre HcoreT HspT ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia) ltac:(intros a Hf; destruct Hf)
  Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & _ & Hcore3 & Hpres3 & Hkept3 & HR3).
subst fx3 c3. rewrite R1'.
apply (w14t_s2 cx POST regs0 W0 mem0 ly3 S3 W3 regs3 mem3 md3 Hpre Hpod Hcore3
  ltac:(rewrite (m2b_sp_pres _ _ Hpres3); exact HspT)).
- etransitivity; [exact HR3|]. rewrite R10'. reflexivity.
- exact (cs_eq_trans _ _ _ _ (cs_eq_trans _ _ _ _ HL4 CL4) (cs_eq_of_pres w14t_L4 _ _ w14t_L4_cs Hpres3)).
- w14t_kept Hkept3 KE Hkept.
- exact HK.
Qed.
End w.

(* ======================================= the piece statement ======================================= *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
(* the two callees' contracts at every float state: the T2 cut holds at any float state fx2 the walk reached, and
   the tail calls both callees there *)
Hypothesis REFUSE : forall fy : YK11.FPState,
  rt_refuse_code_specX (fx := fy) rsegs B MT 0x841b4 0x9bf80 0x21600 [0x21600; 0x21620; 0x21640; 0x21660; 0x21680].
Hypothesis CODE : forall fy : YK11.FPState,
  rt_check_code_specX (fx := fy) rsegs B MT 0x8360c 0x9bf40 0x215c0 [0x21540; 0x21560; 0x21580; 0x215a0].

(* the C4 cut from the T2 cut's facts, carried to a state whose memory agrees outside the callees' stack and whose
   three registers of w14t_L4 agree *)
Lemma w14t_cut_C4 : forall (cx : rsb_scx rsegs) fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rsb_pre rsegs B cx -> rsb_chk_base (fx := fx) rsegs B MT cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ->
rsb_at_cx rsegs cx W2 mem2 regs2 (rsb_L_dec rsegs cx) ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> cs_eq w14t_L4 regs2 regs3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rsb_cut_C4 (fx := fx) rsegs B MT cx fx2 ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre
(Hcore & Hfxk & Hfsh & _) Hat Hcore3 HL K3.
pose proof (m2b_stack B cx Hpre) as (_ & _ & _ & _ & Hceil & H46 & _).
pose proof (m2b_frameF B cx Hpre) as (F32 & F4096 & Fceil & Fapp & _).
pose proof (RtPgStepsB.rtsb_fbounds _ F32 Fapp) as (_ & _ & S0 & S128 & _).
pose proof asan_consts as (C1 & _).
assert (Far : forall a, q_R (x_e rsegs cx) <= a < q_R (x_e rsegs cx) + 0x220 ->
  0 <= a < 2 ^ 64 /\ ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx))).
{ intros a Ha. unfold T_SEG_STK, ASTACK in *. lia. }
unfold rsb_at_cx, rsb_at, rsb_L_dec in Hat. rewrite !Forall_cons_iff in Hat.
destruct Hat as (A8 & A9 & A19 & C10 & C18 & C60 & C168 & C148 & C178 & _).
cbn [rt_at rt_xv fst snd] in A8, A9, A19, C10, C18, C60, C168, C148, C178.
split; [exact Hcore3|]. split; [exact Hfxk|]. split.
- unfold rt_cut. cbn [hi_L4 rate_himg_B]. repeat apply Forall_cons; try apply Forall_nil; cbn [rt_at rt_xv fst snd].
  + w14t_cs_get HL (8%bv : bv 5). exact A8.
  + w14t_cs_get HL (9%bv : bv 5). exact A9.
  + w14t_cs_get HL (19%bv : bv 5). exact A19.
  + eapply (val_mem_kept rsegs); [|exact C10]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    destruct (Far (q_R (x_e rsegs cx) + 0x10 + k) ltac:(lia)) as (Ha & Hs). exact (K3 _ Ha Hs).
  + eapply (val_mem_kept rsegs); [|exact C18]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    destruct (Far (q_R (x_e rsegs cx) + 0x18 + k) ltac:(lia)) as (Ha & Hs). exact (K3 _ Ha Hs).
  + eapply (val_mem_kept rsegs); [|exact C60]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    destruct (Far (q_R (x_e rsegs cx) + 0x60 + k) ltac:(lia)) as (Ha & Hs). exact (K3 _ Ha Hs).
  + eapply (val_mem_kept rsegs); [|exact C148]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    destruct (Far (q_R (x_e rsegs cx) + 0x148 + k) ltac:(lia)) as (Ha & Hs). exact (K3 _ Ha Hs).
  + rewrite Z.add_0_r. eapply (val_mem_kept rsegs); [|exact C168]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    destruct (Far (q_R (x_e rsegs cx) + 0x168 + k) ltac:(lia)) as (Ha & Hs). exact (K3 _ Ha Hs).
  + eapply (val_mem_kept rsegs); [|exact C178]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    destruct (Far (q_R (x_e rsegs cx) + 0x178 + k) ltac:(lia)) as (Ha & Hs). exact (K3 _ Ha Hs).
- unfold rsb_fsh_at in *. apply (rtmb_fsh_kept rsegs (w_H W2) mem2 (w_H W3) mem3 _ _ Hfsh). intros i Hi.
  change (Z.of_nat (length rsb_PB)) with 88 in Hi.
  apply K3; unfold T_SEG_STK, ASTACK in *; lia.
Qed.

(* ---- W14 TAIL: T2 0x82f8c -> C4 0x82f9c ---- *)
Theorem rt_w14_tail_B : rsb_piece_W14_tail_stmt rsegs B MT.
Proof using MTL REFUSE CODE.
unfold rsb_piece_W14_tail_stmt. intros cx POST inp Hst HC4.
unfold rsb_from_T2. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HT.
destruct Hst as (Hpre & _).
destruct HT as (Hbase & Hat).
pose proof Hbase as (Hcore & Hfxk & Hfsh & Hrom & Hpp & Hwf & Hlen & Hpod0 & Hpod & Hpod1).
pose proof (m2b_stack B cx Hpre) as (HR & _).
assert (Hsp : spZ regs2 = q_R (x_e rsegs cx)).
{ rewrite <- HR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
apply (w14t_s1 (fx := fx2) B MT MTL (REFUSE fx2) (CODE fx2) cx POST regs2 W2 mem2 ly2 S2 W2 regs2 mem2 md2
  Hpre Hpod Hcore Hsp).
- intros r Hr. reflexivity.
- intros a _ _. reflexivity.
- intros ly3 S3 W3 regs3 mem3 md3 Hcore3 HL K3.
  apply (HC4 fx2 ly3 S3 W3 regs3 mem3 md3).
  exact (w14t_cut_C4 cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase Hat Hcore3 HL K3).
Qed.
End m.

Print Assumptions rt_w14_tail_B.
About rt_w14_tail_B.
