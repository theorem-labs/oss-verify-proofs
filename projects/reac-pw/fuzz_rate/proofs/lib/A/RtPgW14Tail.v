(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/RPgCheckStr.v at 77f59d02b01 (the call in the middle of a walk: the run
   to the jal, the callee's contract through SRr_bind, a fresh entry state at the return pc; L_ANS_cs as tl_L4_cs and
   ch_L_cs) for the MATCH HALF of reac-pw/fuzz_role's image-A segment M02: the tail and the two checks, proved
   against lib/A/RPgSeg.v's rs_piece_W11b_tail_stmt and rs_piece_W11b_checks_stmt on lib/A/Img0.v rsegs. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_role/lib/A/RPgM02Tail.v, with its module paths, module names, addresses and numbers changed; 140 of its 253 lines of code are new or changed and 844 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, which holds the same loaded bytes). Proves no
   function (kind: segment lemma): the piece W14-tail of LLVMFuzzerTestOneInput's segment M02, whose statement is
   lib/A/RtPgSeg.v's rs_piece_W14_tail_stmt; nothing here restates a cut.

   THE TAIL (rs_cut_T2 at T2 0x82e74 -> rs_cut_C4 at C4 0x82e84), fuzz_rate.c:270 check_code(reac_rate_refuse_code(4), 4):
     0x82e74 addi a0,zero,4; 0x82e78 jal 0x83f60 reac_rate_refuse_code (ra 0x82e7c);
     0x82e7c addi a1,zero,4; 0x82e80 jal 0x83734 check_code (ra 0x82e84 = C4).
   - w14_s1: a run 0x82e74 .. the callee's entry from an entry state with no region (the code between the cut and
     the call only sets a0), reac_rate_refuse_code's contract (the Section hypothesis REFUSE) through SRr_bind with
     RtPgM02Base.m2_pre_call for its rt_cpre and m2_core_call for rs_core at the return: a0 = codes[4] = 0x21680
     (rt_refuse at r = 4).
   - w14_s2: the run 0x82e7c .. check_code's entry, check_code's contract (CODE) with s = 0x21680 and r = 4: the
     text at 0x21680 is rt_refuse_txt 4, the table switch.table.check_code and its four strings and the literal
     "none" are lib/A/RtPgW14Base.v's w14_strs at the call's memory; m2_core_call at the return C4.
   - What C4 reads (hi_L4 = RtPgSeg's rs_L_dec: s0 = S, s1 = R, s4 = the frame's shadow base, and six real-frame
     cells) is carried from the T2 cut: the three registers are callee-saved and not written by the tail, and no
     byte outside the callees' stack [R - T_SEG_STK, R) is written; the frame's shadow (rs_PB) lies below the
     allocator's ceiling, so it is kept too (w14_cut_C4).
   Both callees return at the float state they are called at, so every state of the tail is at the cut's own float
   state fx2; the walk lemmas are stated at the configurations' float state (Section w) and used at fx2.

   SECTION HYPOTHESES of rt_w14_tail_A (Section m): MTL : ameter_laws MT; REFUSE : reac_rate_refuse_code's contract
   rt_refuse_code_specX at 0x83f60 (table 0x9bc80, cov 0x21600, codes 0x21600 .. 0x21680) at every float state;
   CODE : check_code's contract rt_check_code_specX at 0x83734 (table 0x9bc40, lnone 0x215c0, strings 0x21540 ..
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSeg RtPgMem RtPgSteps.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgCheck RtPgM02Base RtPgW14Base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================= registers ======================================= *)
(* the registers the C4 cut reads (hi_L4): s0, s1, s4, all callee-saved and not written by the tail *)
Definition w14_L4 : list (bv 5) := [8; 9; 20]%bv.
Lemma w14_L4_cs : forall r, In r w14_L4 -> acallee_saved (bv_unsigned r).
Proof.
intros r Hr. cbv [w14_L4 In] in Hr. unfold acallee_saved.
repeat (destruct Hr as [<- | Hr];
[lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia | ]).
destruct Hr.
Qed.
Ltac w14_cs_get Hcs r :=
etransitivity; [exact (Hcs r ltac:(cbv [w14_L4 In]; repeat (first [left; apply bv_eq; reflexivity | right])))|].

(* the enter step of a run that starts at a cut with no memory access before its next call: the registers as
   atoms, no region, no fact *)
Ltac w14_enter :=
lazymatch goal with |- SRr rsegs ?W (cfg_at rsegs ?pc ?regs ?mem ?md) _ =>
let HS := fresh "HS" in
pose proof (m2_entry pc [] [] (mkFacts [] [] []) W regs [] mem (Forall_nil _) eq_refl (Forall_nil _) I
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
Ltac w14_stage regs2 pcC :=
let HJ := fresh "HJ" in
lazymatch goal with Hcore : rs_core _ _ _ _ _ _ _ _ regs2 _ _ |- _ => pose proof (proj1 Hcore) as HJ end;
w14_enter;
w14_run m2_awr; ck_keep kwr_stk;
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms), HAE : env_agree 32 _ ?E |- _ =>
let CL4 := fresh "CL4" in let C234 := fresh "C234" in
pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ w14_L4 HS HAE ltac:(vm_compute; reflexivity)) as CL4;
pose proof (cs_eq_of_st_ok _ _ ss ms regs2 _ [2; 3; 4]%bv HS HAE ltac:(vm_compute; reflexivity)) as C234;
rewrite (st_ok_restrict_mkst rsegs H E ss ms HS eq_refl);
replace (ss_pc ss) with pcC by (vm_compute; reflexivity)
end.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis REFUSE : rt_refuse_code_specX rsegs B MT W14_REFUSE W14_RF_TBL W14_RF_COV W14_RF_CS.
Hypothesis CODE : rt_check_code_specX rsegs B MT W14_CODE W14_CC_TBL W14_CC_LNONE W14_CC_CS.

(* rs_core and sp at the callee's entry *)
Ltac w14_coreT regs2 :=
lazymatch goal with
| Hcore : rs_core _ _ _ ?cx ?E2 ?ly2 ?S2 ?W2 regs2 ?mem2 ?md2, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?ms) ?mdT _,
  C234 : cs_eq _ regs2 (ms_regs ?ms), KE : forall a, _ -> ~ _ -> aview _ _ (ms_mem ?ms) a = _,
  Hsp : spZ regs2 = _ |- _ =>
  let HcoreT := fresh "HcoreT" in let HspT := fresh "HspT" in
  assert (HspT : spZ (ms_regs ms) = q_R (x_e rsegs cx)) by (rewrite (w14_sp234 _ _ C234); exact Hsp);
  assert (HcoreT : rs_core rsegs B MT cx E2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT)
  by (apply (m2_core_step B MT MTL cx _ ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) mdT Hcore HJ
        (w14_r234 _ _ C234) eq_refl (Permutation_refl _)); [m2_io | apply (mo_le_refl MT MTL) |];
      intros a Ha _ _; exact (KE a Ha (fun x => x)))
end.
Ltac w14_pre T :=
lazymatch goal with HcoreT : rs_core _ _ _ ?cx _ _ _ _ _ _ _, Hpre : rs_pre _ _ ?cx, R1' : getr _ 1 = w64 _,
  HspT : spZ _ = _ |- _ =>
apply (m2_pre_call B MT cx _ _ _ _ _ _ _ T Hpre HcoreT);
[ rewrite R1'; vm_compute; reflexivity
| unfold raZ; rewrite R1'; unfold w64; rewrite unsigned_lit_small by lia; lia
| exact HspT | unfold T_cmp_STK, T_check_STK, T_SEG_STK, ASTACK, ESTACK; lia ]
end.
Ltac w14_kept Hkept3 KE Hkept :=
let a := fresh "a" in let Ha := fresh "Ha" in let Hs := fresh "Hs" in
intros a Ha Hs; rewrite (Hkept3 a Ha ltac:(unfold T_cmp_STK, T_check_STK, T_SEG_STK, ASTACK, ESTACK in *; lia)
  (fun x => x));
rewrite (KE a Ha (fun x => x)); exact (Hkept a Ha Hs).

(* what reaching C4 from the tail means: rs_core, the three registers of w14_L4 as in regs0, every byte outside
   the callees' stack as in (W0, mem0) *)
Definition w14_K (cx : rs_scx rsegs) (POST : world rsegs -> config -> Prop) (regs0 : bvmap 5 word) (W0 : world rsegs)
(mem0 : word -> option byte) : Prop :=
forall ly3 S3 W3 regs3 mem3 md3,
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> cs_eq w14_L4 regs0 regs3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W0) mem0 a) ->
SRr rsegs W3 (cfg_at rsegs W14_C4 regs3 mem3 md3) POST.

(* 0x82e7c: a0 = codes[4] = 0x21680; addi a1,zero,4; jal check_code -> C4 *)
Lemma w14_s2 : forall (cx : rs_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = q_R (x_e rsegs cx) ->
getr regs2 (Z_to_bv 5 10) = w64 0x21680 ->
cs_eq w14_L4 regs0 regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W0) mem0 a) ->
w14_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs W14_T2R regs2 mem2 md2) POST.
Proof using MTL CODE.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore Hsp H10 HL4 Hkept HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof w14_wx as Hwx. pose proof w14_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
w14_stage regs2 W14_CODE.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R11" in rreg HS (11%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82e84) by exact R1.
assert (R11' : getr (ms_regs ms) 11 = w64 4) by exact R11.
assert (E10 : ew E 10 = getr regs2 (Z_to_bv 5 10)) by (subst E; apply ew_Ereg_nat; reflexivity).
w14_coreT regs2.
destruct (w14_strs B MT cx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ Hpre Hpod HcoreT) as (_ & UC & SC & SN & SR).
eapply SRr_bind.
{ apply (CODE (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
    (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _
    (x_k rsegs cx) (ms_regs ms) 0x21680).
  - w14_pre T_cmp_STK.
  - etransitivity; [exact R10|]. rewrite E10. exact H10.
  - rewrite R11'. vm_compute. congruence.
  - rewrite R11'. change (rt_cstr rsegs (w_H W2) (ms_mem ms) 0x21680 (rt_refuse_txt 4)). exact SR.
  - reflexivity.
  - exact UC.
  - exact SC.
  - exact SN. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (rs_E2 rsegs cx) (fun _ => False) T_cmp_STK ly2 S2 W2 (ms_regs ms) (ms_mem ms) _
  _ _ _ W3 c3 Hpre HcoreT HspT ltac:(unfold T_cmp_STK, T_SEG_STK, ASTACK, ESTACK; lia) ltac:(intros a Hf; destruct Hf)
  Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & _ & Hcore3 & Hpres3 & Hkept3 & _).
subst fx3 c3. rewrite R1'.
apply (HK ly3 S3 W3 regs3 mem3 md3 Hcore3).
- exact (cs_eq_trans _ _ _ _ (cs_eq_trans _ _ _ _ HL4 CL4) (cs_eq_of_pres w14_L4 _ _ w14_L4_cs Hpres3)).
- w14_kept Hkept3 KE Hkept.
Qed.

(* T2 0x82e74: addi a0,zero,4; jal reac_rate_refuse_code (a0 = 4) -> 0x82e7c *)
Lemma w14_s1 : forall (cx : rs_scx rsegs) POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 -> spZ regs2 = q_R (x_e rsegs cx) ->
cs_eq w14_L4 regs0 regs2 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) ->
 aview rsegs (w_H W2) mem2 a = aview rsegs (w_H W0) mem0 a) ->
w14_K cx POST regs0 W0 mem0 ->
SRr rsegs W2 (cfg_at rsegs W14_T2 regs2 mem2 md2) POST.
Proof using MTL REFUSE CODE.
intros cx POST regs0 W0 mem0 ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore Hsp HL4 Hkept HK.
pose proof (m2_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & Hceil & H46 & H47 & Hsp0al & Hev & Hgp & Htp).
pose proof w14_wx as Hwx. pose proof w14_segs_low as Hsegs. pose proof (AR_laws_ok rsegs B) as LAWS.
w14_stage regs2 W14_REFUSE.
let R := fresh "R10" in rreg HS (10%bv : bv 5) R.
let R := fresh "R1" in rreg HS (1%bv : bv 5) R.
assert (R1' : getr (ms_regs ms) 1 = w64 0x82e7c) by exact R1.
assert (R10' : getr (ms_regs ms) 10 = w64 4) by exact R10.
w14_coreT regs2.
destruct (w14_strs B MT cx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ Hpre Hpod HcoreT) as (UR & _).
eapply SRr_bind.
{ apply (REFUSE (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx)
    (x_S rsegs cx) (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 (ms_mem ms) _
    (x_k rsegs cx) (ms_regs ms)).
  - w14_pre T_check_STK.
  - reflexivity.
  - unfold W14_RF_COV. lia.
  - exact UR. }
intros W3 c3 _ Hpost.
destruct (m2_core_call B MT MTL cx (rs_E2 rsegs cx) (fun _ => False) T_check_STK ly2 S2 W2 (ms_regs ms) (ms_mem ms) _
  _ _ _ W3 c3 Hpre HcoreT HspT ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia) ltac:(intros a Hf; destruct Hf)
  Hpost)
as (fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & Hfx3 & _ & Hcore3 & Hpres3 & Hkept3 & HR3).
subst fx3 c3. rewrite R1'.
apply (w14_s2 cx POST regs0 W0 mem0 ly3 S3 W3 regs3 mem3 md3 Hpre Hpod Hcore3
  ltac:(rewrite (m2_sp_pres _ _ Hpres3); exact HspT)).
- etransitivity; [exact HR3|]. rewrite R10'. reflexivity.
- exact (cs_eq_trans _ _ _ _ (cs_eq_trans _ _ _ _ HL4 CL4) (cs_eq_of_pres w14_L4 _ _ w14_L4_cs Hpres3)).
- w14_kept Hkept3 KE Hkept.
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
  rt_refuse_code_specX (fx := fy) rsegs B MT 0x83f60 0x9bc80 0x21600 [0x21600; 0x21620; 0x21640; 0x21660; 0x21680].
Hypothesis CODE : forall fy : YK11.FPState,
  rt_check_code_specX (fx := fy) rsegs B MT 0x83734 0x9bc40 0x215c0 [0x21540; 0x21560; 0x21580; 0x215a0].

(* the C4 cut from the T2 cut's facts, carried to a state whose memory agrees outside the callees' stack and whose
   three registers of w14_L4 agree *)
Lemma w14_cut_C4 : forall (cx : rs_scx rsegs) fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rs_pre rsegs B cx -> rs_chk_base (fx := fx) rsegs B MT cx fx2 rec rs_PB ly2 S2 W2 regs2 mem2 md2 ->
rs_at_cx rsegs cx W2 mem2 regs2 (rs_L_dec rsegs cx) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly3 S3 W3 regs3 mem3 md3 -> cs_eq w14_L4 regs2 regs3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rs_cut_C4 (fx := fx) rsegs B MT cx fx2 ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre
(Hcore & Hfxk & Hfsh & _) Hat Hcore3 HL K3.
pose proof (m2_stack B cx Hpre) as (_ & _ & _ & _ & Hceil & H46 & _).
pose proof (m2_frameF B cx Hpre) as (F32 & F4096 & Fceil & Fapp & _).
pose proof (rts_fbounds _ F32 Fapp) as (_ & _ & S0 & S64 & _).
pose proof asan_consts as (C1 & _).
assert (Far : forall a, q_R (x_e rsegs cx) <= a < q_R (x_e rsegs cx) + 0x1e0 ->
  0 <= a < 2 ^ 64 /\ ~ (q_R (x_e rsegs cx) - T_SEG_STK <= a < q_R (x_e rsegs cx))).
{ intros a Ha. unfold T_SEG_STK, ASTACK in *. lia. }
unfold rs_at_cx, rs_at, rs_L_dec in Hat. rewrite !Forall_cons_iff in Hat.
destruct Hat as (A8 & A9 & A20 & C18 & C50 & C78 & Cc0 & C120 & C138 & _).
cbn [rt_at rt_xv fst snd] in A8, A9, A20, C18, C50, C78, Cc0, C120, C138.
split; [exact Hcore3|]. split; [exact Hfxk|]. split.
- unfold rt_cut. cbn [hi_L4 rate_himg_A]. repeat apply Forall_cons; try apply Forall_nil; cbn [rt_at rt_xv fst snd].
  + w14_cs_get HL (8%bv : bv 5). exact A8.
  + w14_cs_get HL (9%bv : bv 5). exact A9.
  + w14_cs_get HL (20%bv : bv 5). exact A20.
  + eapply (val_mem_kept rsegs); [|exact C18]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    destruct (Far (q_R (x_e rsegs cx) + 0x18 + k) ltac:(lia)) as (Ha & Hs). exact (K3 _ Ha Hs).
  + eapply (val_mem_kept rsegs); [|exact C50]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    destruct (Far (q_R (x_e rsegs cx) + 0x50 + k) ltac:(lia)) as (Ha & Hs). exact (K3 _ Ha Hs).
  + eapply (val_mem_kept rsegs); [|exact C78]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    destruct (Far (q_R (x_e rsegs cx) + 0x78 + k) ltac:(lia)) as (Ha & Hs). exact (K3 _ Ha Hs).
  + rewrite Z.add_0_r. eapply (val_mem_kept rsegs); [|exact Cc0]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    destruct (Far (q_R (x_e rsegs cx) + 0xc0 + k) ltac:(lia)) as (Ha & Hs). exact (K3 _ Ha Hs).
  + eapply (val_mem_kept rsegs); [|exact C120]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    destruct (Far (q_R (x_e rsegs cx) + 0x120 + k) ltac:(lia)) as (Ha & Hs). exact (K3 _ Ha Hs).
  + eapply (val_mem_kept rsegs); [|exact C138]. intros k Hk. change (Z.of_nat 8) with 8 in Hk.
    destruct (Far (q_R (x_e rsegs cx) + 0x138 + k) ltac:(lia)) as (Ha & Hs). exact (K3 _ Ha Hs).
- unfold rs_fsh_at in *. apply (rtm_fsh_kept rsegs (w_H W2) mem2 (w_H W3) mem3 _ _ Hfsh). intros i Hi.
  change (Z.of_nat (length rs_PB)) with 56 in Hi.
  apply K3; unfold T_SEG_STK, ASTACK in *; lia.
Qed.

(* ---- W14 TAIL: T2 0x82e74 -> C4 0x82e84 ---- *)
Theorem rt_w14_tail_A : rs_piece_W14_tail_stmt rsegs B MT.
Proof using MTL REFUSE CODE.
unfold rs_piece_W14_tail_stmt. intros cx POST inp Hst HC4.
unfold rs_from_T2. intros fx2 ly2 S2 W2 regs2 mem2 md2 rec HT.
destruct Hst as (Hpre & _).
destruct HT as (Hbase & Hat).
pose proof Hbase as (Hcore & Hfxk & Hfsh & Hrom & Hpp & Hwf & Hlen & Hpod0 & Hpod & Hpod1).
pose proof (m2_stack B cx Hpre) as (HR & _).
assert (Hsp : spZ regs2 = q_R (x_e rsegs cx)).
{ rewrite <- HR. unfold spZ. f_equal. destruct Hcore as (_ & Hr & _). exact (Hr 2 ltac:(lia)). }
apply (w14_s1 (fx := fx2) B MT MTL (REFUSE fx2) (CODE fx2) cx POST regs2 W2 mem2 ly2 S2 W2 regs2 mem2 md2
  Hpre Hpod Hcore Hsp).
- intros r Hr. reflexivity.
- intros a _ _. reflexivity.
- intros ly3 S3 W3 regs3 mem3 md3 Hcore3 HL K3.
  apply (HC4 fx2 ly3 S3 W3 regs3 mem3 md3).
  exact (w14_cut_C4 cx fx2 rec ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hpre Hbase Hat Hcore3 HL K3).
Qed.
End m.

Print Assumptions rt_w14_tail_A.
About rt_w14_tail_A.
