(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the last segment of plugin-hostd/fuzz_command's sup_broadcast walk, in the form
   of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (the step through a call): from the return of arg_line (0x8b048)
   the frame is restored and `j answer` (0x8b06c) runs answer at the entry stack pointer; answer's statement
   (a Section hypothesis) gives the post-condition.

   Pass-4/5 re-fit: TANSWER is taken at every FP state and used at the entry's fx (no
   earlier call changes the FP state); answer's rounding-mode-0 premise is the entry's (HFRM); answer is the last
   step, through PaFx.v's cl_callS_wideF, and PaFx.v's apost_baseF_intro closes sup_broadcast's apost_baseF.
   Statement pass 5 removed astack_pres, so no stack fact is built for answer's entry; the frame chain answer's
   afn_pre asks is sup_broadcast's own afn_pre chain (s0 at the tail jump is the entry s0), kept by achain_kept. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_broadcast_s3.v, with its module paths and module names changed; 277 of its 325 lines of code are new or changed and 382 lines of the source are left out. *)
(* sup_remove's walk on the ASan build of plugin-hostd/fuzz_command, the join piece (sup_remove_s1.v's sr_jl_stmt):
   from the join 0x8abbc (BASE + AF_sup_remove + 0x6c) to the tail jump into answer. One symbolic run passes the two
   inline checks of c and c + 4 and stores c->fn := REC_REMOVE and c->nargs := 0; arg_i(c, id) is composed through
   PaFx.v's cl_callS_wideF (PaNoChain's cl_callS_wide for a callee whose post is apost_baseF) with arg_i's statement
   (its footprint, c->nargs and c->args[0], is a part of the program's statics in sup_remove's footprint); the run
   after the call restores the frame and stops at `j answer` with a0 = c, a1 = the literal 0x21ce0, a2 = 1, where
   the arm's continuation TAILK applies.
   The form follows sup_broadcast's tail (sup_broadcast_s3.v) and hand_back's call
   (hand_back.v).

   Statement passes 4 and 5 (FP lifts, and frame chains at a call): TARG_I holds at every FP state
   and is used at the entry's fx with the piece's rounding-mode-0 premise. arg_i reaches the snprintf wrapper and
   returns at some fx1 with fxrel fx fx1; the symbolic state after the call is carried to fx1 by the core's
   st_ok_xfx (lib/Reusable/YL05.v: st_ok reads the FP state only in its f-register and fcsr clauses), the run
   after the call is the executor at fx1, and TAILK is applied at fx1 (in place). The frame
   chain at arg_i's entry is achain's empty case (s0 = id); astack_pres is gone. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaSB PaCallRun PaCall PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YL05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c arg_i_c answer_c sup_remove_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaNoChain PaArt sup_remove_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma sj_u64 : forall z, bv_unsigned (Z_to_bv 64 z) = z mod 2 ^ 64.
Proof. intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). reflexivity. Qed.
Lemma sj_aval_keep : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, 0 <= k < Z.of_nat n -> rd' (a + k) = rd (a + k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.
(* the program's statics lie below 2^32 *)
Lemma sj_PG_low : forall a, inFP cmd_PG a -> 0 <= a < 2 ^ 32.
Proof.
intros a (r & Hr & Ha). unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in *. cbn [In] in Hr.
destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia.
Qed.
(* the call's slot lies in sup_remove's footprint *)
Lemma sj_slot_FP : forall O c a, sr_slot c -> c <= a < c + CALL_SIZE -> inFP (sr_FP O) a.
Proof.
intros O c a Hc Ha. destruct (sr_slot_range c Hc) as (_ & _ & [H | ->]); unfold sr_FP.
- apply inFP_cons. right. apply inFP_cons. left. unfold CALL_SIZE, OFF_ANSWER, OFF_CALLS, A_G_REC in *. lia.
- apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. left.
  unfold CALL_SIZE, SC_SIZE, A_REC_SPILL in *. lia.
Qed.
Lemma sj_aregs : forall regs rT : bvmap 5 word,
getr rT (Z_to_bv 5 2) = getr regs (Z_to_bv 5 2) -> getr rT (Z_to_bv 5 3) = getr regs (Z_to_bv 5 3) ->
getr rT (Z_to_bv 5 4) = getr regs (Z_to_bv 5 4) -> getr rT (Z_to_bv 5 8) = getr regs (Z_to_bv 5 8) ->
getr rT (Z_to_bv 5 9) = getr regs (Z_to_bv 5 9) ->
(forall r, 18 <= r <= 27 -> getr rT (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
aregs_preserved regs rT.
Proof. intros regs rT H2 H3 H4 H8 H9 Hs r Hr. unfold acallee_saved in Hr. destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]]; auto. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma sj_aval_of_val_mem : forall (H : word -> bool) mem a (n : nat) v,
val_mem SEGS (mrestrict H mem) a n v -> aval_mem (aview SEGS H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis RPG : forall a, inFP cmd_PG a -> ~ in_roP SEGS CMD_RLO CMD_RHI a.
Hypothesis RRO : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a.
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis TARG_I : forall fx0 : YK11.FPState, @targ_i_spec fx0 rc SK PI B MT.
Let RUN := paj_run B LAWS.

(* the call target of arg_i *)
Lemma sr_sig_arg_i : SIGMA CS_arg_i = BASE + AF_arg_i.
Proof. rewrite (SIGP CS_arg_i); [reflexivity | cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right])]. Qed.

Lemma sr_jl : sr_jl_stmt B MT.
Proof.
unfold sr_jl_stmt.
intros ly S W regs mem md ch id O kj lyj Sj Wj regsj memj mdj c EV Q
  HPRE HFRM Hfr8 H10 Hid HROD HO HJ Hc Hspj H8j H9j H18j H3j H4j Hsj V18 V9 V8 V1 Hev Hlive HMOK TAILK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : SUP_REMOVE_STK = 16592) by reflexivity.
assert (WA : ARG_I_STK = 16528) by reflexivity.
destruct (sr_slot_range c Hc) as (Hc8 & Hclo & _).
assert (Hcb : 6174544 <= c <= 6175712) by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL in Hclo; lia).
pose proof HJ as (HARj & Hlyj & _ & _ & _ & Hfrj & _ & _ & _ & _ & _ & _ & _ & Hpresj & _).
pose proof Hlyj as (_ & _ & _ & _ & _ & _ & _ & _ & Etopj & _).
destruct (sr_join_seed B HB LAWS PRW Wj lyj Sj regs regsj memj mdj (spZ regs) c HARj Hspj Hal16
  ltac:(lia) ltac:(intros a Ha; apply Hpresj; lia) V18 V9 V8 V1 H9j Hc H18j) as [HS SHOK].
remember (Eimg (Ereg regsj (sr_jextra regs))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsj (sr_jextra regs)) E)
  by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsj r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (sr_jextra regs) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E32 : ew E 32 = getr regs 1) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew E 33 = getr regs 8) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew E 34 = getr regs 9) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = getr regs 18) by exact (EX 3%nat ltac:(lia)).
assert (E2 : ew E 2 = getr regsj 2) by (apply EE; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (rewrite (EE 3%nat 3%bv eq_refl); exact H3j).
assert (E4 : ew E 4 = getr regs 4) by (rewrite (EE 4%nat 4%bv eq_refl); exact H4j).
assert (E8 : ew E 8 = w64 id) by (rewrite (EE 8%nat 8%bv eq_refl), H8j; exact H10).
assert (E9 : ew E 9 = w64 c) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9j).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 32) by (rewrite E2; exact Hspj).
assert (Uc : bv_unsigned (ew E 9) = c) by (rewrite E9; apply unsigned_lit_small; lia).
clear HE EX.
(* 0x8abbc .. 0x8ac04: the checks of c and c + 4, c->fn := REC_REMOVE, c->nargs := 0, a0 := c, a1 := id, and the
   call of arg_i *)
paj_run_tok RUN HS HJ SHOK sr_Bspan.
{ unfold ss_srj, sr_jregions. cbn [ss_mem].
  eapply (awr_ok_cons_stack_off SEGS B E sr_jstack _ _ _ _ _ _ _ _ _ 2%nat (-32));
    [reflexivity | rewrite Usp; lia | unfold sr_jstack; cbn [YP09.r_wlo]; lia | unfold sr_jstack; cbn [YP09.r_whi]; lia |].
  eapply (awr_ok_cons_prog B HB cif_prog_img E sr_jslot _ _ _ _ _ _ _ _ _ 9%nat c); [reflexivity | exact Uc | | apply awr_ok_nil].
  intros a Ha. unfold sr_jslot in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  split; [apply (sj_slot_FP O c a Hc) | apply (sr_slot_PG c a Hc)]; unfold CALL_SIZE; lia. }
lazymatch goal with |- context [with_vm_backing ?x ?y ?z] => set (mdv := with_vm_backing x y z) in *; clearbody mdv end.
(* the run wrote only the frame and the slot's first 8 bytes *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> ~ (c <= a < c + 8) ->
  rdW Wj (ms_mem ms) a = rdW Wj memj a).
{ intros a Ha H1 H2.
  apply (kept_of_frame (segs := SEGS) E _ (w_H Wj) memj (ms_mem ms)
    (fun a => (spZ regs - 32 <= a < spZ regs) \/ (c <= a < c + 8)) HFr); [| exact Ha | intros [Hx | Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  intros b wlo whi a' Hin Hrr. cbv beta. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp, ?Uc in Hrr; lia|]).
  destruct Hin. }
clear HF HFr HG.
(* the slot's two words *)
lazymatch type of HS with st_ok _ _ ?ssx (restrict _ ?msx) =>
  let rg := eval vm_compute in (nth 1 (ss_mem ssx) sr_jslot) in
  pose proof (st_ok_region_nth E ssx (restrict (w_H Wj) msx) 1 rg HS ltac:(vm_compute; reflexivity)) as HRg;
  cbn [ms_mem restrict] in HRg end.
pose proof (field_of_region E _ 9%nat c _ _ _ _ _ 4 4 (SLit 0) 0 HRg Uc ltac:(left; reflexivity) ltac:(reflexivity)
  ltac:(cbn; lia) ltac:(cbn; lia)) as VN.
pose proof (field_of_region E _ 9%nat c _ _ _ _ _ 0 4 (SLit 2) 2 HRg Uc ltac:(right; left; reflexivity) ltac:(reflexivity)
  ltac:(cbn; lia) ltac:(cbn; lia)) as VF.
assert (VNa : aval_mem (rdW Wj (ms_mem ms)) (c + CALL_OFF_NARGS) 4 0) by exact (sj_aval_of_val_mem _ _ _ _ _ VN).
assert (VFa : aval_mem (rdW Wj (ms_mem ms)) (c + CALL_OFF_FN) 4 REC_REMOVE) by exact (sj_aval_of_val_mem _ _ _ _ _ VF).
clear HRg VN VF.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs + -32) by (unfold spZ at 1; rewrite P2, Usp; lia).
assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, E3; exact Hgp).
assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, E4; exact Htp).
assert (P10' : getr (ms_regs ms) 10 = w64 c) by (rewrite P10; exact E9).
assert (P11' : getr (ms_regs ms) 11 = w64 id) by (rewrite P11; exact E8).
pose proof (proj1 HJ) as HARc.
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW Wj (ms_mem ms)))
  by exact (sr_aro_journal B LAWS RPG RRO _ _ O ly S W mem md [] lyj Sj Wj (ms_mem ms) mdv kj HAR HO HJ HROD).
(* the frame chain at the call: s0 = id is no frame pointer *)
assert (HCH : achain lyj (rdW Wj (ms_mem ms)) (spZ regs + -32) (s0Z (ms_regs ms)) []).
{ assert (Hs0 : s0Z (ms_regs ms) = id mod 2 ^ 64) by (unfold s0Z; rewrite P8, E8; apply sj_u64).
  rewrite Hs0. left. split; [|reflexivity].
  destruct (Z_lt_le_dec id 0) as [Hn | Hn].
  - right. left. assert (Hm : id mod 2 ^ 64 = id + 2 ^ 64)
      by (rewrite <- (Z.mod_add id 1 (2 ^ 64)) by lia; apply Z.mod_small; lia).
    rewrite Hm, Etopj. lia.
  - left. rewrite Z.mod_small by lia. lia. }
(* a byte of a live block is no byte of the slot *)
assert (HBNS : forall b m i, In (b, m) (ablocks B lyj Sj) -> 0 <= i < req_size m -> ~ (c <= b + i < c + CALL_SIZE)).
{ intros b m i Hin Hi Hr. apply (blk_img SEGS B LAWS lyj Sj Wj (ms_mem ms) mdv b m (b + i) HARc Hin ltac:(lia)).
  apply cif_prog_img. exact (sr_slot_PG c (b + i) Hc Hr). }
set (FP1 := [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * 0, c + CALL_OFF_ARGS + 8 * 0 + 8)]).
assert (HFP1 : forall a, inFP FP1 a -> c + 4 <= a < c + 16).
{ intros a Ha. unfold FP1 in Ha. apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_NARGS in Ha; lia|].
  apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_ARGS in Ha; lia | destruct (inFP_nil a Ha)]. }
eapply SRr_bind.
{ eapply (cl_callS_wideF B LAWS Wj (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (SIGMA CS_arg_i)) SUP_REMOVE_STK (spZ regs)
    (sr_FP O) ly S W mem md [] lyj Sj mdv kj ARG_I_STK FP1 EV_ARG_I (-32) (Z_to_bv 64 (BASE + 18196)) [] _ HJ Hsp1).
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - exact P3'.
  - exact P4'.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - exact HCH.
  - (* arg_i's statement *)
    intros HPREc. rewrite sr_sig_arg_i.
    eapply SRr_mono.
    { exact (TARG_I fx lyj Sj Wj (ms_regs ms) (ms_mem ms) mdv [] c id 0 HPREc HFRM
        ltac:(rewrite Hfrj; exact Hfr8) HRODc (cmd_ro_ok_of_aro lyj Sj Wj (ms_mem ms) mdv HARc HRODc)
        P10' P11' Hid Hc VNa ltac:(unfold REC_ARGS_MAX; lia) Hev Hlive HMOK). }
    unfold apost_baseF. cbv beta.
    intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hf1 & Hf2 & HJ2 & HP2 & HQ2).
    exists fx1, ly2, S2, regs2, mem2, md2. split; [rewrite P1; reflexivity|]. split; [exact Hf1|].
    split; [exact Hf2|]. split; [exact HJ2|]. split; [exact HP2 | exact HQ2].
  - (* arg_i's footprint, c->nargs and c->args[0], is a part of the program's statics in sup_remove's footprint *)
    intros a Ha. pose proof (HFP1 a Ha) as Hr. unfold awr_byte, awr_prog_or_caller.
    right. right. right. right. left.
    assert (Hpg : inFP cmd_PG a) by (apply (sr_slot_PG c a Hc); unfold CALL_SIZE; lia).
    split; [apply (sj_slot_FP O c a Hc); unfold CALL_SIZE; lia|].
    split; [exact (HPROG B HB a Hpg) | exact (cif_prog_img a Hpg)].
  - (* no footprint byte of arg_i lies in sup_remove's stack window *)
    intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. pose proof (HFP1 a Ha). lia. }
cbv beta. intros W2 c2 Hwle2 (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HJ2c & HP2 & HQ2).
cbv beta zeta in HQ2.
destruct HQ2 as (BB2 & MLE2 & [(Hm6 & _) | (_ & p & (Hp4096 & Hp64) & HpPerm & HpApart & HpN & HpA & HpS)]).
{ exfalso. unfold REC_ARGS_MAX in Hm6. lia. }
(* back at 0x8ac08 *)
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
pose proof HJ2c as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & F2c & F3c & _).
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
  - apply (mbyte_of_aview SEGS). apply F1c; [lia | lia | intros Hf; pose proof (HFP1 a Hf); lia].
  - intros _. apply (apresent_writable SEGS). apply Hpres2. lia. }
clear HS.
(* arg_i returned at fx1: the state after the call at fx1 (st_ok_xfx), the run after the call at fx1 *)
lazymatch type of HS2 with
| st_ok_pi ?sg ?vl ?Ex ?ssx (mkst ?rx ?pcx ?mx ?rm) =>
  assert (HS : st_ok_pi (fx := fx1) sg vl Ex ssx (@mkst fx1 rx pcx mx rm))
    by exact (YL05.st_ok_xfx fx fx1 sg Ex (abs_ss vl ssx) rx pcx mx HS2)
end.
clear HS2. rewrite <- (restrict_mkst_fx (fx := fx1)) in HS.
pose proof (paj_run (fx := fx1) B LAWS) as RUN1.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ec eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM Ec) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 36)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regsj (sr_jextra regs)) Ec) by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HE2.
assert (Usp2 : bv_unsigned (ew Ec 2) = spZ regs - 32) by (rewrite OLD2 by lia; exact Usp).
assert (SHOK2 : sh_ok SEGS sr_Bxj [] Ec (mrestrict (w_H W2) mem2)) by (unfold sh_ok; apply Forall_nil).
(* 0x8ac08 .. 0x8ac2c: a1 := the literal, a2 := 1, a0 := c, the frame's restore and the tail jump into answer *)
paj_run_tok RUN1 HS HJ2 SHOK2 sr_Bspan.
{ eapply (awr_ok_cons_stack_off SEGS B Ec _ _ _ _ _ _ _ _ _ _ 2%nat (-32));
    [reflexivity | rewrite Usp2; lia | cbn; lia | cbn; lia | apply awr_ok_nil]. }
lazymatch goal with |- context [with_vm_backing ?x ?y ?z] => set (mdv2 := with_vm_backing x y z) in *; clearbody mdv2 end.
match goal with |- SRr _ _ {| cfg_ms := ?msx; cfg_model := _ |} _ => rename msx into ms3 end.
(* the run after the call wrote only the frame *)
lazymatch goal with
| HFx : frame_of Ec _ (mrestrict _ mem2) (mrestrict _ (ms_mem ms3)) |- _ =>
  assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) -> rdW W2 (ms_mem ms3) a = rdW W2 mem2 a)
  by (intros a Ha Hn;
      apply (kept_of_frame (segs := SEGS) Ec _ (w_H W2) mem2 (ms_mem ms3) (fun a => spZ regs - 32 <= a < spZ regs) HFx);
      [ intros b wlo whi a' Hin Hrr; cbv beta; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp2 in Hrr; lia|]);
        destruct Hin
      | exact Ha | exact Hn ])
end.
(* at the tail jump: the frame is popped, a0 = c, a1 = the literal, a2 = 1 *)
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12. prreg HS (18%bv : bv 5) T18.
pose proof (regs_kept_of_st_ok SEGS Ec _ _ regsj (sr_jextra regs) (map (Z_to_bv 5) [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27])
  HS HAE2 ltac:(vm_compute; reflexivity)) as KR. cbn [ms_regs restrict] in KR.
assert (KR' : forall r, In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr (ms_regs ms3) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite (KR (Z_to_bv 5 r) (in_map _ _ _ Hr)). cbn [In] in Hr.
  destruct Hr as [<- | [<- | Hr]]; [exact H3j | exact H4j | apply Hsj; lia]. }
assert (E283c : ew Ec 283 = Z_to_bv 64 0x21ce0).
{ pose proof (HEI2 283%nat ltac:(unfold A_TEXT, A_LIM; lia)) as H.
  change (VAL 283%nat) with (VAL (A_OBJ 42)) in H. rewrite (VOBJS 42%nat ltac:(vm_compute; lia)) in H.
  apply bv_eq. rewrite H. rewrite unsigned_lit_small by lia. vm_compute. reflexivity. }
assert (Q2 : getr (ms_regs ms3) 2 = getr regs 2).
{ rewrite T2, Usp2. replace (spZ regs - 32 + 32) with (spZ regs) by lia. apply Z_to_bv_bv_unsigned. }
assert (Q1 : getr (ms_regs ms3) 1 = getr regs 1) by (rewrite T1, OLD2 by lia; exact E32).
assert (Q8 : getr (ms_regs ms3) 8 = getr regs 8) by (rewrite T8, OLD2 by lia; exact E33).
assert (Q9 : getr (ms_regs ms3) 9 = getr regs 9) by (rewrite T9, OLD2 by lia; exact E34).
assert (Q18 : getr (ms_regs ms3) 18 = getr regs 18) by (rewrite T18, OLD2 by lia; exact E35).
assert (HPT : aregs_preserved regs (ms_regs ms3)).
{ apply sj_aregs; [exact Q2 | exact (KR' 3 ltac:(cbn; tauto)) | exact (KR' 4 ltac:(cbn; tauto)) | exact Q8 | exact Q9 |].
  intros r Hr. assert (Hr' : r = 18 \/ In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]) by (cbn [In]; lia).
  destruct Hr' as [-> | Hr']; [exact Q18 | exact (KR' r Hr')]. }
(* arg_i kept the program's statics outside its footprint *)
assert (HFP1pos : Forall (fun r => 0 < fst r) FP1).
{ unfold FP1. apply Forall_cons; [cbn [fst]; unfold CALL_OFF_NARGS; lia|].
  apply Forall_cons; [cbn [fst]; unfold CALL_OFF_ARGS; lia | apply Forall_nil]. }
assert (KEEPC : forall a, inFP cmd_PG a -> ~ (c + 4 <= a < c + 16) -> rdW W2 mem2 a = rdW Wj (ms_mem ms) a).
{ intros a Hpg Hn. destruct (sr_prog_sep B HB cif_prog_img a Hpg) as (Himg & Hno & Herr & _).
  apply F3c; [exact Himg | exact Hno | exact Herr |].
  apply fp_spares_closed; [exact (sink_closed_pos _ HFP1pos) | intros Hf; exact (Hn (HFP1 a Hf))]. }
(* the copy's block lies below the stack *)
assert (Hpin : In (p, Z.of_nat (length (dec id)) + 1) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HpPerm | left; reflexivity]).
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hpin) as (_ & _ & Hpc & _).
pose proof (req_size_pos (Z.of_nat (length (dec id)) + 1) ltac:(lia)) as [_ Hrq].
replace (c + CALL_OFF_ARGS + 8 * 0) with (c + CALL_OFF_ARGS) in HpA by lia.
apply (TAILK fx1 Hfx ly2 S2 W2 (ms_regs ms3) (ms_mem ms3) mdv2 p).
- exact HJ2.
- unfold spZ at 1. rewrite Q2. reflexivity.
- exact Q1.
- exact HPT.
- rewrite T10, OLD2 by lia. exact E9.
- rewrite T11. exact E283c.
- exact T12.
- (* c->fn: stored by the run before the call, outside arg_i's footprint and the frame *)
  apply (sj_aval_keep (rdW Wj (ms_mem ms))); [exact VFa |].
  intros k Hk. change (Z.of_nat 4) with 4 in Hk. unfold CALL_OFF_FN in *.
  assert (Hpg : inFP cmd_PG (c + 0 + k)) by (apply (sr_slot_PG c); [exact Hc | unfold CALL_SIZE; lia]).
  rewrite KEEP3 by lia. apply KEEPC; [exact Hpg | lia].
- apply (sj_aval_keep (rdW W2 mem2)); [exact HpN |].
  intros k Hk. change (Z.of_nat 4) with 4 in Hk. unfold CALL_OFF_NARGS in *. apply KEEP3; lia.
- apply (sj_aval_keep (rdW W2 mem2)); [exact HpA |].
  intros k Hk. change (Z.of_nat 8) with 8 in Hk. unfold CALL_OFF_ARGS in *. apply KEEP3; lia.
- exact (astr_atR_kept (rdW W2 mem2) (rdW W2 (ms_mem ms3)) (spZ regs - 32) (spZ regs) p (dec id) KEEP3 HpS
    ltac:(lia) ltac:(lia) ltac:(lia)).
- exact Hp4096.
- exact HpPerm.
- exact HpApart.
- (* the program's statics outside c->fn, c->nargs and c->args[0] *)
  intros a Hpg Hn. pose proof (sj_PG_low a Hpg).
  rewrite KEEP3 by lia. rewrite KEEPC by (first [exact Hpg | lia]). apply KEEP1; lia.
- (* the live blocks at the join *)
  intros b m i Hin Hi.
  destruct (al_blocks _ _ LAWS lyj Sj Wj (ms_mem ms) mdv b m HARc Hin) as (_ & Hb4096 & Hbc & _).
  pose proof (HBNS b m i Hin Hi) as Hns. unfold CALL_SIZE in Hns.
  assert (Hin2 : In (b, m) (ablocks B ly2 S2))
    by (eapply Permutation_in; [apply Permutation_sym; exact HpPerm | right; exact Hin]).
  rewrite KEEP3 by lia.
  rewrite (F2c b m i Hin Hin2 Hi) by (intros Hf; pose proof (HFP1 _ Hf); lia).
  apply KEEP1; lia.
- exact BB2.
- exact MLE2.
Qed.
End c.
End b.
End a.
