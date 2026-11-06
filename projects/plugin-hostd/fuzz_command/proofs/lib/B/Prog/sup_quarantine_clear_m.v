(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_quarantine_clear (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan), its middle: the segment from the return of record (0x8bdcc) through the call of arg_s
   (0x8bdd4), and the segment from the return of arg_s (0x8bdd8) through the call of rec_shape_of (0x8bde4), each
   ending in the next segment (sup_quarantine_clear_t.v's sqcb_S3). In the form of lib/A/Prog/sup_quarantine_clear_s3.v
   (the A walk, a working branch f2402580166: sqc_SX's call of xstrdup and of rec_shape_of), re-derived
   on B's code: B calls arg_s where A stored the slot's fields itself and called xstrdup. *)

(* 0x8bdcc .. 0x8bdd4: mv s1,a0; mv a1,s0; jal arg_s.
   0x8bdd8 .. 0x8bde4: auipc a0,0xfff96; addi a0,a0,0x68 (the verb literal 0x21e40, listing object 70); li a1,16;
   jal rec_shape_of. No branch, no ASan check, no UBSan trap, no store. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c rec_calls_free_c record_c arg_s_c rec_shape_of_c mix_call_c hand_back_c answer_c sup_quarantine_clear_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecRest CmdRecRo CmdRecImg RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_quarantine_clear_aux sup_quarantine_clear_t.
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

Lemma sqcb_aval_val : forall (W : world SEGS) mem a n v,
aval_mem (rdW W mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem) a n v.
Proof.
intros W mem a n v H k Hk. pose proof (H k Hk) as Hv. unfold aview in Hv.
unfold val_mem.
destruct (mbyte SEGS (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|] eqn:Eb;
  cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as Hv. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned, Hv. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
cbv [YO0f.le_byte YG0f.le_byte]. symmetry. apply Z.mod_mod. lia.
Qed.

Lemma sqcb_val_aval : forall (W : world SEGS) mem a n v,
val_mem SEGS (mrestrict (w_H W) mem) a n v -> aval_mem (rdW W mem) a n v.
Proof.
intros W mem a n v H k Hk. pose proof (H k Hk) as Hb. unfold aview. rewrite Hb. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
repeat first [progress unfold YO0f.le_byte | progress unfold YG0f.le_byte]. apply Z.mod_mod. lia.
Qed.

Lemma sqcb_val_kept : forall (W W' : world SEGS) m m' a n v,
val_mem SEGS (mrestrict (w_H W) m) a n v ->
(forall k, (k < n)%nat -> rdW W' m' (a + Z.of_nat k) = rdW W m (a + Z.of_nat k)) ->
val_mem SEGS (mrestrict (w_H W') m') a n v.
Proof.
intros W W' m m' a n v Hv Hk. apply sqcb_aval_val. intros k Hkn. rewrite (Hk k Hkn).
exact (sqcb_val_aval W m a n v Hv k Hkn).
Qed.

(* a frame kept byte by byte is kept *)
Lemma sqcb_frame_kept : forall (W W' : world SEGS) m m' sp1 regs0,
sqcb_frame_at (mrestrict (w_H W) m) sp1 regs0 ->
(forall a, sp1 <= a < sp1 + SQB_FRAME -> rdW W' m' a = rdW W m a) ->
sqcb_frame_at (mrestrict (w_H W') m') sp1 regs0.
Proof.
intros W W' m m' sp1 regs0 HF K j r Hjr. apply (sqcb_val_kept W W' m m'); [exact (HF j r Hjr)|].
assert (Hj : (j < 3)%nat) by (change 3%nat with (length sqcb_saved); apply nth_error_Some; rewrite Hjr; discriminate).
intros kk Hkk. apply K. unfold SQB_FRAME. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's callees (sup_quarantine_clear_c.v, at every FP state), the object bridge, and the walk hypotheses
   (a Theorem Labs lane's RULING-STMT.md section 1): the record HB, the image facts IMG of a Theorem Labs lane's lib/B/Prog/CmdRecBase.v, from
   which a Theorem Labs lane's CmdRecRest / CmdRecRo / CmdRecImg give the read-only, program-static and heap-tail facts below *)
Context {TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT}.
Context {TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT}.
Context {TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT}.
Context {VOBJS : cmd_val_objs}.
Context {HB : CmdBSyms B}.
Context {IMG : CmdRecBase.cmd_img_facts SEGS B}.
Context {MTL : ameter_laws MT}.
Context {cmd_sig_prog_PB : cmd_sig_prog}.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let cmd_prog_img := @CmdRecRest.cmd_prog_img rc SK SEGS B LAWS HB IMG.
Let cmd_ro_prog_apart := @CmdRecRest.cmd_ro_prog_apart rc SK SEGS B LAWS HB IMG.
Let ROB := @CmdRecRo.ROB rc SK SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro := @CmdRecRo.cmd_ro_ok_of_aro rc SK SEGS B LAWS HB IMG.
Let CMD_RO_IN := @CmdRecRo.CMD_RO_IN rc SK SEGS B LAWS HB IMG.
Let cmd_heap_tail_vis := @CmdRecImg.cmd_heap_tail_vis rc SEGS B LAWS HB.

Let S3L := sqcb_S3 B MT (TANSWER := TANSWER) (HB := HB) (IMG := IMG) (MTL := MTL) (cmd_sig_prog_PB := cmd_sig_prog_PB).

(* the walk at the return of arg_s (0x8bdd8) *)
Definition sqcb_S2_spec : Prop :=
forall ly S W regs mem md ch pw which R O x (L1 F O1 : list (Z * Z)) p ly2 S2 W2 (regs2 : bvmap 5 word) mem2 md2 k2,
sqcb_pre B MT ly S W regs mem md ch pw which R O -> which = Some x ->
ajournal SEGS B SQB_STK (spZ regs) (sqcb_FP O) ly S W mem md [] ly2 S2 W2 mem2 md2 k2 ->
k2 = EV_RECORD R + EV_ARG_S ->
sqcb_frame_at (mrestrict (w_H W2) mem2) (spZ regs - SQB_FRAME) regs ->
getr regs2 2 = w64 (spZ regs - SQB_FRAME) -> getr regs2 3 = w64 (as_gp B) -> getr regs2 4 = w64 (as_tp B) ->
getr regs2 9 = w64 (rec_slot R) ->
(forall r, 18 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
rec_repA B ly2 S2 (rdW W2 mem2) (rec_record R SQB_FN [x]) ((p, Z.of_nat (length x) + 1) :: O1) ->
Permutation (ablocks B ly S) (L1 ++ F) -> (forall pn, In pn F -> In pn O) ->
(forall pn, In pn O1 <-> In pn O /\ ~ In pn F) ->
Permutation (ablocks B ly2 S2) ((p, Z.of_nat (length x) + 1) :: L1) ->
Forall (fun qk => iv_apart p (Z.of_nat (length x) + 1) (fst qk) (snd qk)) L1 ->
mo_le MT S S2 (XM_RECORD MT R + XM_ARG_S MT which) ->
blocks_bytes S2 <= blocks_bytes S + LIVE_ARG_S which ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + SQB_RETA)) mem2 (seg_rom SEGS)) md2)
(apost_baseF SEGS B SQB_STK (sqcb_FP O) regs ly S W mem md (EV_SUP_QUARANTINE_CLEAR R) (sqcb_Q B MT ly S R O which)).

Lemma sqcb_S2 : sqcb_S2_spec.
Proof.
intros ly S W regs mem md ch pw which R O x L1 F O1 p ly2 S2 W2 regs2 mem2 md2 k2
  PRE Hwh HJ Hk HFRM G2 G3 G4 G9 G18 HREP2 HPERM HFO HO1 HPERM2 HFR2 MLE2 HBB2.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof PRE as (HPRE & Hfrm0 & HROD & HRO & H10 & Hpw & HARG & HREP & HFR8 & HEV & HLIVE & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQTi).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HST : SQB_STK = 16592) by reflexivity.
rewrite HST in Hslo.
set (sp0 := spZ regs) in *.
set (n := Z.of_nat (length x) + 1) in *.
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (sqcb_rec_repA_in B ly S _ R O HREP).
pose proof (proj1 HJ) as HAR2.
assert (Hsp0 : 2 ^ 46 + 32 <= sp0 <= 2 ^ 47) by lia.
assert (G2u : bv_unsigned (getr regs2 2) = sp0 - SQB_FRAME)
  by (rewrite G2; unfold w64; apply unsigned_lit_small; unfold SQB_FRAME; lia).
assert (HS : st_ok_pi SEGS VAL (sqcb_E regs2 regs) (sqcb_ssF SQB_RETA sr_atoms)
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + SQB_RETA)) mem2 (seg_rom SEGS)))).
{ apply sqcb_seed.
  - rewrite G2u. unfold SQB_FRAME. lia.
  - rewrite G2u. unfold SQB_FRAME. replace (sp0 - 32) with (sp0 + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
  - unfold sqcb_E. apply regs_ok_Eimg_Ereg.
  - rewrite G2u. exact HFRM. }
assert (EE : forall kk (rr : bv 5), Z.of_nat kk = bv_unsigned rr -> ew (sqcb_E regs2 regs) kk = getr regs2 rr)
  by (intros kk rr Hkk; exact (sqcb_E_reg regs2 regs kk rr Hkk)).
assert (V311 : ew (sqcb_E regs2 regs) 311 = Z_to_bv 64 SQB_VERB) by exact (sqcb_E_verb regs2 regs VOBJS).
assert (HEI : img_env VAL A_LIM (sqcb_E regs2 regs)) by exact (sqcb_E_img regs2 regs).
set (E := sqcb_E regs2 regs) in *.
assert (SHOK : sh_ok SEGS (SLit 0) [] E (mrestrict (w_H W2) mem2)) by (unfold sh_ok; constructor).
(* 0x8bdd8 .. 0x8bde4: a0 := the verb literal, a1 := 16, jal rec_shape_of *)
paj_run_tok RUN HS HJ SHOK sqcb_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?Bv ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?f0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg Bv Ex rs' stk spx fp b0 bc f0 lyx own) end.
  apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|]. apply awr_ok_nil. }
pmkst HS. sqcb_md.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
lazymatch goal with HFx : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ => rename HFx into HFRC end.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFRC
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia|]); destruct Hin)) as KE.
assert (HRK : forall a, 0 <= a < 2 ^ 64 -> rdW W2 (ms_mem ms) a = rdW W2 mem2 a)
  by (intros a Ha; exact (KE a Ha (fun H => H))).
pose proof (proj1 HJ) as HARc.
assert (Q1 : getr (ms_regs ms) 1 = w64 (BASE + SQB_RETS)) by (rewrite P1; reflexivity).
assert (Q2 : getr (ms_regs ms) 2 = w64 (sp0 - SQB_FRAME)) by (rewrite P2, (EE 2%nat 2%bv eq_refl); exact G2).
assert (Q2s : spZ (ms_regs ms) = sp0 + -32)
  by (unfold spZ; rewrite Q2; unfold w64; rewrite unsigned_lit_small by (unfold SQB_FRAME; lia); unfold SQB_FRAME; lia).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl); exact G3).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl); exact G4).
assert (Q9 : getr (ms_regs ms) 9 = w64 (rec_slot R)) by (rewrite P9, (EE 9%nat 9%bv eq_refl); exact G9).
assert (Q10 : getr (ms_regs ms) 10 = w64 SQB_VERB) by (rewrite P10, V311; reflexivity).
assert (Q11 : getr (ms_regs ms) 11 = w64 (Z.of_nat (length sqcb_verb))) by (rewrite P11; reflexivity).
assert (X18_27 : forall r, 18 <= r <= 27 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite <- (G18 r Hr).
  assert (H10r : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct H10r as [-> | H10r]); [..| subst r];
  rewrite (st_ok_restrict_reg SEGS (w_H W2) E _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  lazymatch goal with |- ew _ ?m = getr _ (Z_to_bv 5 ?rr) => exact (EE m (Z_to_bv 5 rr) eq_refl) end. }
assert (HAROd : arodata_okP SEGS RLO RHI B (rdW W2 (ms_mem ms)))
  by exact (sqcb_aro B (ROB := ROB) cmd_ro_prog_apart _ ly S W mem md O ly2 S2 W2 (ms_mem ms) mdv [] _ sp0 HAR HOin HJ HROD).
assert (HROd : cmd_ro_ok (rdW W2 (ms_mem ms))) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HARc HAROd).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
(* the call of rec_shape_of("quarantine_clear", 16) (0x8bde4) *)
rewrite (cmd_sig_prog_PB CS_rec_shape_of ltac:(vm_compute; tauto)).
change (pa_val A_TEXT + cmd_af CS_rec_shape_of) with (BASE + AF_rec_shape_of).
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS W2 (ms_regs ms) (ms_mem ms) _ SQB_STK sp0 (sqcb_FP O) ly S W mem md [] ly2 S2 _ _
    REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (-32) (w64 (BASE + SQB_RETS))
    (fun ly3 S3 W3 regs3 mem3 md3 =>
      (exists q, getr regs3 10 = w64 q /\ 0 <= q < 2 ^ 64 /\
       forall O', astr_argA B ly3 S3 (rdW W3 mem3) (in_roP SEGS RLO RHI) O' q (Some (shape_of sqcb_verb))) /\
      Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) /\ ly3 = ly2 /\ S3 = S2) HJ Q2s).
  - reflexivity.
  - lia.
  - unfold REC_SHAPE_OF_STK, ESTACK. lia.
  - rewrite HST. unfold REC_SHAPE_OF_STK, ESTACK. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - unfold w64. apply sqcb_ret_ok. right; right; reflexivity.
  - unfold w64. rewrite sqcb_ret_val by (right; right; reflexivity). unfold SQB_RETS, AF_sup_quarantine_clear. lia.
  - intros HPRE1. eapply SRr_mono.
    + apply (TREC_SHAPE_OF fx ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ SQB_VERB sqcb_verb HPRE1 HAROd Q10
        ltac:(unfold SQB_VERB; lia) Q11 ltac:(vm_compute; reflexivity) HROd VOBJS).
      * intros _. split; [exact (sqcb_verb_bytes _ HROd)|]. right. exact (sqcb_verb_argA B HB ly2 S2 _ [] CMD_RO_IN HROd).
      * rewrite Hk in Hnev2. unfold EV_SUP_QUARANTINE_CLEAR, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC, EV_REC_SHAPE_OF in *. lia.
    + cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HQ3).
      exists ly3, S3, regs3, mem3, md3. split; [rewrite Q1; reflexivity|]. split; [exact HJ3|]. split; [exact HP3|].
      exact HQ3.
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 &
  ((q & Hq10 & Hq64 & HqA) & Hperm3 & Ely3 & ES3)).
subst ly3 S3.
assert (CS3 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs3 rr = getr (ms_regs ms) rr)
  by (intros rr Hr; pose proof (HP3 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx).
assert (R2 : getr regs3 2 = w64 (sp0 - SQB_FRAME))
  by (rewrite (CS3 2%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact Q2).
assert (R3 : getr regs3 3 = w64 (as_gp B))
  by (rewrite (CS3 3%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact Q3).
assert (R4 : getr regs3 4 = w64 (as_tp B))
  by (rewrite (CS3 4%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact Q4).
assert (R9 : getr regs3 9 = w64 (rec_slot R))
  by (rewrite (CS3 9%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact Q9).
assert (R18 : forall r, 18 <= r <= 27 -> getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite (HP3 r ltac:(unfold acallee_saved; lia)). exact (X18_27 r Hr). }
(* the frame and the recorder survive rec_shape_of, which writes nothing outside its window *)
assert (HKS : forall a, sp0 - SQB_FRAME <= a < sp0 -> rdW W3 mem3 a = rdW W2 mem2 a).
{ intros a Ha. rewrite <- (HRK a ltac:(unfold SQB_FRAME in Ha; lia)).
  apply (sqcb_keep_stack B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc3); [intros b Hb; exfalso; exact (inFP_nil b Hb) | | ];
  unfold SQB_FRAME in Ha; lia. }
assert (HFRM3 : sqcb_frame_at (mrestrict (w_H W3) mem3) (sp0 - SQB_FRAME) regs).
{ apply (sqcb_frame_kept W2 W3 mem2 mem3 _ regs HFRM). intros a Ha. apply HKS. lia. }
assert (HO22 : forall pn, In pn ((p, n) :: O1) -> In pn (ablocks B ly2 S2)) by exact (sqcb_rec_repA_in B _ _ _ _ _ HREP2).
assert (HREP3 : rec_repA B ly2 S2 (rdW W3 mem3) (rec_record R SQB_FN [x]) ((p, n) :: O1)).
{ apply (sqcb_rec_repA_ext B ly2 S2 (rdW W2 mem2) ly2 S2 _ _ _ HREP2 HO22).
  intros a [Ha | [Ha | (pn & Hpn & Ha)]].
  - rewrite <- (HRK a ltac:(unfold A_G_REC, REC_SIZE in Ha; lia)).
    apply (sqcb_keep_prog B HB cmd_prog_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3);
    [constructor | intros Hf; exact (inFP_nil a Hf) | exact (sqcb_PG_grec a Ha)].
  - rewrite <- (HRK a ltac:(unfold A_REC_SPILL, SC_SIZE in Ha; lia)).
    apply (sqcb_keep_prog B HB cmd_prog_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJc3);
    [constructor | intros Hf; exact (inFP_nil a Hf) | exact (sqcb_PG_spill a Ha)].
  - destruct pn as [b m]. cbn [fst snd] in Ha. pose proof (HO22 _ Hpn) as Hin.
    destruct (sqcb_blk_bounds B ly2 S2 W2 mem2 md2 b m HAR2 Hin) as (Hb & Hbc & _ & Hmr & _).
    replace a with (b + (a - b)) by lia.
    rewrite <- (HRK (b + (a - b)) ltac:(lia)).
    apply (sqcb_keep_blk B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b m (a - b) HJc3 Hin Hin); [lia|].
    intros Hf. exact (inFP_nil _ Hf). }
apply (S3L ly S W regs mem md ch pw which R O x L1 F O1 p ly2 S2 W3 regs3 mem3 md3 (k2 + EV_REC_SHAPE_OF) q
  PRE Hwh HJ3 ltac:(rewrite Hk; unfold EV_REC_SHAPE_OF; lia) HFRM3 R2 R3 R4 R9 Hq10 Hq64 R18 HqA HREP3
  HPERM HFO HO1 HPERM2 HFR2 MLE2 HBB2).
Qed.

(* the walk at the return of record (0x8bdcc) *)
Definition sqcb_S1_spec : Prop :=
forall ly S W regs mem md ch pw which R O x (F O1 : list (Z * Z)) ly1 S1 W1 (regs1 : bvmap 5 word) mem1 md1 k1,
sqcb_pre B MT ly S W regs mem md ch pw which R O -> which = Some x ->
ajournal SEGS B SQB_STK (spZ regs) (sqcb_FP O) ly S W mem md [] ly1 S1 W1 mem1 md1 k1 ->
k1 = EV_RECORD R ->
sqcb_frame_at (mrestrict (w_H W1) mem1) (spZ regs - SQB_FRAME) regs ->
getr regs1 2 = w64 (spZ regs - SQB_FRAME) -> getr regs1 3 = w64 (as_gp B) -> getr regs1 4 = w64 (as_tp B) ->
getr regs1 8 = w64 pw -> getr regs1 10 = w64 (rec_slot R) ->
(forall r, 18 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
rec_repA B ly1 S1 (rdW W1 mem1) (rec_record R SQB_FN []) O1 ->
Permutation (ablocks B ly S) (ablocks B ly1 S1 ++ F) -> (forall pn, In pn F -> In pn O) ->
(forall pn, In pn O1 <-> In pn O /\ ~ In pn F) ->
mo_le MT S S1 (XM_RECORD MT R) -> blocks_bytes S1 <= blocks_bytes S ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + SQB_RETR)) mem1 (seg_rom SEGS)) md1)
(apost_baseF SEGS B SQB_STK (sqcb_FP O) regs ly S W mem md (EV_SUP_QUARANTINE_CLEAR R) (sqcb_Q B MT ly S R O which)).

Lemma sqcb_S1 : sqcb_S1_spec.
Proof.
intros ly S W regs mem md ch pw which R O x F O1 ly1 S1 W1 regs1 mem1 md1 k1
  PRE Hwh HJ Hk HFRM G2 G3 G4 G8 G10 G18 HREP1 HPERM HFO HO1 MLE1 HBB1.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof PRE as (HPRE & Hfrm0 & HROD & HRO & H10 & Hpw & HARG & HREP & HFR8 & HEV & HLIVE & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQTi).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HST : SQB_STK = 16592) by reflexivity.
rewrite HST in Hslo.
set (sp0 := spZ regs) in *.
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (sqcb_rec_repA_in B ly S _ R O HREP).
assert (Hn16 : (length (r_calls R) <= 16)%nat).
{ destruct HREP as (Q0 & (_ & _ & _ & (Gl & _) & _) & _). exact Gl. }
destruct (sqcb_slot_bounds R Hn16) as (Hcs & Hcb).
set (c := rec_slot R) in *.
pose proof (proj1 HJ) as HAR1.
assert (Hsp0 : 2 ^ 46 + 32 <= sp0 <= 2 ^ 47) by lia.
(* the argument: a string in a live block that is none of the recorder's, so record() kept it *)
destruct HARG as (x' & Hwh' & Hblk & Hxs & Hxl & Hxap).
rewrite Hwh in Hwh'. injection Hwh' as <-.
set (n := Z.of_nat (length x) + 1) in *.
destruct Hblk as (b0 & m0 & Hin0 & Hb01 & Hb02).
assert (HnO : ~ In (b0, m0) O).
{ intros HO. rewrite Forall_forall in Hxap. pose proof (Hxap _ HO) as Hap. cbn [fst snd] in Hap.
  unfold iv_apart in Hap. unfold n in *. lia. }
assert (Hin1 : In (b0, m0) (ablocks B ly1 S1)).
{ apply (Permutation_in _ HPERM) in Hin0. apply in_app_or in Hin0 as [H | H]; [exact H|].
  exfalso. exact (HnO (HFO _ H)). }
destruct (sqcb_blk_bounds B ly S W mem md b0 m0 HAR Hin0) as (Hb0 & Hbc0 & Hm00 & Hmr0 & _).
assert (Hxs1 : astr_atR (rdW W1 mem1) pw x).
{ apply (sqcb_str_keep (rdW W mem)); [exact Hxs|]. intros a Ha.
  replace a with (b0 + (a - b0)) by lia.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
  apply (F2 b0 m0 (a - b0) Hin0 Hin1); [unfold n in *; lia|].
  intros Hf. destruct (sqcb_inFP_cases O _ Hf) as [HP | (b2 & m2 & Hin2 & Ha2)].
  - apply (RecBLemmas.recb_heap_noimg_m B ly S W mem md b0 m0 (b0 + (a - b0)) HAR Hin0); [unfold n in *; lia|].
    exact (cmd_prog_img _ (sqcb_PG_tfib _ HP)).
  - assert (Hne : (b0, m0) <> (b2, m2)) by (intros E0; apply HnO; rewrite E0; exact Hin2).
    destruct (sqcb_blk_apart B ly S W mem md b0 m0 b2 m2 HAR Hin0 (HOin _ Hin2) Hne); unfold n in *; lia. }
assert (G2u : bv_unsigned (getr regs1 2) = sp0 - SQB_FRAME)
  by (rewrite G2; unfold w64; apply unsigned_lit_small; unfold SQB_FRAME; lia).
assert (HS : st_ok_pi SEGS VAL (sqcb_E regs1 regs) (sqcb_ssF SQB_RETR sr_atoms)
  (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + SQB_RETR)) mem1 (seg_rom SEGS)))).
{ apply sqcb_seed.
  - rewrite G2u. unfold SQB_FRAME. lia.
  - rewrite G2u. unfold SQB_FRAME. replace (sp0 - 32) with (sp0 + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
  - unfold sqcb_E. apply regs_ok_Eimg_Ereg.
  - rewrite G2u. exact HFRM. }
assert (EE : forall kk (rr : bv 5), Z.of_nat kk = bv_unsigned rr -> ew (sqcb_E regs1 regs) kk = getr regs1 rr)
  by (intros kk rr Hkk; exact (sqcb_E_reg regs1 regs kk rr Hkk)).
assert (HEI : img_env VAL A_LIM (sqcb_E regs1 regs)) by exact (sqcb_E_img regs1 regs).
set (E := sqcb_E regs1 regs) in *.
assert (SHOK : sh_ok SEGS (SLit 0) [] E (mrestrict (w_H W1) mem1)) by (unfold sh_ok; constructor).
(* 0x8bdcc .. 0x8bdd4: s1 := the slot, a1 := the argument, jal arg_s *)
paj_run_tok RUN HS HJ SHOK sqcb_Bspan.
{ lazymatch goal with |- awr_ok ?sg ?Bv ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?f0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg Bv Ex rs' stk spx fp b0 bc f0 lyx own) end.
  apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo]; lia|]. apply awr_ok_nil. }
pmkst HS. sqcb_md.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
lazymatch goal with HFx : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ => rename HFx into HFRB end.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFRB
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; lia|]); destruct Hin)) as KE.
assert (HRK : forall a, 0 <= a < 2 ^ 64 -> rdW W1 (ms_mem ms) a = rdW W1 mem1 a)
  by (intros a Ha; exact (KE a Ha (fun H => H))).
pose proof (proj1 HJ) as HARc.
assert (Q1 : getr (ms_regs ms) 1 = w64 (BASE + SQB_RETA)) by (rewrite P1; reflexivity).
assert (Q2 : getr (ms_regs ms) 2 = w64 (sp0 - SQB_FRAME)) by (rewrite P2, (EE 2%nat 2%bv eq_refl); exact G2).
assert (Q2s : spZ (ms_regs ms) = sp0 + -32)
  by (unfold spZ; rewrite Q2; unfold w64; rewrite unsigned_lit_small by (unfold SQB_FRAME; lia); unfold SQB_FRAME; lia).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl); exact G3).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl); exact G4).
assert (Q8 : getr (ms_regs ms) 8 = w64 pw) by (rewrite P8, (EE 8%nat 8%bv eq_refl); exact G8).
assert (Q9 : getr (ms_regs ms) 9 = w64 c) by (rewrite P9, (EE 10%nat 10%bv eq_refl); exact G10).
assert (Q10 : getr (ms_regs ms) 10 = w64 c) by (rewrite P10, (EE 10%nat 10%bv eq_refl); exact G10).
assert (Q11 : getr (ms_regs ms) 11 = w64 pw) by (rewrite P11, (EE 8%nat 8%bv eq_refl); exact G8).
assert (X18_27 : forall r, 18 <= r <= 27 -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite <- (G18 r Hr).
  assert (H10r : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct H10r as [-> | H10r]); [..| subst r];
  rewrite (st_ok_restrict_reg SEGS (w_H W1) E _ _ _ HS); cbn [ms_regs];
  lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ => let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
  cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
  lazymatch goal with |- ew _ ?m = getr _ (Z_to_bv 5 ?rr) => exact (EE m (Z_to_bv 5 rr) eq_refl) end. }
assert (HAROd : arodata_okP SEGS RLO RHI B (rdW W1 (ms_mem ms)))
  by exact (sqcb_aro B (ROB := ROB) cmd_ro_prog_apart _ ly S W mem md O ly1 S1 W1 (ms_mem ms) mdv [] _ sp0 HAR HOin HJ HROD).
assert (HROd : cmd_ro_ok (rdW W1 (ms_mem ms))) by exact (cmd_ro_ok_of_aro _ _ _ _ _ HARc HAROd).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev1 & _).
assert (HREP1m : rec_repA B ly1 S1 (rdW W1 (ms_mem ms)) (rec_record R SQB_FN []) O1).
{ pose proof (sqcb_rec_repA_in B _ _ _ _ _ HREP1) as HO11.
  apply (sqcb_rec_repA_ext B ly1 S1 (rdW W1 mem1) ly1 S1 _ _ _ HREP1 HO11).
  intros a [Ha | [Ha | (pn & Hpn & Ha)]]; apply HRK;
  [unfold A_G_REC, REC_SIZE in Ha; lia | unfold A_REC_SPILL, SC_SIZE in Ha; lia |].
  destruct pn as [b m]. cbn [fst snd] in Ha.
  destruct (sqcb_blk_bounds B ly1 S1 W1 mem1 md1 b m HAR1 (HO11 _ Hpn)) as (Hb & Hbc & _ & Hmr & _). lia. }
assert (Hxs1m : astr_atR (rdW W1 (ms_mem ms)) pw x).
{ apply (sqcb_str_keep (rdW W1 mem1)); [exact Hxs1|]. intros a Ha. apply HRK. unfold n in *. lia. }
assert (HXM0 : forall t, 0 <= XM_ANSWER MT t).
{ intros t. unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC, LIVE_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.max (Z.of_nat (length t) + 1) 1) ltac:(lia)). lia. }
assert (HXS0 : 0 <= XM_ARG_S MT which).
{ unfold XM_ARG_S, XM_XMALLOC, LIVE_XMALLOC. apply (mo_malloc_nonneg MT MTL). lia. }
assert (HLA0 : forall t, 0 <= LIVE_ANSWER t) by (intros t; unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC; lia).
(* the call of arg_s(c, which) (0x8bdd4) *)
rewrite (cmd_sig_prog_PB CS_arg_s ltac:(vm_compute; tauto)).
change (pa_val A_TEXT + cmd_af CS_arg_s) with (BASE + AF_arg_s).
assert (HAS : ARG_S_STK = 16464) by reflexivity.
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W1 (ms_regs ms) (ms_mem ms) _ SQB_STK sp0 (sqcb_FP O) ly S W mem md [] ly1 S1 _ _
    ARG_S_STK _ EV_ARG_S (-32) (w64 (BASE + SQB_RETA)) []
    (fun ly2 S2 W2 regs2 mem2 md2 =>
      blocks_bytes S2 <= blocks_bytes S1 + LIVE_ARG_S which /\ mo_le MT S1 S2 (XM_ARG_S MT which) /\
      exists p, 4096 <= p < 2 ^ 64 /\ Permutation (ablocks B ly2 S2) ((p, n) :: ablocks B ly1 S1) /\
      Forall (fun qk => iv_apart p n (fst qk) (snd qk)) (ablocks B ly1 S1) /\
      rec_repA B ly2 S2 (rdW W2 mem2) (rec_record R SQB_FN [x]) ((p, n) :: O1)) HJ Q2s).
  - reflexivity.
  - lia.
  - rewrite HAS. lia.
  - rewrite HAS, HST. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - unfold w64. apply sqcb_ret_ok. right; left; reflexivity.
  - unfold w64. rewrite sqcb_ret_val by (right; left; reflexivity). unfold SQB_RETA, AF_sup_quarantine_clear. lia.
  - apply achain_low. unfold s0Z. rewrite Q8. unfold w64. rewrite unsigned_lit_small by lia. unfold n in *. lia.
  - intros HPRE1. eapply SRr_mono.
    + apply (TARG_S fx ly1 S1 W1 (ms_regs ms) (ms_mem ms) _ [] c pw SQB_FN [] which R O1 HPRE1).
      * exact HAROd.
      * exact HROd.
      * exact Q10.
      * exact Q11.
      * reflexivity.
      * exact HREP1m.
      * left. rewrite Hwh. cbn [astr_argA]. split; [unfold n in *; lia|]. split; [exact Hxs1m|].
        split; [exact Hxl|]. left. split; [|constructor]. exists b0, m0. split; [exact Hin1 | unfold n in *; lia].
      * intros x0 Hx0. rewrite Hwh in Hx0. injection Hx0 as <-.
        apply (cmd_heap_tail_vis ly1 S1 W1 (ms_mem ms) mdv b0 m0 (pw + Z.of_nat (length x)) HARc Hin1). unfold n in *. lia.
      * rewrite Hk in Hnev1. unfold EV_SUP_QUARANTINE_CLEAR, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in *. lia.
      * unfold LIVE_SUP_QUARANTINE_CLEAR in HLIVE. pose proof (HLA0 (snd (sup_quarantine_clear_m R which))). lia.
      * apply (mok_station MT S S1 _ _ _ MTL HMOK MLE1 HXS0).
        unfold XM_SUP_QUARANTINE_CLEAR. pose proof (HXM0 (snd (sup_quarantine_clear_m R which))). lia.
    + cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2).
      exists ly2, S2, regs2, mem2, md2. split; [rewrite Q1; reflexivity|]. split; [exact HJ2|]. split; [exact HP2|].
      destruct HQ2 as (HBB & MLE & [(Hl & _) | (_ & pa & Hpa & Hperm & Hfresh & Hrep)]); [cbn in Hl; discriminate Hl|].
      split; [exact HBB|]. split; [exact MLE|]. exists pa.
      rewrite Hwh in Hrep, Hperm, Hfresh. cbn [sarg app] in Hrep, Hperm, Hfresh.
      split; [exact Hpa|]. split; [exact Hperm|]. split; [exact Hfresh | exact Hrep].
  - intros a Ha.
    apply inFP_cons in Ha as [Ha | Ha]; [|apply inFP_cons in Ha as [Ha | Ha]; [|exfalso; exact (inFP_nil a Ha)]].
    all: assert (HPa : inFP cmd_PG a /\ inFP (sqcb_FP []) a)
      by (apply (sqcb_PG_slot R a Hn16); unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; cbn [length] in *; lia).
    all: apply (sqcb_awr_prog B HB cmd_prog_img); [exact (proj1 HPa) | exact (sqcb_FP_O O a (proj2 HPa))].
  - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso.
    cbn [length Z.of_nat] in Ha.
    apply inFP_cons in Ha as [Ha | Ha]; [|apply inFP_cons in Ha as [Ha | Ha]; [|exact (inFP_nil a Ha)]];
    unfold CALL_OFF_NARGS, CALL_OFF_ARGS, A_G_REC, A_REC_SPILL, OFF_CALLS in *; cbn [length] in *; rewrite HST in Hw; lia. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc2 & HP2 &
  (HBB2 & MLE2 & p & Hp4096 & HPERM2 & HFR2 & HREP2)).
assert (CS2 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr (ms_regs ms) rr)
  by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx).
assert (R2 : getr regs2 2 = w64 (sp0 - SQB_FRAME))
  by (rewrite (CS2 2%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact Q2).
assert (R3 : getr regs2 3 = w64 (as_gp B))
  by (rewrite (CS2 3%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact Q3).
assert (R4 : getr regs2 4 = w64 (as_tp B))
  by (rewrite (CS2 4%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact Q4).
assert (R9 : getr regs2 9 = w64 (rec_slot R))
  by (rewrite (CS2 9%bv) by (unfold acallee_saved; rewrite bv_unsigned_BV; lia); exact Q9).
assert (R18 : forall r, 18 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite (HP2 r ltac:(unfold acallee_saved; lia)). exact (X18_27 r Hr). }
(* the frame survives arg_s, whose footprint is the slot's nargs and args[0] *)
assert (HFP2low : forall b, inFP (if Z.of_nat (length (@nil (list byte))) <? REC_ARGS_MAX
    then [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4);
          (c + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))),
           c + CALL_OFF_ARGS + 8 * Z.of_nat (length (@nil (list byte))) + 8)] else []) b -> b < alloc_ceiling).
{ intros b Hb. destruct (Z.of_nat (length (@nil (list byte))) <? REC_ARGS_MAX); [|exfalso; exact (inFP_nil b Hb)].
  apply inFP_cons in Hb as [Hb | Hb]; [|apply inFP_cons in Hb as [Hb | Hb]; [|exfalso; exact (inFP_nil b Hb)]];
  unfold CALL_OFF_NARGS, CALL_OFF_ARGS, A_G_REC, A_REC_SPILL, OFF_CALLS in *; cbn [length] in *; lia. }
assert (HFRM2 : sqcb_frame_at (mrestrict (w_H W2) mem2) (sp0 - SQB_FRAME) regs).
{ apply (sqcb_frame_kept W1 W2 mem1 mem2 _ regs HFRM). intros a Ha. unfold SQB_FRAME in Ha.
  rewrite <- (HRK a ltac:(lia)).
  apply (sqcb_keep_stack B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc2); [exact HFP2low | lia | rewrite HAS; lia]. }
apply (sqcb_S2 ly S W regs mem md ch pw which R O x (ablocks B ly1 S1) F O1 p ly2 S2 W2 regs2 mem2 md2
  (k1 + EV_ARG_S) PRE Hwh HJ2 ltac:(rewrite Hk; reflexivity) HFRM2 R2 R3 R4 R9 R18 HREP2 HPERM HFO HO1 HPERM2 HFR2
  (mle_station MT S S1 S2 _ _ MTL MLE1 MLE2) ltac:(lia)).
Qed.

End e.
End f.
End d.

Print Assumptions sqcb_S2.
Print Assumptions sqcb_S1.
