(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of descriptors_panel_get (plugin-hostd/fuzz_command.asan-ubsan, 0x8ccfc, 22 instructions), re-made at B's addresses from the ASan walk lib/A/Prog/descriptors_panel_get.v and its segment _s7.v (a working branch 2db68b2223b): the prologue, the call of record (B's function where A inlined it) composed with its contract, and the moves to the call of arg_s; then the segments of descriptors_panel_get_a.v and descriptors_panel_get_r.v. *)

(* descriptors_panel_get (recorder.c:554-560) on B, 0x8ccfc: the prologue stores ra, s0, s1 in a 32-byte frame,
   s0 := uri, record(24) takes the slot (g_rec.calls[n], or record.spill after freeing the spill's arguments),
   s1 := the slot, a1 := uri, arg_s records the copy of uri, rec_shape_of finds the shape of "panel_get", the
   epilogue restores the frame and `j answer` tail-jumps into answer. The function has no branch, no inline ASan
   check (no `jal __asan_report_*`) and no UBSan trap site: the measured image (capstone over fuzz_command.asan-ubsan,
   sha256 658cefbe...) has 22 instructions at 0x8ccfc .. 0x8cd50, the calls record 0x8a728 (0x8cd14), arg_s 0x8a820
   (0x8cd20), rec_shape_of 0x896d4 (0x8cd30) and the tail jump to answer 0x8aa10 (0x8cd50), so no report edge needs
   refuting here; the callees' edges are their contracts'. The segments:
   - this file, dpgb_entry: the entry to the call of arg_s;
   - descriptors_panel_get_a.v, dpgb_A_of_R: arg_s to the call of rec_shape_of;
   - descriptors_panel_get_r.v, dpgb_R_holds: rec_shape_of, the epilogue and the tail jump into answer. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q YG0d_tail.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c rec_calls_free_c record_c arg_s_c rec_shape_of_c hand_back_c mix_call_c answer_c descriptors_panel_get_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecRo CmdRecRest CmdRecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import descriptors_panel_get_aux.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
descriptors_panel_get_a descriptors_panel_get_r.

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
(* the statement's hypotheses (descriptors_panel_get_c.v:70-75) *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the per-binary facts the statement does not carry: the allocator record, the meter laws, and a Theorem Labs lane's record facts
   (lib/B/Prog/CmdRec*.v) that are proved only for the pinned instance, stated for the abstract one *)
Hypothesis HB : CmdBSyms B.
(* a Theorem Labs lane's CmdRecRest.v `cmd_sig_prog_PB`, stated for the abstract instance *)
Hypothesis cmd_sig_prog_PB : cmd_sig_prog (PI := PI).
Hypothesis MTL : ameter_laws MT.
(* a Theorem Labs lane's CmdRecImg.v `cmd_img_facts_tfib`, stated for the abstract instance's segments *)
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> cmd_img_facts SEGS B0.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : cmd_img_facts SEGS B := cmd_img_facts_tfib B HB.
(* a Theorem Labs lane's record facts over any segments (lib/B/Prog/CmdRecRo.v, CmdRecRest.v), at this walk's *)
Let CMD_RO_IN : cmd_ro_in (in_roP SEGS RLO RHI) := CmdRecRo.CMD_RO_IN SEGS B LAWS HB IMG.
Let cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img SEGS B LAWS HB IMG.
Let cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC :=
  CmdRecRest.cmd_ro_prog_apart SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) := CmdRecRo.cmd_ro_ok_of_aro SEGS B LAWS HB IMG.
Let RUN := paj_run B LAWS.

Lemma dpgb_entry : dpgb_A_stmt B MT ->
forall ly S W regs mem md ch pu x R O,
dpgb_ctx B MT ly S W regs mem md ch pu x R O ->
SRr SEGS W (cfg_at SEGS (BASE + AF_descriptors_panel_get) regs mem md)
  (dpgb_post B MT ly S W regs mem md R (Some x) O).
Proof.
intros HA ly S W regs mem md ch pu x R O CTX.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof CTX as (HPRE & Hfrm & HROD & HRO & H10 & Hpu & HBLK0 & HSTR0 & HLEN & HAPO & HREP & Hfr8 & Hev & Hlive & MOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HREP as (Q & HQ & HQO).
pose proof HQ as (_ & _ & _ & (HL16 & _) & _).
destruct (dpgb_slot_ok R HL16) as (Hc1 & Hc2 & Hc8 & Hc3).
assert (Hc3' : (rec_slot R + CALL_SIZE <= A_G_REC + REC_SIZE) \/ rec_slot R = A_REC_SPILL)
  by (destruct Hc3 as [[H _] | H]; [left | right]; exact H).
clear Hc3.
assert (HOin : forall pn, In pn O -> In pn (ablocks B ly S)) by exact (dpgb_rec_repA_in B ly S (rdW W mem) R O HREP).
assert (HSTKr : RECORD_STK + 32 <= DESCRIPTORS_PANEL_GET_STK) by (unfold DESCRIPTORS_PANEL_GET_STK; lia).
assert (HSTKp : 0 <= RECORD_STK) by (unfold RECORD_STK, REC_CALLS_FREE_STK, ASTACK; lia).
assert (Hsp46 : 2 ^ 46 <= spZ regs <= 2 ^ 47).
{ change (2 ^ 46) with 70368744177664. change (2 ^ 47) with 140737488355328.
  clear - Hceil Hslo Hshi H47 Hstk0 HSTKr HSTKp C1. lia. }
pose proof HBLK0 as (qb & kb & Hqb & Hqb1 & Hqb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ qb kb HAR Hqb) as (_ & Hqb4096 & Hqbc & _ & _ & _ & Hkb).
pose proof (dpgb_req_ge kb ltac:(lia)) as [_ Rkb].
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
assert (EEo : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew (Eimg (Ereg regs [])) nn = getr regs rr).
{ intros nn rr Hnn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hnn. }
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs [])) 2) = spZ regs) by (rewrite (EEo 2%nat 2%bv eq_refl); reflexivity).
pose proof (ajournal_init SEGS B DESCRIPTORS_PANEL_GET_STK (dpgb_FP O) ly S W regs mem md ch HPRE) as HJ.
destruct (dpgb_entry_seed W mem regs (SLit 0) Hsp46 Hal16
  ltac:(intros a Ha; apply Hpres; unfold DPGB_FRAME in Ha; lia)) as [HS SHOK].
set (E := Eimg (Ereg regs [])) in *.
unfold cfg_at, w64.
(* 0x8ccfc .. 0x8cd14: the prologue, s0 := uri, a0 := 24, then record *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack with (n := 2%nat).
  - reflexivity.
  - exact Usp.
  - cbn [YP09.r_wlo]. lia.
  - cbn [YP09.r_whi]. lia.
  - apply awr_ok_nil. }
rewrite ?wvb_collapse in HJ.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 32 <= a < spZ regs) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin];
      [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]);
    exfalso; exact Hin)) as UN.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
lazymatch type of HS with
| st_ok_pi _ _ ?Ex ?SSX (restrict _ ?MSX) =>
  assert (KRc : forall r : bv 5, sr_get (ss_regs SSX) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs MSX) r = getr regs r)
    by (intros r Hr; rewrite (st_ok_pi_restrict_reg (w_H W) Ex SSX MSX r HS), Hr; cbn [sv_denot];
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
        pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        apply EEo; lia);
  let r0 := eval vm_compute in (nth 0 (ss_mem SSX) (stack_region 0)) in
  pose proof (st_ok_pi_region_nth Ex SSX (restrict (w_H W) MSX) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0
| st_ok _ ?Ex ?SSX (restrict _ ?MSX) =>
  assert (KRc : forall r : bv 5, sr_get (ss_regs SSX) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs MSX) r = getr regs r)
    by (intros r Hr; rewrite (st_ok_restrict_reg SEGS (w_H W) Ex SSX MSX r HS), Hr; cbn [sv_denot];
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
        pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        apply EEo; lia);
  let r0 := eval vm_compute in (nth 0 (ss_mem SSX) (stack_region 0)) in
  pose proof (st_ok_region_nth Ex SSX (restrict (w_H W) MSX) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0
end.
cbn [ms_mem restrict mkst] in HR0.
pose proof (dpgb_frame_of_region _ _ (spZ regs) regs _ HR0 Usp EEo
  ltac:(intros j r Hj; unfold dpgb_saved in Hj;
        do 3 (destruct j as [|j]; [cbn in Hj; injection Hj as <-; cbn; tauto|]);
        destruct j; cbn in Hj; discriminate Hj)) as HFRM.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  set (regsx := rg) in *; set (memx := mm) in * end.
assert (Rsp : spZ regsx = spZ regs + -32).
{ unfold spZ at 1. rewrite P2, Usp.
  rewrite (unsigned_lit_small (spZ regs + -32)) by lia. reflexivity. }
assert (R1 : getr regsx 1 = Z_to_bv 64 (BASE + DPGB_RET_REC))
  by (rewrite P1; unfold DPGB_RET_REC, AF_descriptors_panel_get; reflexivity).
assert (R3 : getr regsx 3 = w64 (as_gp B)) by (rewrite P3, (EEo 3%nat 3%bv eq_refl); exact Hgp).
assert (R4 : getr regsx 4 = w64 (as_tp B)) by (rewrite P4, (EEo 4%nat 4%bv eq_refl); exact Htp).
assert (R8 : getr regsx 8 = w64 pu) by (rewrite P8, (EEo 10%nat 10%bv eq_refl); exact H10).
assert (R10 : getr regsx 10 = w64 REC_DESCRIPTORS_PANEL_GET) by (rewrite P10; reflexivity).
(* the recorder and the read-only bytes at the call: the run wrote only the frame, above the allocator's ceiling *)
assert (KEEPA : forall a, 0 <= a < alloc_ceiling -> rdW W memx a = rdW W mem a).
{ intros a Ha. apply UN; [lia|]. lia. }
assert (HREPx : rec_repA B ly S (rdW W memx) R O) by exact (dpgb_rep_low B ly S W mem md (rdW W memx) R O HAR HREP KEEPA).
assert (HRODx : arodata_okP SEGS RLO RHI B (rdW W memx))
  by exact (dpgb_rodata_kept B cmd_ro_prog_apart _ _ ly S W mem md O [] ly S W memx mdv 0 HAR HOin HJ HROD).
assert (HEV1 : st_nev S + EV_RECORD R <= EV_MAX)
  by (unfold EV_DESCRIPTORS_PANEL_GET, EV_ARG_S, EV_ANSWER, EV_HAND_BACK, EV_XMALLOC in Hev; lia).
assert (HXMs : 0 <= XM_ARG_S MT (Some x))
  by (unfold XM_ARG_S, XM_XMALLOC; apply (mo_malloc_nonneg MT MTL); unfold LIVE_XMALLOC; lia).
assert (HXMa : 0 <= XM_ANSWER MT (snd (descriptors_panel_get_m R (Some x)))).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (LIVE_XMALLOC (Z.of_nat (length (snd (descriptors_panel_get_m R (Some x)))) + 1))
    ltac:(unfold LIVE_XMALLOC; lia)). lia. }
assert (HMOK1 : mo_ok MT S (XM_RECORD MT R)).
{ apply (mo_ok_le MT MTL S (XM_RECORD MT R) (XM_DESCRIPTORS_PANEL_GET MT R (Some x)) MOK).
  unfold XM_DESCRIPTORS_PANEL_GET. lia. }
(* the footprint of the call of record lies below the allocator's ceiling *)
assert (HrFP : forall a, inFP ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
    (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O)) a ->
  ((A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
   (inFP (dpgb_FP O) a /\ exists b m, In (b, m) O /\ b <= a < b + req_size m))).
{ intros a (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
  - left. left. unfold A_G_REC, OFF_NCALLS, REC_SIZE in *. lia.
  - left. apply (dpgb_slot_PG (rec_slot R)); [exact Hc1 | exact Hc2 | exact Hc3' | lia].
  - right. destruct (Nat.ltb (length (r_calls R)) 16); [destruct Hr|].
    assert (Hb : exists b m, In (b, m) O /\ b <= a < b + req_size m)
      by (apply inFP_ablocks_fp_inv; exists r; split; [exact Hr | exact Ha]).
    destruct Hb as (b & m & Hbm & Hr2). split; [|exists b, m; split; [exact Hbm | exact Hr2]].
    replace a with (b + (a - b)) by lia. apply (dpgb_inFP_blk O b m (a - b) Hbm). lia. }
assert (HrFP' : forall a, ((A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
   (inFP (dpgb_FP O) a /\ exists b m, In (b, m) O /\ b <= a < b + req_size m)) -> a < alloc_ceiling).
{ intros a [[Ha | Ha] | (_ & b & m & Hbm & Ha)].
  - unfold A_G_REC, REC_SIZE in Ha. lia.
  - unfold A_REC_SPILL, SC_SIZE in Ha. lia.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR (HOin _ Hbm)) as (_ & _ & Hbc & _). lia. }
(* the call of record(24) *)
rewrite (rca_sig_record cmd_sig_prog_PB).
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS W regsx memx _ DESCRIPTORS_PANEL_GET_STK (spZ regs) (dpgb_FP O) ly S W mem md [] ly S mdv 0
    RECORD_STK
    ((A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4) :: (rec_slot R, rec_slot R + 8) ::
     (if Nat.ltb (length (r_calls R)) 16 then [] else ablocks_fp O))
    (EV_RECORD R) (-32) (Z_to_bv 64 (BASE + DPGB_RET_REC)) []
    (fun ly' S' W' regs' mem' md' => exists (F O' : list (Z * Z)),
       getr regs' 10 = w64 (rec_slot R) /\
       Permutation (ablocks B ly S) (ablocks B ly' S' ++ F) /\
       Z.of_nat (length F) = rec_spill_frees R /\
       (forall pn, In pn F -> In pn O) /\
       rec_repA B ly' S' (rdW W' mem') (rec_record R REC_DESCRIPTORS_PANEL_GET []) O' /\
       (forall pn, In pn O' <-> In pn O /\ ~ In pn F) /\
       blocks_bytes S' <= blocks_bytes S /\
       mo_le MT S S' (XM_RECORD MT R))
    HJ Rsp).
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - apply ret_ok_codeptr_v; [unfold DPGB_RET_REC, AF_descriptors_panel_get; lia | reflexivity].
  - rewrite unsigned_lit_small by (unfold DPGB_RET_REC, AF_descriptors_panel_get; lia).
    unfold DPGB_RET_REC, AF_descriptors_panel_get. lia.
  - apply achain_low. unfold s0Z. rewrite R8, unsigned_lit_small by lia. lia.
  - intros HPREx. eapply SRr_mono.
    + exact (TRECORD fx ly S W regsx memx mdv [] REC_DESCRIPTORS_PANEL_GET R O HPREx HRODx R10
        ltac:(unfold REC_DESCRIPTORS_PANEL_GET, REC_FN_COUNT; lia) HREPx HEV1 HMOK1).
    + cbv beta. unfold apost_base. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK).
      exists ly3, S3, regs3, mem3, md3. split; [rewrite R1; reflexivity|]. split; [exact HJ1|]. split; [exact HP | exact HK].
  - (* record writes g_rec.ncalls, the slot's fn and nargs, and in the spill arm the spill's argument blocks *)
    intros a Ha. destruct (HrFP a Ha) as [Hg | (HfA & b & m & Hbm & Hr)].
    + apply (dpgb_awr_slot B HB cmd_prog_img). exact Hg.
    + right; left. split; [exact HfA|]. exists b, m. split; [exact (HOin _ Hbm) | exact Hr].
  - (* none of them is in this call's stack window *)
    intros ly5 S5 W5 regs5 mem5 md5 _ a Ha Hw _. exfalso.
    pose proof (HrFP' a (HrFP a Ha)). lia. }
cbv beta. intros W1 c1 Hwle1 (ly1 & S1 & regs1 & mem1 & md1 & -> & HJ1 & HJi & HP1 & HK1).
destruct HK1 as (F & O1 & R10' & HPermF & HlenF & HFO & HREP1 & HO1 & HBB1 & HMLE1).
rewrite Z.add_0_l in HJ1.
pose proof (proj1 HJi) as HAR1.
(* back at 0x8cd18: the registers record keeps, the frame *)
assert (CS1 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs1 rr = getr regsx rr)
  by (intros rr Hr; pose proof (HP1 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx).
assert (X2 : getr regs1 2 = getr regsx 2) by (apply CS1; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (X3 : getr regs1 3 = getr regsx 3) by (apply CS1; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (X4 : getr regs1 4 = getr regsx 4) by (apply CS1; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
assert (X8 : getr regs1 8 = getr regsx 8) by (apply CS1; unfold acallee_saved; rewrite bv_unsigned_BV; lia).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & GX1 & _).
assert (HFR1 : forall j r, nth_error dpgb_saved j = Some r ->
  aval_mem (rdW W1 mem1) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros j r Hj. assert (Hj3 : (j < 3)%nat) by (apply (proj1 (nth_error_Some dpgb_saved j)); rewrite Hj; discriminate).
  apply (dpgb_aval_mem_kept (rdW W memx)); [apply dpgb_aval_mem; exact (HFRM j r Hj)|].
  intros kk Hkk. apply GX1; [lia | lia |].
  intros Hf. pose proof (HrFP' _ (HrFP _ Hf)). lia. }
(* 0x8cd18 .. 0x8cd20: s1 := the slot, a1 := uri, then arg_s *)
destruct (dpgb_reg_seed W1 regs1 mem1 DPGB_RET_REC (SLit 0)) as [HS2 SHOK2].
assert (HEI1 : img_env VAL A_LIM (Eimg (Ereg regs1 []))) by apply Eimg_env.
assert (EE1 : forall nn (rr : bv 5), Z.of_nat nn = bv_unsigned rr -> ew (Eimg (Ereg regs1 [])) nn = getr regs1 rr).
{ intros nn rr Hnn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hnn. }
set (E1 := Eimg (Ereg regs1 [])) in *.
paj_run_tok RUN HS2 HJ1 SHOK2 Bspan.
{ apply awr_ok_nil. }
rewrite ?wvb_collapse in HJ1.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdw := mdx) in *; clearbody mdw end.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ : Z => False) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin; exfalso; exact Hin)) as UN2.
pmkst HS2.
lazymatch type of HS2 with
| st_ok_pi _ _ ?Ex ?SSX (restrict _ ?MSX) =>
  assert (KR2 : forall r : bv 5, sr_get (ss_regs SSX) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs MSX) r = getr regs1 r)
    by (intros r Hr; rewrite (st_ok_pi_restrict_reg (w_H W1) Ex SSX MSX r HS2), Hr; cbn [sv_denot];
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
        pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        apply EE1; lia)
| st_ok _ ?Ex ?SSX (restrict _ ?MSX) =>
  assert (KR2 : forall r : bv 5, sr_get (ss_regs SSX) r = SOff (Z.to_nat (bv_unsigned r)) 0 ->
      getr (ms_regs MSX) r = getr regs1 r)
    by (intros r Hr; rewrite (st_ok_restrict_reg SEGS (w_H W1) Ex SSX MSX r HS2), Hr; cbn [sv_denot];
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
        pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        apply EE1; lia)
end.
prreg HS2 (1%bv : bv 5) Q1. prreg HS2 (9%bv : bv 5) Q9. prreg HS2 (11%bv : bv 5) Q11.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
  set (regsJ := rg) in *; set (memJ := mm) in * end.
assert (HKTJ : forall a, 0 <= a < 2 ^ 64 -> rdW W1 memJ a = rdW W1 mem1 a)
  by (intros a Ha; exact (UN2 a Ha (fun z => z))).
assert (Z2 : getr regsJ 2 = getr regs1 2) by (apply KR2; vm_compute; reflexivity).
assert (Z3 : getr regsJ 3 = getr regs1 3) by (apply KR2; vm_compute; reflexivity).
assert (Z4 : getr regsJ 4 = getr regs1 4) by (apply KR2; vm_compute; reflexivity).
assert (Z8 : getr regsJ 8 = getr regs1 8) by (apply KR2; vm_compute; reflexivity).
assert (Z10 : getr regsJ 10 = getr regs1 10) by (apply KR2; vm_compute; reflexivity).
assert (HspJ : spZ regsJ = spZ regs - DPGB_FRAME).
{ unfold spZ at 1. rewrite Z2, X2. change (bv_unsigned (getr regsx 2%bv)) with (spZ regsx). rewrite Rsp.
  unfold DPGB_FRAME. clear - regs. lia. }
assert (R1J : getr regsJ 1 = Z_to_bv 64 (BASE + DPGB_RET_ARG))
  by (rewrite Q1; unfold DPGB_RET_ARG, AF_descriptors_panel_get; reflexivity).
assert (R3J : getr regsJ 3 = w64 (as_gp B)) by (rewrite Z3, X3; exact R3).
assert (R4J : getr regsJ 4 = w64 (as_tp B)) by (rewrite Z4, X4; exact R4).
assert (R8J : getr regsJ 8 = w64 pu) by (rewrite Z8, X8; exact R8).
assert (R9J : getr regsJ 9 = w64 (rec_slot R)) by (rewrite Q9, (EE1 10%nat 10%bv eq_refl); exact R10').
assert (R10J : getr regsJ 10 = w64 (rec_slot R)) by (rewrite Z10; exact R10').
assert (R11J : getr regsJ 11 = w64 pu) by (rewrite Q11, (EE1 8%nat 8%bv eq_refl), X8; exact R8).
assert (RhiJ : forall r, 18 <= r <= 27 -> getr regsJ (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr.
  assert (Hrr : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  transitivity (getr regs1 (Z_to_bv 5 r)).
  - repeat (destruct Hrr as [-> | Hrr]; [apply KR2; vm_compute; reflexivity|]). subst r. apply KR2. vm_compute. reflexivity.
  - rewrite (HP1 r ltac:(unfold acallee_saved; lia)).
    repeat (destruct Hrr as [-> | Hrr]; [apply KRc; vm_compute; reflexivity|]). subst r. apply KRc. vm_compute. reflexivity. }
assert (HFRJ : forall j r, nth_error dpgb_saved j = Some r ->
  aval_mem (rdW W1 memJ) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros j r Hj. assert (Hj3 : (j < 3)%nat) by (apply (proj1 (nth_error_Some dpgb_saved j)); rewrite Hj; discriminate).
  apply (dpgb_aval_mem_kept (rdW W1 mem1)); [exact (HFR1 j r Hj)|].
  intros kk Hkk. apply HKTJ. lia. }
(* the blocks after record, the recorder, the string argument *)
assert (BLK : dpgb_blk B ly S O ly1 S1 O1) by exact (dpgb_blk_of_record B ly S W mem md O ly1 S1 F O1 HAR HPermF HFO HO1).
assert (HKeep : forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B ly1 S1)).
{ intros pn Hin Hno. apply (Permutation_in pn HPermF) in Hin. apply in_app_or in Hin as [H | H]; [exact H|].
  exfalso. exact (Hno (HFO pn H)). }
destruct (dpgb_blk_kept B cmd_prog_img DESCRIPTORS_PANEL_GET_STK (spZ regs) ly S W mem md O [] ly1 S1 W1 memJ mdw
  (EV_RECORD R) pu (Z.of_nat (length x) + 1) HAR HJ1 HOin HKeep ltac:(lia) HBLK0 HAPO) as [HBLK1 HKB1].
assert (HSTR1 : astr_atR (rdW W1 memJ) pu x) by exact (dpgb_rastr_kept (rdW W mem) (rdW W1 memJ) pu x HSTR0 HKB1).
assert (HREPJ : rec_repA B ly1 S1 (rdW W1 memJ) (rec_record R REC_DESCRIPTORS_PANEL_GET []) O1)
  by exact (dpgb_rep_low B ly1 S1 W1 mem1 md1 (rdW W1 memJ) _ _ HAR1 HREP1 (fun a Ha => HKTJ a ltac:(lia))).
exact (HA ly S W regs mem md ch pu x R O CTX ly1 S1 W1 regsJ memJ mdw O1 BLK HJ1 HMLE1 HBB1 HREPJ
  HspJ R3J R4J R1J R8J R9J R10J R11J RhiJ HFRJ HBLK1 HSTR1).
Qed.

Theorem tdescriptors_panel_get_holds : tdescriptors_panel_get_spec B MT.
Proof.
assert (HR : dpgb_R_stmt B MT) by (apply dpgb_R_holds; assumption).
assert (HA : dpgb_A_stmt B MT) by (apply dpgb_A_of_R; assumption).
assert (HE : forall ly S W regs mem md ch pu x R O, dpgb_ctx B MT ly S W regs mem md ch pu x R O ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_descriptors_panel_get) regs mem md)
    (dpgb_post B MT ly S W regs mem md R (Some x) O))
  by (apply dpgb_entry; assumption).
intros ly S W regs mem md ch pu uri R O HPRE Hfrm HROD HRO H10 Hpu (x & -> & HB0 & HS0 & HL & HF) HREP Hfr Hev Hlive
  MOK.
pose (CTX := conj HPRE (conj Hfrm (conj HROD (conj HRO (conj H10 (conj Hpu (conj HB0 (conj HS0 (conj HL
  (conj HF (conj HREP (conj Hfr (conj Hev (conj Hlive MOK))))))))))))) : dpgb_ctx B MT ly S W regs mem md ch pu x R O).
exact (HE ly S W regs mem md ch pu x R O CTX).
Qed.

End e.
End f.
End d.
