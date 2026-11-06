(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the last segment of record's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan): from the meet of record()'s two arms (0x8a7ac) to the return (0x8a7f8) and the
   statement's post, after A's spa_meet (lib/A/Prog/sup_pin_accept_s4.v, a working branch 3cc8391594b), which
   continued into the inlined arg_s; B returns, so the segment ends at `ret` with paj_ret_at. The run decides the
   UBSan alignment trap 0x8a7b0 by the slot atom's alignment fact (rcb_facts, from rcb_rec_slot_ok) and both inline
   checks (0x8a7c0 and 0x8a7d8, whose report calls are 0x8a80c and 0x8a81c) by the slot's shadow entry (record_s0.v
   rcb_shok); neither report path is stepped. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_aux record_s0.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecCells CmdRecRest CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_calls_free_c record_c CmdRecAns.
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
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the post of the statement (record_c.v:107-119) *)
Definition rcb_post (B : asyms) (MT : ameter_ops) (R : rstate) (fn : Z) (O : list (Z * Z)) ly S
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (F O' : list (Z * Z)),
 getr regs' 10 = w64 (rec_slot R) /\
 Permutation (ablocks B ly S) (ablocks B ly' S' ++ F) /\
 Z.of_nat (length F) = rec_spill_frees R /\
 (forall pn, In pn F -> In pn O) /\
 rec_repA B ly' S' (rdW W' mem') (rec_record R fn []) O' /\
 (forall pn, In pn O' <-> In pn O /\ ~ In pn F) /\
 blocks_bytes S' <= blocks_bytes S /\
 mo_le MT S S' (XM_RECORD MT R).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HB : CmdBSyms B.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img (SK := SK) SEGS B LAWS HB IMG.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

(* a byte of the slot record() returns is one the footprint names: a Theorem Labs lane's program-static disjunct of awr_byte *)
Lemma rcb_awr_slot : forall STK sp0 R O bl0 blc fr0 ly own a, (length (r_calls R) <= 16)%nat ->
rec_slot R <= a < rec_slot R + 8 -> awr_byte SEGS B STK sp0 (rca_recFP R O) bl0 blc fr0 ly own a.
Proof.
intros STK sp0 R O bl0 blc fr0 ly own a HL Ha.
assert (HP : Exists (in_zr a) TFIB_PROG_STATIC)
  by (apply (rcb_in_PG (rec_slot R)); [exact (rcb_rec_slot_ok R HL) | unfold CALL_SIZE; lia]).
right; right; right; right; left. split; [|split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)]].
exists (rec_slot R, rec_slot R + 8). split; [right; left; reflexivity | cbn [fst snd]; exact Ha].
Qed.

(* g_rec.ncalls: the first range of the footprint *)
Lemma rcb_awr_ncalls : forall STK sp0 R O bl0 blc fr0 ly own a,
A_G_REC + OFF_NCALLS <= a < A_G_REC + OFF_NCALLS + 4 -> awr_byte SEGS B STK sp0 (rca_recFP R O) bl0 blc fr0 ly own a.
Proof.
intros STK sp0 R O bl0 blc fr0 ly own a Ha.
assert (HP : Exists (in_zr a) TFIB_PROG_STATIC) by (apply rcb_grec_in; unfold OFF_NCALLS, REC_SIZE in *; lia).
right; right; right; right; left. split; [|split; [rewrite (ts_prog B HB); exact HP | exact (cmd_prog_img a HP)]].
exists (A_G_REC + OFF_NCALLS, A_G_REC + OFF_NCALLS + 4). split; [left; reflexivity | cbn [fst snd]; exact Ha].
Qed.

(* --- from the meet of record()'s two arms (0x8a7ac) to the return ----------------------------------------- *)
(* 0x8a7ac .. 0x8a7f8: `andi a0,s1,7; bnez a0` (the UBSan alignment trap 0x8a7b0, decided by the slot atom's
   alignment fact), the shadow check of c->fn (0x8a7b4 .. 0x8a7c0, its report path 0x8a800 decided by the slot's
   shadow entry rcb_shok), `sw s0,0(s1)`, the shadow check of c->nargs (0x8a7c8 .. 0x8a7d8, report path 0x8a810
   decided the same way), `sw zero,4(s1)`, a0 := s1, the frame's four words back, sp += 32, ret. *)
Lemma rcb_meet : forall ly S W regs mem md ch fn R O lyc Sc Wc (regs1 : bvmap 5 word) memc mdc k O1 F,
afn_pre SEGS B RECORD_STK ly S W regs mem md ch ->
ajournal SEGS B RECORD_STK (spZ regs) (rca_recFP R O) ly S W mem md [] lyc Sc Wc memc mdc k ->
k <= EV_RECORD R ->
Permutation (ablocks B ly S) (ablocks B lyc Sc ++ F) -> Z.of_nat (length F) = rec_spill_frees R ->
(forall pn, In pn F -> In pn O) -> (forall pn, In pn O1 <-> In pn O /\ ~ In pn F) ->
blocks_bytes Sc <= blocks_bytes S -> mo_le MT S Sc (XM_RECORD MT R) ->
(length (r_calls R) <= 16)%nat -> 0 <= fn < REC_FN_COUNT ->
spZ regs1 = spZ regs - RCB_FRAME ->
getr regs1 9 = w64 (rec_slot R) -> getr regs1 8 = w64 fn -> getr regs1 18 = w64 SB ->
getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
(forall r, 19 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall j r, nth_error rcb_saved j = Some r ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
(forall rd', (forall a, 0 <= a < 2 ^ 64 -> ~ (rec_slot R <= a < rec_slot R + 8) -> rd' a = rdW Wc memc a) ->
   aval_mem rd' (rec_slot R + CALL_OFF_FN) 4 fn -> aval_mem rd' (rec_slot R + CALL_OFF_NARGS) 4 0 ->
   rec_repA B lyc Sc rd' (rec_record R fn []) O1) ->
SRr SEGS Wc (cfg_at SEGS (BASE + RCB_MEET) regs1 memc mdc)
  (apost_base SEGS B RECORD_STK (rca_recFP R O) regs ly S W mem md (EV_RECORD R) (rcb_post B MT R fn O ly S)).
Proof.
intros ly S W regs mem md ch fn R O lyc Sc Wc regs1 memc mdc k O1 F
  HPRE HJ Hk HPERM HFlen HFO HO1 HBB HMLE HL Hfn Rsp R9 R8 R18 R3 R4 Rhi HFR HPEND.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : RECORD_STK = 16560) by (vm_compute; reflexivity).
set (sp0 := spZ regs) in *.
set (c := rec_slot R) in *.
assert (Hok : rcb_slot_ok c) by exact (rcb_rec_slot_ok R HL).
destruct (rcb_slot_bounds c Hok) as (Hcb & Hc8 & Hce).
assert (Hcr : 0x5e32d0 <= c <= 0x5e3760 /\ c + 56 <= 0x5e3798)
  by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, CALL_SIZE, SC_SIZE in Hcb, Hce; lia).
assert (Hsp46 : 2 ^ 46 <= sp0 - RCB_FRAME) by (unfold RCB_FRAME; rewrite WS in Hslo; lia).
pose proof (proj1 HJ) as HARc.
destruct (rcb_meet_seed B HB PRW lyc Sc Wc memc mdc regs regs1 c sp0 HARc Hsp46 ltac:(lia) Hal16 Hok Rsp R9 R18 HFR)
  as [HS SHOK].
set (E := rcb_EM regs1 regs c) in HS, SHOK.
assert (HEI : img_env VAL A_LIM E) by (unfold E, rcb_EM; apply Eimg_env).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r).
{ intros nn r Hnn. unfold E, rcb_EM. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hnn. }
assert (EX : forall j, (j < 6)%nat -> ew E (32 + j) = nth j (rcb_extra regs c) (Z_to_bv 64 0)).
{ intros j Hj. unfold E, rcb_EM. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (EC : ew E 33 = Z_to_bv 64 c) by (exact (EX 1%nat ltac:(lia))).
assert (ERA : ew E 34 = getr regs (Z_to_bv 5 1)) by (exact (EX 2%nat ltac:(lia))).
assert (ES0 : ew E 35 = getr regs (Z_to_bv 5 8)) by (exact (EX 3%nat ltac:(lia))).
assert (ES1 : ew E 36 = getr regs (Z_to_bv 5 9)) by (exact (EX 4%nat ltac:(lia))).
assert (ES2 : ew E 37 = getr regs (Z_to_bv 5 18)) by (exact (EX 5%nat ltac:(lia))).
assert (UC : bv_unsigned (ew E 33) = c) by (rewrite EC; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E 2) = sp0 - RCB_FRAME) by (rewrite (EE 2%nat 2%bv eq_refl); exact Rsp).
clearbody E.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK rcb_Bspan.
{ unfold ss_meet, rcb_mrs, rcb_mframe, rcb_mslot. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := SA_C) (b := c); [reflexivity | exact UC | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  apply rcb_awr_slot; [exact HL | unfold c in *; lia]. }
(* the two stores wrote the slot's fn and nargs fields and nothing else *)
lazymatch goal with Hfr : frame_of E _ (mrestrict _ memc) (mrestrict _ ?m1) |- _ =>
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 8) -> rdW Wc m1 a = rdW Wc memc a)
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => c <= a < c + 8) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
      rewrite ?Usp, ?UC in Hrr; cbv beta; lia|]);
    destruct Hin
  | exact Ha | exact Hn ]); clear Hfr end.
lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
  set (msF := msx) in *;
  let r := eval vm_compute in (nth 1 (ss_mem ssx) rcb_mslot) in
  pose proof (st_ok_pi_region_nth E ssx (restrict (w_H Wc) msx) 1 r HS eq_refl) as HRs end.
cbn [ms_mem restrict mkst] in HRs.
assert (VFN : aval_mem (rdW Wc (ms_mem msF)) (c + CALL_OFF_FN) 4 fn).
{ apply aval_mem_view.
  exact (field_of_region (segs:=SEGS) E _ 33 c _ _ _ _ _ 0 4%N (SOff 8 0) fn HRs UC
    ltac:(cbn; right; left; reflexivity)
    ltac:(cbn [sv_denot]; rewrite (EE 8%nat 8%bv eq_refl), R8; unfold w64;
          rewrite unsigned_lit_small by (unfold REC_FN_COUNT in Hfn; lia); rewrite Z.add_0_r; reflexivity)
    ltac:(cbn; unfold REC_FN_COUNT in Hfn; lia) ltac:(cbn; lia)). }
assert (VNA : aval_mem (rdW Wc (ms_mem msF)) (c + CALL_OFF_NARGS) 4 0).
{ apply aval_mem_view.
  exact (field_of_region (segs:=SEGS) E _ 33 c _ _ _ _ _ 4 4%N (SLit 0) 0 HRs UC
    ltac:(cbn; left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)). }
assert (HREPF : rec_repA B lyc Sc (rdW Wc (ms_mem msF)) (rec_record R fn []) O1)
  by (apply HPEND; [exact KEEP | exact VFN | exact VNA]).
(* the return *)
eapply (RET Wc _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
prreg HS (1%bv : bv 5) Rf1. prreg HS (10%bv : bv 5) Rf10.
unfold apost_base. eexists lyc, Sc, (ms_regs msF), (ms_mem msF), _.
split.
{ rewrite Rf1, ERA. pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'.
  assert (Gra : getr regs (Z_to_bv 5 1) = getr regs 1) by reflexivity. rewrite Gra, Hra'. reflexivity. }
split.
{ apply (ajournal_mono_k SEGS B) with (k := k); [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ | exact Hk]. }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | Hr']]]]]].
  - prreg HS (Z_to_bv 5 2) Q. rewrite Q, Usp. unfold RCB_FRAME, sp0, spZ.
    replace (bv_unsigned (getr regs 2) - 32 + 32) with (bv_unsigned (getr regs 2)) by lia.
    assert (Gsp : getr regs (Z_to_bv 5 2) = getr regs 2) by reflexivity. rewrite Gsp. apply Z_to_bv_bv_unsigned.
  - prreg HS (Z_to_bv 5 3) Q. rewrite Q, (EE 3%nat (Z_to_bv 5 3) eq_refl). exact R3.
  - prreg HS (Z_to_bv 5 4) Q. rewrite Q, (EE 4%nat (Z_to_bv 5 4) eq_refl). exact R4.
  - prreg HS (Z_to_bv 5 8) Q. rewrite Q. exact ES0.
  - prreg HS (Z_to_bv 5 9) Q. rewrite Q. exact ES1.
  - prreg HS (Z_to_bv 5 18) Q. rewrite Q. exact ES2.
  - destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]];
    (lazymatch goal with |- getr _ ?rr = _ => prreg HS rr Qr end;
     rewrite Qr; lazymatch goal with |- ew E ?nn = getr _ ?rr => rewrite (EE nn rr eq_refl) end;
     apply Rhi; lia). }
exists F, O1.
split; [rewrite Rf10, EC; reflexivity|].
split; [exact HPERM|]. split; [exact HFlen|]. split; [exact HFO|].
split; [exact HREPF|]. split; [exact HO1|]. split; [exact HBB | exact HMLE].
Qed.
End e.
End f.
End d.
