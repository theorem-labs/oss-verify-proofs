(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment D of check_words' ASan walk (plugin-hostd/fuzz_command, 0x87c90 .. 0x87d64), in the form of lib/A/Prog/sup_reply_code.v and proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (seeds, symbolic runs, calls). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words_sD.v, with its module paths, module names, addresses and numbers changed; 202 of its 573 lines of code are new or changed and 1289 lines of the source are left out. *)
(* check_words' ASan+UBSan walk (plugin-hostd/fuzz_command.asan-ubsan, entry 0x87ae8), segment D (check_words_d.v):
   `seg_D : forall c, (forall fx0, ST_LH (c + 1)) -> (forall fx0, ST_REL) -> ST_D c`. The B twin of the A walk's
   lib/A/Prog/check_words_sD.v (an earlier version). The seeds, the latch and the facts carried from the entry
   are in check_words_sD1.v.

   After the item loop of call c (cp = &g_rec.calls[c].fn = A_G_REC + 16 + 56 c), B code:
     0x87f80  ld a0,96(s1); lb a0,0(a0); bnez a0 -> 0x88080   the instrumented check of cp; its partial-granule path
              0x88080 .. 0x8808c and the error path 0x881f0 are not reached (g_rec's shadow is zero: CW_ZSH_P at
              (A_G_REC, 960), shent d_SH of check_words_sD1.v)
     0x87f8c  a2 := cp, a0 := fn, s2 := read, s3 := g_rec; fn = 20 -> 0x88004; s5 := c; fn = 17 -> 0x87fdc;
              fn <> 0 -> the latch 0x8802c
     each call arm (0x87fb4 add, 0x87fdc chain, 0x88004 pin_set): the instrumented check of W16 = Wd + 16 (the shadow
              address (Wd + 16)/8 from slot 136 plus s6; lbu, bnez); its error paths 0x881d8 / 0x881e0 / 0x881e8 are
              not reached (W16 lies in the stack window, whose shadow is zero: AR's zshadow_ok, cwd_stk_addressable);
              a1 := w->w, a0 := cp, a2 := read, `jal` check_words_add 0x88eac (at 0x87fd4) / check_words_chain 0x890e0
              (at 0x87ffc) / check_words_pin_set 0x894cc (at 0x88028)
   check_words_add and check_words_pin_set keep the FP state (apost_base, afn_pre_na: PaNoChain.v's cl_callS_na);
   check_words_chain returns at some FP state fx1 (apost_baseF: PaFx.v's cl_callSF, its frame chain by achain_push
   on afn_pre's chain at s0 = sp0), and the walk goes on at fx1 with cwdh_after
   (check_words_sD1.v, a closed section) and cw_ent_fx. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_words_d check_words_ki check_words_sD1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* a register of the symbolic state, without prreg's normalisation *)
Ltac cwd_reg HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v in Hr;
  cbn [ms_regs restrict mkst] in Hr
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.
Ltac cwdc_cs_tac := lazymatch goal with |- acallee_saved (bv_unsigned ?r) =>
  let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v; unfold acallee_saved; lia end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's hypotheses (check_words_c.v:125-127), word for word *)
Hypothesis HADD : forall fx0 : YK11.FPState, @tcheck_words_add_spec fx0 rc SK PI B MT.
Hypothesis HCHAIN : forall fx0 : YK11.FPState, @tcheck_words_chain_spec fx0 rc SK PI B MT.
Hypothesis HPIN : forall fx0 : YK11.FPState, @tcwps_spec fx0 rc SK PI B MT.
(* the walk hypotheses and the record facts of check_words_d.v *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis RRO : RRO_P.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis IMG : @CmdRecBase.cmd_img_facts SK SEGS B.
Hypothesis cmd_prog_unowned : cmd_prog_unowned_P B.
Hypothesis ZSH_cw : CW_ZSH_P B.
Let RUN := paj_run (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNTO := paj_run_to (PL := PL_cmd) (PI := PI) B LAWS.
Let BR := paj_branch (PI := PI).

(* the three program callees' entries: SIGP (cmd_sig_prog) and cmd_af by computation *)
Lemma cwd_sig_add : SIG CS_check_words_add = BASE + AF_check_words_add.
Proof. rewrite (SIGP CS_check_words_add ltac:(vm_compute; tauto)). f_equal; vm_compute; reflexivity. Qed.
Lemma cwd_sig_chain : SIG CS_check_words_chain = BASE + AF_check_words_chain.
Proof. rewrite (SIGP CS_check_words_chain ltac:(vm_compute; tauto)). f_equal; vm_compute; reflexivity. Qed.
Lemma cwd_sig_pin : SIG CS_check_words_pin_set = BASE + AF_check_words_pin_set.
Proof. rewrite (SIGP CS_check_words_pin_set ltac:(vm_compute; tauto)). f_equal; vm_compute; reflexivity. Qed.
Lemma cwd_mem_kept_eq : forall (rd rd' : reader) sp1 F, (forall x, 0 <= x < 2 ^ 64 -> rd' x = rd x) ->
cw_mem_kept B rd rd' sp1 F.
Proof. intros rd rd' sp1 F He x Hx _ _ _. exact (He x Hx). Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the calls of check_words_add (jal at 0x87fd4) and check_words_pin_set (jal at 0x88028): PaNoChain.v's
   cl_callS_na (both callees' pre is afn_pre_na, no frame chain), the callee's statement at its entry, then INV_LH at
   the return and the latch (cwdh_after) *)
Lemma cwd_call_add : forall e lyc Sc Wc regs2 mem2 md2 pos sp1 line c args, ST_LH B MT (c + 1) -> ST_REL B MT ->
  cw_ent B MT e -> cw_core B e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED ->
  cw_line B MT e lyc Sc (rdW Wc mem2) line -> cw_lscr e (rdW Wc mem2) sp1 (frame_addr (e_ly e) 0 pos) line c ->
  nth_error (r_calls (e_R e)) (Z.to_nat c) = Some (0, args) -> 0 <= c < cw_ncalls e ->
  getr regs2 10 = w64 (A_G_REC + OFF_CALLS + CALL_SIZE * c) -> getr regs2 11 = w64 (e_arr e) ->
  getr regs2 12 = w64 (cw_read e) -> getr regs2 1 = Z_to_bv 64 (BASE + CW_PC_RADD) ->
  getr regs2 19 = w64 A_G_REC -> getr regs2 21 = w64 c ->
  SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + AF_check_words_add)) mem2 (seg_rom SEGS)) md2) (cw_post B MT e).
Proof.
intros e lyc Sc Wc regs2 mem2 md2 pos sp1 line c args HLH HREL Hent Hc Hl Hs Hnth Hcr R10 R11 R12 R1 R19 R21.
pose proof Hent as Hent0. unfold cw_ent in Hent0. cbv zeta in Hent0.
destruct Hent0 as (HPRE0 & _ & _ & _ & _ & HVO & _ & _ & _ & Harr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev
  & _ & _ & _ & Harr8).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (Hal0 & _).
pose proof Hc as Hc0. unfold cw_core in Hc0. cbv zeta in Hc0.
destruct Hc0 as (HJ & Hsp & Hsp32 & Hspr & G3 & G4 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
pose proof (cwdl_ncalls_le (fx := fx) B MT e Hent) as Hn16.
destruct (cwd_rodata_at (fx := fx) B MT LAWS RRO HB IMG e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED Hent Hc) as [HRO HROK].
destruct (cwd_call_at (fx := fx) B MT LAWS cmd_prog_unowned e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED line c 0 args
  Hent Hc Hl Hnth ltac:(lia)) as (_ & Hla & _ & Vna & _ & Hargs).
destruct (cwd_cwok (fx := fx) B MT e c 0 args Hent Hnth) as (_ & Hok0 & _ & _).
destruct (Hok0 eq_refl) as (Hl4 & Hx2 & Hx3). cbn [fst snd] in Hl4, Hx2, Hx3.
assert (N2 : nth_error args 2 = Some (nth 2 args [])) by (apply nth_error_nth'; lia).
assert (N3 : nth_error args 3 = Some (nth 3 args [])) by (apply nth_error_nth'; lia).
destruct (Hargs 2%nat (nth 2 args []) N2) as (q2 & V2 & Hq2 & Hb2 & Hs2).
destruct (Hargs 3%nat (nth 3 args []) N3) as (q3 & V3 & Hq3 & Hb3 & Hs3).
change (8 * Z.of_nat 2) with 16 in V2. change (8 * Z.of_nat 3) with 24 in V3.
assert (Hr : 0 <= cw_read e <= 64) by (unfold cw_read, cw_n; lia).
assert (Hcp1 : A_G_REC + OFF_CALLS <= A_G_REC + OFF_CALLS + CALL_SIZE * c) by (unfold CALL_SIZE; lia).
assert (Hcp2 : A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_SIZE <= A_G_REC + REC_SIZE)
  by (unfold OFF_CALLS, CALL_SIZE, REC_SIZE; lia).
assert (Hcp8 : (A_G_REC + OFF_CALLS + CALL_SIZE * c) mod 8 = 0) by (unfold OFF_CALLS, CALL_SIZE; exact (cwd_cp_al c)).
assert (Hna : 0 <= Z.of_nat (length args) <= 6) by lia.
assert (Hn4 : Z.of_nat (length args) = 4) by lia.
assert (HA2 : Z.of_nat (length args) = 4 ->
  aval_mem (rdW Wc mem2) (A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_OFF_ARGS + 16) 8 q2 /\ 0 <= q2 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) q2 (Z.of_nat (length (nth 2 args [])) + 1) /\ astr_atR (rdW Wc mem2) q2 (nth 2 args []))
  by (intros _; split; [exact V2|]; split; [lia|]; split; [exact Hb2 | exact Hs2]).
assert (HA3 : Z.of_nat (length args) = 4 ->
  aval_mem (rdW Wc mem2) (A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_OFF_ARGS + 24) 8 q3 /\ 0 <= q3 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) q3 (Z.of_nat (length (nth 3 args [])) + 1) /\ astr_atR (rdW Wc mem2) q3 (nth 3 args []))
  by (intros _; split; [exact V3|]; split; [lia|]; split; [exact Hb3 | exact Hs3]).
assert (HW3 : 3 < cw_read e ->
  in_blockA (ablocks B lyc Sc) (e_arr e + 24) 8 /\ aval_mem (rdW Wc mem2) (e_arr e + 24) 8 (nth 3 (e_wp e) 0) /\
  0 <= nth 3 (e_wp e) 0 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) (nth 3 (e_wp e) 0) (Z.of_nat (length (nth 3 (e_ws e) [])) + 1) /\
  astr_atR (rdW Wc mem2) (nth 3 (e_wp e) 0) (nth 3 (e_ws e) [])).
{ intros H3. pose proof (cwdh_word (fx := fx) B MT LAWS e lyc Sc Wc regs2 mem2 md2 pos sp1 line 3%nat Hent Hc Hl ltac:(lia)) as X.
  change (8 * Z.of_nat 3) with 24 in X. exact X. }
assert (HW4 : 4 < cw_read e ->
  in_blockA (ablocks B lyc Sc) (e_arr e + 32) 8 /\ aval_mem (rdW Wc mem2) (e_arr e + 32) 8 (nth 4 (e_wp e) 0) /\
  0 <= nth 4 (e_wp e) 0 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) (nth 4 (e_wp e) 0) (Z.of_nat (length (nth 4 (e_ws e) [])) + 1) /\
  astr_atR (rdW Wc mem2) (nth 4 (e_wp e) 0) (nth 4 (e_ws e) [])).
{ intros H4. pose proof (cwdh_word (fx := fx) B MT LAWS e lyc Sc Wc regs2 mem2 md2 pos sp1 line 4%nat Hent Hc Hl ltac:(lia)) as X.
  change (8 * Z.of_nat 4) with 32 in X. exact X. }
assert (Hev1 : st_nev Sc + EV_CHECK_WORDS_ADD <= EV_MAX) by (unfold EV_CHECK_WORDS_ADD; unfold EV_CHECK_WORDS in Hev; lia).
assert (HSTKa : CHECK_WORDS_ADD_STK = 8256) by reflexivity.
assert (HSTK : CHECK_WORDS_STK = 16848) by (vm_compute; reflexivity).
destruct (cwdh_ra CW_PC_RADD ltac:(unfold CW_PC_RADD; lia) eq_refl) as [Hraw Hra4].
rewrite <- R1 in Hraw, Hra4.
eapply SRr_bind.
{ exact (OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.PaNoChain.cl_callS_na (fx := fx) (PI := PI) B LAWS
    Wc regs2 mem2
    (Z_to_bv 64 (BASE + AF_check_words_add)) CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
    [(0, pos)] lyc Sc md2 EV_JOINED CHECK_WORDS_ADD_STK [] EV_CHECK_WORDS_ADD (sp1 - cw_sp0 e) (getr regs2 1)
    (fun ly' S' (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) =>
       Permutation (ablocks B ly' S') (ablocks B lyc Sc) /\ ly' = lyc /\ S' = Sc)
    HJ ltac:(lia) (cwd_o16 sp1 (cw_sp0 e) Hsp32 Hal0) ltac:(lia) ltac:(lia) ltac:(lia)
    (eq_trans G3 Hgp0) (eq_trans G4 Htp0) eq_refl Hraw Hra4
    (fun HPRE1 => HADD fx lyc Sc Wc regs2 mem2 md2 (A_G_REC + OFF_CALLS + CALL_SIZE * c) (e_arr e) (cw_read e)
       (Z.of_nat (length args)) (nth 3 (e_wp e) 0) (nth 4 (e_wp e) 0) q2 q3 (nth 3 (e_ws e) []) (nth 4 (e_ws e) [])
       (nth 2 args []) (nth 3 args []) HPRE1 HRO R10 R11 R12 Hr Harr HROK HVO Hcp1 Hcp2 Hcp8 Vna Hna HA2 HA3 HW3 HW4
       Harr8 Hn4 Hx2 Hx3 Hev1)
    (fun a Ha => False_ind _ (inFP_nil a Ha))). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc & HP & (HPm & Hly3 & HS3)).
change (EV_JOINED + EV_CHECK_WORDS_ADD) with EV_JOINED in HJ3.
replace (cw_sp0 e + (sp1 - cw_sp0 e)) with sp1 in HJc by lia.
rewrite R1. subst S3.
exact (cwdh_after (fx := fx) B MT LAWS MTL cmd_prog_unowned ZSH_cw CW_PC_RADD e lyc Sc Wc regs2 mem2 md2 pos sp1 line c
  CHECK_WORDS_ADD_STK EV_CHECK_WORDS_ADD W3 ly3 Sc regs3 mem3 md3 HLH HREL (or_intror (or_introl eq_refl)) Hent Hc Hl Hs
  R19 R21 Hcr ltac:(lia) HJ3 HJc HP HPm Hly3 (mo_le_refl MT MTL Sc)).
Qed.

Lemma cwd_call_pin : forall e lyc Sc Wc regs2 mem2 md2 pos sp1 line c args, ST_LH B MT (c + 1) -> ST_REL B MT ->
  cw_ent B MT e -> cw_core B e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED ->
  cw_line B MT e lyc Sc (rdW Wc mem2) line -> cw_lscr e (rdW Wc mem2) sp1 (frame_addr (e_ly e) 0 pos) line c ->
  nth_error (r_calls (e_R e)) (Z.to_nat c) = Some (20, args) -> 0 <= c < cw_ncalls e ->
  getr regs2 10 = w64 (A_G_REC + OFF_CALLS + CALL_SIZE * c) -> getr regs2 11 = w64 (e_arr e) ->
  getr regs2 12 = w64 (cw_read e) -> getr regs2 1 = Z_to_bv 64 (BASE + CW_PC_LATCH) ->
  getr regs2 19 = w64 A_G_REC -> getr regs2 21 = w64 c ->
  SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + AF_check_words_pin_set)) mem2 (seg_rom SEGS)) md2) (cw_post B MT e).
Proof.
intros e lyc Sc Wc regs2 mem2 md2 pos sp1 line c args HLH HREL Hent Hc Hl Hs Hnth Hcr R10 R11 R12 R1 R19 R21.
pose proof Hent as Hent0. unfold cw_ent in Hent0. cbv zeta in Hent0.
destruct Hent0 as (HPRE0 & _ & _ & _ & _ & HVO & _ & _ & _ & Harr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev
  & _ & _ & _ & Harr8).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (Hal0 & _).
pose proof Hc as Hc0. unfold cw_core in Hc0. cbv zeta in Hc0.
destruct Hc0 as (HJ & Hsp & Hsp32 & Hspr & G3 & G4 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & Hnev & _).
pose proof (cwdl_ncalls_le (fx := fx) B MT e Hent) as Hn16.
destruct (cwd_rodata_at (fx := fx) B MT LAWS RRO HB IMG e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED Hent Hc) as [HRO HROK].
destruct (cwd_call_at (fx := fx) B MT LAWS cmd_prog_unowned e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED line c 20 args
  Hent Hc Hl Hnth ltac:(lia)) as (_ & Hla & _ & Vna & _ & Hargs).
destruct (cwd_cwok (fx := fx) B MT e c 20 args Hent Hnth) as (_ & _ & _ & Hok20).
destruct (Hok20 eq_refl) as (Hl4 & Hx3). cbn [fst snd] in Hl4, Hx3.
assert (N3 : nth_error args 3 = Some (nth 3 args [])) by (apply nth_error_nth'; lia).
destruct (Hargs 3%nat (nth 3 args []) N3) as (q3 & V3 & Hq3 & Hb3 & Hs3).
change (8 * Z.of_nat 3) with 24 in V3.
assert (Hr : 0 <= cw_read e <= 64) by (unfold cw_read, cw_n; lia).
assert (Hcp1 : A_G_REC + OFF_CALLS <= A_G_REC + OFF_CALLS + CALL_SIZE * c) by (unfold CALL_SIZE; lia).
assert (Hcp2 : A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_SIZE <= A_G_REC + REC_SIZE)
  by (unfold OFF_CALLS, CALL_SIZE, REC_SIZE; lia).
assert (Hcp8 : (A_G_REC + OFF_CALLS + CALL_SIZE * c) mod 8 = 0) by (unfold OFF_CALLS, CALL_SIZE; exact (cwd_cp_al c)).
assert (Hna : 0 <= Z.of_nat (length args) <= 6) by lia.
assert (Hn4 : Z.of_nat (length args) = 4) by lia.
assert (HA3 : Z.of_nat (length args) = 4 ->
  aval_mem (rdW Wc mem2) (A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_OFF_ARGS + 24) 8 q3 /\ 0 <= q3 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) q3 (Z.of_nat (length (nth 3 args [])) + 1) /\ astr_atR (rdW Wc mem2) q3 (nth 3 args []))
  by (intros _; split; [exact V3|]; split; [lia|]; split; [exact Hb3 | exact Hs3]).
assert (HW4 : 4 < cw_read e ->
  in_blockA (ablocks B lyc Sc) (e_arr e + 32) 8 /\ range_addressable (rdW Wc mem2) SHADOW_OFF (e_arr e + 32) 8 /\
  aval_mem (rdW Wc mem2) (e_arr e + 32) 8 (nth 4 (e_wp e) 0) /\ 0 <= nth 4 (e_wp e) 0 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) (nth 4 (e_wp e) 0) (Z.of_nat (length (nth 4 (e_ws e) [])) + 1) /\
  astr_atR (rdW Wc mem2) (nth 4 (e_wp e) 0) (nth 4 (e_ws e) [])).
{ intros H4. pose proof (cwdh_word (fx := fx) B MT LAWS e lyc Sc Wc regs2 mem2 md2 pos sp1 line 4%nat Hent Hc Hl ltac:(lia)) as X.
  change (8 * Z.of_nat 4) with 32 in X. destruct X as (Xb & X).
  split; [exact Xb|]. split; [exact (cwd_blk_ra B LAWS lyc Sc Wc mem2 md2 (e_arr e + 32) 8 HAR Xb ltac:(lia)) | exact X]. }
assert (Hev1 : st_nev Sc + EV_CWPS <= EV_MAX) by (unfold EV_CWPS; unfold EV_CHECK_WORDS in Hev; lia).
assert (HSTKp : CWPS_STK = 8224) by reflexivity.
assert (HSTK : CHECK_WORDS_STK = 16848) by (vm_compute; reflexivity).
destruct (cwdh_ra CW_PC_LATCH ltac:(unfold CW_PC_LATCH; lia) eq_refl) as [Hraw Hra4].
rewrite <- R1 in Hraw, Hra4.
eapply SRr_bind.
{ exact (OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.PaNoChain.cl_callS_na (fx := fx) (PI := PI) B LAWS
    Wc regs2 mem2
    (Z_to_bv 64 (BASE + AF_check_words_pin_set)) CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e)
    (e_md e) [(0, pos)] lyc Sc md2 EV_JOINED CWPS_STK [] EV_CWPS (sp1 - cw_sp0 e) (getr regs2 1)
    (fun ly' S' (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) =>
       ly' = lyc /\ S' = Sc)
    HJ ltac:(lia) (cwd_o16 sp1 (cw_sp0 e) Hsp32 Hal0) ltac:(lia) ltac:(lia) ltac:(lia)
    (eq_trans G3 Hgp0) (eq_trans G4 Htp0) eq_refl Hraw Hra4
    (fun HPRE1 => HPIN fx lyc Sc Wc regs2 mem2 md2 (A_G_REC + OFF_CALLS + CALL_SIZE * c) (e_arr e) (cw_read e)
       (Z.of_nat (length args)) (nth 4 (e_wp e) 0) q3 (nth 4 (e_ws e) []) (nth 3 args [])
       HPRE1 HRO HROK HVO R10 R11 R12 Hr Hcp1 Hcp2 Hcp8 Vna Hna HA3 HW4 Harr8 Hn4 Hx3 Hev1)
    (fun a Ha => False_ind _ (inFP_nil a Ha))). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc & HP & (Hly3 & HS3)).
change (EV_JOINED + EV_CWPS) with EV_JOINED in HJ3.
replace (cw_sp0 e + (sp1 - cw_sp0 e)) with sp1 in HJc by lia.
rewrite R1. subst S3 ly3.
exact (cwdh_after (fx := fx) B MT LAWS MTL cmd_prog_unowned ZSH_cw CW_PC_LATCH e lyc Sc Wc regs2 mem2 md2 pos sp1 line c
  CWPS_STK EV_CWPS W3 lyc Sc regs3 mem3 md3 HLH HREL (or_introl eq_refl) Hent Hc Hl Hs
  R19 R21 Hcr ltac:(lia) HJ3 HJc HP (Permutation_refl _) eq_refl (mo_le_refl MT MTL Sc)).
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the call of check_words_chain (fn = 17) at 0x87ffc, through PaFx.v's cl_callSF (the callee's footprint is [], its
   post apost_baseF) and its statement HCHAIN, back at 0x88000 at the FP state fx1 the callee returns: the latch at
   fx1 (cwdh_after, a lemma of check_words_sD1.v's closed section), lifted to the entry's FP state by
   srr_apost_baseF_lift *)
Lemma cwd_call_chain : forall e lyc Sc Wc regs2 mem2 md2 pos sp1 line c args,
  (forall fx0, ST_LH (fx := fx0) B MT (c + 1)) -> (forall fx0, ST_REL (fx := fx0) B MT) ->
  cw_ent B MT e -> cw_core B e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED ->
  cw_line B MT e lyc Sc (rdW Wc mem2) line -> cw_lscr e (rdW Wc mem2) sp1 (frame_addr (e_ly e) 0 pos) line c ->
  nth_error (r_calls (e_R e)) (Z.to_nat c) = Some (17, args) -> 0 <= c < cw_ncalls e ->
  getr regs2 10 = w64 (A_G_REC + OFF_CALLS + CALL_SIZE * c) -> getr regs2 11 = w64 (e_arr e) ->
  getr regs2 12 = w64 (cw_read e) -> getr regs2 1 = Z_to_bv 64 (BASE + CW_PC_RCHAIN) ->
  getr regs2 19 = w64 A_G_REC -> getr regs2 21 = w64 c ->
  SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + AF_check_words_chain)) mem2 (seg_rom SEGS)) md2) (cw_post B MT e).
Proof.
intros e lyc Sc Wc regs2 mem2 md2 pos sp1 line c args HLH HREL Hent HC HL HLS Hnth Hc H10 H11 H12 H1 H19 H21.
pose proof Hent as Hent'. unfold cw_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE & HFRM & HROD & _ & _ & HOBJ & Hspw & Hhi & Harr & Harr64 & Hn & Hlen & Hn31 & Hblk & Hwords
  & HJN & _ & _ & _ & HC4 & Hev & Hlive & MOK & HWd8 & Harr8).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & _ & Hch0 & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htophi).
pose proof HC as HC'. unfold cw_core in HC'. cbv zeta in HC'.
destruct HC' as (HJ & Hsp & Hsp32 & Hsprng & H3 & H4 & H8 & H9 & H22 & Hsaves & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2).
assert (WS : CHECK_WORDS_STK = 16848) by (vm_compute; reflexivity).
assert (WC : CHECK_WORDS_CHAIN_STK = 12528) by (vm_compute; reflexivity).
assert (EVJ : EV_JOINED = 1) by reflexivity.
assert (EVC : EV_CHECK_WORDS = 2) by reflexivity.
assert (EVCC : EV_CHECK_WORDS_CHAIN = 0) by reflexivity.
destruct (cwdg_div_of _ 16 ltac:(lia) Hal16) as (q0 & Hq0).
pose proof HJ as (HAR1 & Hly1 & _ & _ & _ & Hfrs1 & Hnev1 & _).
destruct Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof (cwdl_ncalls_le (fx := fx) B MT e Hent) as Hn16.
(* check_words_chain's premises at the call state *)
destruct (cwd_rodata_at (fx := fx) B MT LAWS RRO HB IMG e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED Hent HC) as [P3 P9].
destruct (cwd_call_at (fx := fx) B MT LAWS cmd_prog_unowned e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED line c 17 args
  Hent HC HL Hnth ltac:(lia)) as (_ & Hna6 & _ & Vna & _ & Hargs).
destruct (cwd_cwok (fx := fx) B MT e c 17 args Hent Hnth) as (_ & _ & H17 & _).
destruct (H17 eq_refl) as (Hl3 & Hx1 & Hx2). cbn [snd] in Hl3, Hx1, Hx2.
assert (Hl1 : (1 < length args)%nat) by lia. assert (Hl2 : (2 < length args)%nat) by lia.
destruct (Hargs 1%nat (nth 1 args []) (nth_error_nth' args [] Hl1)) as (p1 & Vp1 & Rp1 & Bp1 & Sp1).
destruct (Hargs 2%nat (nth 2 args []) (nth_error_nth' args [] Hl2)) as (p2 & Vp2 & Rp2 & Bp2 & Sp2).
destruct (cwd_words_at (fx := fx) B MT LAWS e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED line Hent HC HL) as (_ & _ & Harr' & Hw').
assert (PW : forall k, 2 <= k < cw_read e ->
  in_blockA (ablocks B lyc Sc) (e_arr e + 8 * k) 8 /\
  aval_mem (rdW Wc mem2) (e_arr e + 8 * k) 8 (nth (Z.to_nat k) (e_wp e) 0) /\
  0 <= nth (Z.to_nat k) (e_wp e) 0 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) (nth (Z.to_nat k) (e_wp e) 0) (Z.of_nat (length (nth (Z.to_nat k) (e_ws e) []))+ 1) /\
  astr_atR (rdW Wc mem2) (nth (Z.to_nat k) (e_wp e) 0) (nth (Z.to_nat k) (e_ws e) [])).
{ intros k Hk. unfold cw_read, cw_n in Hk.
  assert (Hkn : (Z.to_nat k < length (e_ws e))%nat) by lia.
  destruct (Hw' (Z.to_nat k) Hkn) as (W1 & W2 & W3 & W4). rewrite Z2Nat.id in W1 by lia.
  split; [|split; [exact W1 | split; [exact W2 | split; [exact W3 | exact W4]]]].
  destruct Harr' as (p & m & Hin & Hp1 & Hp2). exists p, m. split; [exact Hin | lia]. }
assert (Hr64 : 0 <= cw_read e <= 64) by (unfold cw_read, cw_n; lia).
assert (Hcp1 : A_G_REC + OFF_CALLS <= A_G_REC + OFF_CALLS + CALL_SIZE * c) by (unfold CALL_SIZE; lia).
assert (Hcp2 : A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_SIZE <= A_G_REC + REC_SIZE)
  by (unfold OFF_CALLS, CALL_SIZE, REC_SIZE; lia).
assert (Hcp8 : (A_G_REC + OFF_CALLS + CALL_SIZE * c) mod 8 = 0) by (unfold OFF_CALLS, CALL_SIZE; exact (cwd_cp_al c)).
assert (Hna : 0 <= Z.of_nat (length args) <= 6) by lia.
assert (Hn3 : Z.of_nat (length args) = 3) by (rewrite Hl3; reflexivity).
assert (Hp1f : Z.of_nat (length args) = 3 ->
  aval_mem (rdW Wc mem2) (A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_OFF_ARGS + 8) 8 p1 /\ 0 <= p1 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) p1 (Z.of_nat (length (nth 1 args [])) + 1) /\ astr_atR (rdW Wc mem2) p1 (nth 1 args []))
  by (intros _; split; [exact Vp1 | split; [lia | split; [exact Bp1 | exact Sp1]]]).
assert (Hp2f : Z.of_nat (length args) = 3 ->
  aval_mem (rdW Wc mem2) (A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_OFF_ARGS + 16) 8 p2 /\ 0 <= p2 < 2 ^ 64 /\
  in_blockA (ablocks B lyc Sc) p2 (Z.of_nat (length (nth 2 args [])) + 1) /\ astr_atR (rdW Wc mem2) p2 (nth 2 args []))
  by (intros _; split; [exact Vp2 | split; [lia | split; [exact Bp2 | exact Sp2]]]).
assert (HC4' : count_cid 4 (frames Sc) < fs_frames 4) by (rewrite Hfrs1; exact HC4).
assert (HEV : st_nev Sc + EV_CHECK_WORDS_CHAIN <= EV_MAX) by lia.
(* s0 = sp0 at the call: the frame chain pushes check_words' own record (ra at sp0 - 8, s0 at sp0 - 16) *)
assert (Hs0 : s0Z regs2 = cw_sp0 e) by (unfold s0Z; rewrite H8; reflexivity).
assert (HCH : exists ch1, achain lyc (rdW Wc mem2) (cw_sp0 e + (sp1 - cw_sp0 e)) (s0Z regs2) ch1).
{ rewrite Hs0. replace (cw_sp0 e + (sp1 - cw_sp0 e)) with sp1 by lia.
  destruct (Z_lt_le_dec (cw_sp0 e) (ly_top (e_ly e) - 16)) as [Hlt | Hge].
  - exists ((cw_sp0 e, bv_unsigned (getr (e_regs e) (Z_to_bv 5 1)), s0Z (e_regs e)) :: e_ch e).
    apply (achain_ly_top (e_ly e) lyc); [exact Etop|].
    apply (achain_push (e_ly e) (rdW (e_W e) (e_mem e)) (rdW Wc mem2) (cw_sp0 e) (s0Z (e_regs e))
      (bv_unsigned (getr (e_regs e) (Z_to_bv 5 1))) (e_ch e) sp1 Hch0).
    + lia.
    + intros a Ha. exact (cwd_keep_above (fx := fx) B MT e lyc Sc Wc regs2 mem2 md2 pos sp1 EV_JOINED a Hent HC Ha).
    + pose proof (Hsaves 0%nat 1 eq_refl) as HS0.
      replace (cw_sp0 e - 8 - 8 * Z.of_nat 0) with (cw_sp0 e - 8) in HS0 by lia.
      exact (cwdg_rdword _ _ _ _ HS0 (cwdg_bv64 _)).
    + pose proof (Hsaves 1%nat 8 eq_refl) as HS1.
      replace (cw_sp0 e - 8 - 8 * Z.of_nat 1) with (cw_sp0 e - 16) in HS1 by lia.
      exact (cwdg_rdword _ _ _ _ HS1 (cwdg_bv64 (getr (e_regs e) (Z_to_bv 5 8)))).
    + exact Hra4.
    + unfold cw_sp0 in *; lia.
    + apply (cwdg_mod_of _ 8 ltac:(lia)). exists (2 * q0). unfold cw_sp0. lia.
    + exact Hlt.
    + lia.
  - exists []. unfold achain. left. split; [right; left; rewrite Etop; exact Hge | reflexivity]. }
destruct HCH as (ch1 & Hch1).
pose proof (fun HPRE1 : afn_pre SEGS B CHECK_WORDS_CHAIN_STK lyc Sc Wc regs2 mem2 md2 ch1 =>
  HCHAIN fx lyc Sc Wc regs2 mem2 md2 ch1 (A_G_REC + OFF_CALLS + CALL_SIZE * c) (e_arr e) (cw_read e)
    (Z.of_nat (length args)) p1 p2 (e_wp e) (e_ws e) (nth 1 args []) (nth 2 args [])
    HPRE1 HFRM P3 H10 H11 H12 Hr64 Harr64 P9 HOBJ Hcp1 Hcp2 Hcp8 Vna Hna Hp1f Hp2f PW Harr8 Hn3 Hx1 Hx2 HC4' HEV)
  as HCALL.
unfold apost_baseF, cfg_at in HCALL.
(* the call rule's premises *)
assert (Hspo : spZ regs2 = cw_sp0 e + (sp1 - cw_sp0 e)) by lia.
assert (Halo : (sp1 - cw_sp0 e) mod 16 = 0) by exact (cwd_o16 sp1 (cw_sp0 e) Hsp32 Hal16).
assert (Hnego : sp1 - cw_sp0 e <= 0) by lia.
assert (Hstk1 : 0 <= CHECK_WORDS_CHAIN_STK) by lia.
assert (Hbud : CHECK_WORDS_CHAIN_STK - (sp1 - cw_sp0 e) <= CHECK_WORDS_STK) by lia.
assert (Hgp' : getr regs2 3 = w64 (as_gp B)) by (rewrite H3; exact Hgp).
assert (Htp' : getr regs2 4 = w64 (as_tp B)) by (rewrite H4; exact Htp).
destruct (cwdh_ra CW_PC_RCHAIN ltac:(unfold CW_PC_RCHAIN; lia) eq_refl) as [Hraw Hra4'].
rewrite <- H1 in Hraw, Hra4'.
eapply SRr_bind.
{ refine (OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.PaFx.cl_callSF (fx := fx) (PI := PI) B LAWS
    Wc regs2 mem2 _ CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e)
    (e_md e) [(0, pos)] lyc Sc md2 EV_JOINED CHECK_WORDS_CHAIN_STK [] EV_CHECK_WORDS_CHAIN (sp1 - cw_sp0 e)
    (getr regs2 1) ch1 _ HJ Hspo Halo Hnego Hstk1 Hbud Hgp' Htp' eq_refl Hraw Hra4' Hch1 HCALL
    (fun a Hf => False_ind _ (inFP_nil a Hf))). }
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs3 & mem3 & md3 & Hfx & -> & HJ2 & HJ1 & HP & HK).
destruct HK as (HPerm2 & Hly2 & f & HS2).
rewrite EVCC, Z.add_0_r in HJ2.
replace (cw_sp0 e + (sp1 - cw_sp0 e)) with sp1 in HJ1 by lia.
assert (Hmo2 : mo_le MT Sc S2 0) by (rewrite HS2; exact (mo_le_set_fs_r MT MTFL _ _ _ _ (mo_le_refl MT MTL Sc))).
rewrite H1. unfold cw_post.
apply (OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog.PaFx.srr_apost_baseF_lift (fx := fx) SEGS fx1 W2 _
  B CHECK_WORDS_STK [] (e_regs e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) EV_CHECK_WORDS _ Hfx).
(* back at 0x88000 at fx1: INV_LH at the return, then the latch *)
exact (cwdh_after (fx := fx1) B MT LAWS MTL cmd_prog_unowned ZSH_cw CW_PC_RCHAIN e lyc Sc Wc regs2 mem2 md2 pos sp1 line c
  CHECK_WORDS_CHAIN_STK EV_CHECK_WORDS_CHAIN W2 ly2 S2 regs3 mem3 md3 (HLH fx1) (HREL fx1) (or_intror (or_intror eq_refl))
  (cw_ent_fx fx fx1 B MT e Hent (fxrel_frm0 fx fx1 HFRM Hfx)) HC HL HLS H19 H21 Hc Hstk1 HJ2 HJ1 HP HPerm2 Hly2 Hmo2).
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
Lemma seg_D : forall c, (forall fx0, ST_LH (fx := fx0) B MT (c + 1)) -> (forall fx0, ST_REL (fx := fx0) B MT) -> ST_D B MT c.
Proof.
intros c HLH HREL. unfold ST_D. intros e lyc Sc Wc regsc memc mdc pos sp1 line Hent HI.
destruct HI as (HC & HLN & HLS & HCS & Hcr).
pose proof HC as (HJ & Hsp1 & Hsp32 & Hsp1lo & Hgp3 & Hgp4 & Hr8 & Hr9 & Hr22 & HSAV
  & V16 & V24 & V32 & VF56 & VSH4 & VSH5).
pose proof HJ as (HARc & HLY & _ & _ & _ & HFRc & Hnev & _ & _ & _ & _ & _ & _ & HPRESc & HSTKOK & _ & _).
destruct HSTKOK as (Hal16 & HstkP & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
assert (HSTK : CHECK_WORDS_STK = 16848) by (vm_compute; reflexivity).
pose proof Hent as Hent'. unfold cw_ent in Hent'. cbv zeta in Hent'.
destruct Hent' as (HPRE & HFRM & HROD & H10e & HRO & HOBJ & Hspw & Hhiw & Harr & Harr64 & Hn4 & Hlenwp
  & Hn31 & Hblk & Hwords & HJN & HREC & HWP & Hcid0 & Hcid4 & Hev & Hlive & MOK & HWd8 & Harr8).
assert (Hnthx : exists fn args, nth_error (r_calls (e_R e)) (Z.to_nat c) = Some (fn, args)).
{ destruct (nth_error (r_calls (e_R e)) (Z.to_nat c)) as [[fn args]|] eqn:E1; [exists fn, args; reflexivity|].
  exfalso. apply nth_error_None in E1. unfold cw_ncalls in Hcr. lia. }
destruct Hnthx as (fn & args & Hnth).
destruct (cwd_call_at (fx := fx) B MT LAWS cmd_prog_unowned e lyc Sc Wc regsc memc mdc pos sp1 EV_JOINED line c fn args
  Hent HC HLN Hnth ltac:(lia)) as (Hfn0 & Hargs6 & VFN & VNA & VNC & HARGS).
destruct (cwd_words_at (fx := fx) B MT LAWS e lyc Sc Wc regsc memc mdc pos sp1 EV_JOINED line Hent HC HLN)
  as (VW16 & VW24 & HARRB & HWORD).
pose proof (cwdl_ncalls_le (fx := fx) B MT e Hent) as Hn16.
assert (Hsp1b : 2 ^ 46 <= sp1 <= 2 ^ 47) by (unfold cw_sp0 in *; lia).
assert (HW16b : 2 ^ 46 <= e_Wd e + 16 <= 2 ^ 47 - 16) by (unfold cw_sp0 in *; lia).
assert (HW16s : sp1 + 168 <= e_Wd e + 16) by (unfold cw_sp0 in *; lia).
assert (Hfnb : 0 <= fn <= 25) by (unfold REC_FN_COUNT in Hfn0; lia).
assert (Hrdvb : 0 <= cw_read e <= 64).
{ unfold cw_read, cw_n. split; [apply Z.min_glb; [apply Zle_0_nat | lia] | apply Z.le_min_r]. }
assert (Hcb : 0 <= c <= 15) by lia.
destruct (ZSH_cw lyc Sc Wc memc mdc A_G_REC 960 HARc ltac:(left; reflexivity)) as (RAG & _).
assert (RA1 : range_addressable (rdW Wc memc) SHADOW_OFF (A_G_REC + 16 + 56 * c) 8).
{ apply (range_addressable_sub (rdW Wc memc) SHADOW_OFF A_G_REC 960); [exact RAG | lia | lia]. }
destruct HLY as (LY1 & LY2 & LY3 & LY4 & LY5 & LYF & LY7 & LY8 & LYtop & LYlo & LYhi & LYrest).
assert (RA2 : range_addressable (rdW Wc memc) SHADOW_OFF (e_Wd e + 16) 8).
{ apply (cwd_stk_addressable B lyc Sc Wc memc mdc (e_Wd e + 16) 8 HARc);
  [rewrite LYlo | rewrite LYhi | ]; unfold cw_sp0 in *; lia. }
replace (A_G_REC + OFF_CALLS + CALL_SIZE * c + CALL_OFF_FN) with (A_G_REC + 16 + 56 * c) in VFN
  by (unfold OFF_CALLS, CALL_SIZE, CALL_OFF_FN; lia).
pose proof HLS as (L152 & L8 & L80 & L88 & L144 & L64 & L72 & L40 & L56 & L176 & L160 & L48 & L112 & L120).
pose proof HCS as (C104 & C96 & C128 & C184 & C136).
destruct (cwd_seedD Wc regsc memc sp1 c (e_Wd e + 16) (e_arr e) fn (cw_read e)
  Hr9 Hsp1b Hsp32 Hr22 Hcb HW16b HW16s Harr64 Hfnb Hrdvb
  L48 C96 C104 C128 C136 L144 L160 VFN VW16 RA1 RA2) as (HS & SHOK).
remember (Eimg (Ereg regsc (d_extra (A_G_REC + 16 + 56 * c) (e_Wd e + 16) (e_arr e) fn c (cw_read e)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc (d_extra (A_G_REC + 16 + 56 * c) (e_Wd e + 16) (e_arr e) fn c (cw_read e))) E)
  by (split; [intros n Hn; rewrite HE; apply Eimg_low; unfold A_TEXT; lia | rewrite HE; reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 A_G_REC) by (rewrite HE; exact (cwd_extra_ew regsc _ _ _ _ _ _ 0 ltac:(lia))).
assert (E33 : ew E 33 = Z_to_bv 64 (A_G_REC + 16 + 56 * c)) by (rewrite HE; exact (cwd_extra_ew regsc _ _ _ _ _ _ 1 ltac:(lia))).
assert (E35 : ew E 35 = Z_to_bv 64 (e_arr e)) by (rewrite HE; exact (cwd_extra_ew regsc _ _ _ _ _ _ 3 ltac:(lia))).
assert (E36 : ew E 36 = Z_to_bv 64 fn) by (rewrite HE; exact (cwd_extra_ew regsc _ _ _ _ _ _ 4 ltac:(lia))).
assert (E37 : ew E 37 = Z_to_bv 64 c) by (rewrite HE; exact (cwd_extra_ew regsc _ _ _ _ _ _ 5 ltac:(lia))).
assert (E38 : ew E 38 = Z_to_bv 64 (cw_read e)) by (rewrite HE; exact (cwd_extra_ew regsc _ _ _ _ _ _ 6 ltac:(lia))).
clear HE.
unfold cw_at.
(* D to the first dispatch branch (0x87fa0, fn = 20) *)
paj_run_tok RUN HS HJ SHOK DBspan; [awr_ok_tac | ].
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
pose proof (cwd_kept_run _ _ (w_H Wc) _ _ HFr ltac:(vm_compute; reflexivity)) as K1.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK DBspan.
- (* fn = 20: check_words_pin_set at 0x88028, back at the latch *)
  rewrite (cwd_eq_atom _ 36%nat fn 20 E36 ltac:(lia) ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ SHOK DBspan; [awr_ok_tac | ].
  set (mdv2 := with_vm_backing _ _ _) in *; clearbody mdv2.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into mA end.
  pose proof (cwd_kept_run _ _ (w_H Wc) _ _ HFr ltac:(vm_compute; reflexivity)) as KK.
  assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem mA) x = rdW Wc memc x)
    by (intros x Hx; rewrite (KK x Hx); exact (K1 x Hx)).
  clear HF HFr HG KK.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regsc _ [2; 3; 4; 8; 9; 22]%bv HS HAE
    ltac:(vm_compute; reflexivity)) as RK.
  assert (HCRK : cw_cregs_kept regsc (ms_regs mA)).
  { split; [exact (RK 2%bv ltac:(cbn; tauto))|]. split; [exact (RK 3%bv ltac:(cbn; tauto))|].
    split; [exact (RK 4%bv ltac:(cbn; tauto))|]. split; [exact (RK 8%bv ltac:(cbn; tauto))|].
    split; [exact (RK 9%bv ltac:(cbn; tauto)) | exact (RK 22%bv ltac:(cbn; tauto))]. }
  destruct (cw_base_kept (fx := fx) B MT LAWS TL e lyc Sc Wc regsc memc mdc (ms_regs mA) (ms_mem mA) mdv2
    pos sp1 line c Hent HC HLN HLS HCS HJ HCRK
    (cwd_mem_kept_eq _ _ sp1 (frame_addr (e_ly e) 0 pos) KEEP)) as (HC2 & HLN2 & HLS2 & HCS2).
  cwd_reg HS (1%bv : bv 5) Rra. cwd_reg HS (10%bv : bv 5) Ra0. cwd_reg HS (11%bv : bv 5) Ra1.
  cwd_reg HS (12%bv : bv 5) Ra2. cwd_reg HS (19%bv : bv 5) R19. cwd_reg HS (21%bv : bv 5) R21.
  change (SOff 240 6908) with (SOff A_TEXT 6908) in Rra. rewrite (codeptr_val _ 6908 HEI) in Rra.
  rewrite (cwd_denot_off _ 33%nat _ 0 E33), Z.add_0_r in Ra0.
  rewrite (cwd_denot_off _ 35%nat _ 0 E35), Z.add_0_r in Ra1.
  rewrite (cwd_denot_off _ 38%nat _ 0 E38), Z.add_0_r in Ra2.
  rewrite (cwd_denot_off _ 32%nat _ 0 E32), Z.add_0_r in R19.
  rewrite (cwd_denot_off _ 37%nat _ 0 E37), Z.add_0_r in R21.
  replace (A_G_REC + 16 + 56 * c) with (A_G_REC + OFF_CALLS + CALL_SIZE * c) in Ra0
    by (unfold OFF_CALLS, CALL_SIZE; lia).
  pmkst HS. rewrite cwd_sig_pin.
  rewrite Hc in Hnth.
  replace (BASE + 6908) with (BASE + CW_PC_LATCH) in Rra by (unfold CW_PC_LATCH; lia).
  exact (cwd_call_pin e lyc Sc Wc (ms_regs mA) (ms_mem mA) mdv2 pos sp1 line c args (HLH fx) (HREL fx) Hent
    HC2 HLN2 HLS2 Hnth Hcr Ra0 Ra1 Ra2 Rra R19 R21).
- (* fn <> 20 *)
  rewrite (cwd_eq_atom _ 36%nat fn 20 E36 ltac:(lia) ltac:(lia)) in Hc. apply Z.eqb_neq in Hc.
  paj_run_tok RUN HS HJ SHOK DBspan; [awr_ok_tac | ].
  set (mdv2 := with_vm_backing _ _ _) in *; clearbody mdv2.
  pose proof (cwd_kept_run _ _ (w_H Wc) _ _ HFr ltac:(vm_compute; reflexivity)) as K2.
  assert (K12 : forall x, 0 <= x < 2 ^ 64 ->
    rdW Wc (ms_mem ltac:(lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => exact m end)) x = rdW Wc memc x)
    by (intros x Hx; rewrite (K2 x Hx); exact (K1 x Hx)).
  clear HF HFr HG K2.
  psrr_branch_tok RUN BR HS SHOK DBspan.
  + (* fn = 17: check_words_chain at 0x87ffc *)
    rewrite (cwd_eq_atom _ 36%nat fn 17 E36 ltac:(lia) ltac:(lia)) in Hc0. apply Z.eqb_eq in Hc0.
    paj_run_tok RUN HS HJ SHOK DBspan; [awr_ok_tac | ].
    set (mdv3 := with_vm_backing _ _ _) in *; clearbody mdv3.
    lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into mB end.
    pose proof (cwd_kept_run _ _ (w_H Wc) _ _ HFr ltac:(vm_compute; reflexivity)) as KK.
    assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem mB) x = rdW Wc memc x)
      by (intros x Hx; rewrite (KK x Hx); exact (K12 x Hx)).
    clear HF HFr HG KK.
    pose proof (regs_kept_of_st_ok SEGS _ _ _ regsc _ [2; 3; 4; 8; 9; 22]%bv HS HAE
      ltac:(vm_compute; reflexivity)) as RK.
    assert (HCRK : cw_cregs_kept regsc (ms_regs mB)).
    { split; [exact (RK 2%bv ltac:(cbn; tauto))|]. split; [exact (RK 3%bv ltac:(cbn; tauto))|].
      split; [exact (RK 4%bv ltac:(cbn; tauto))|]. split; [exact (RK 8%bv ltac:(cbn; tauto))|].
      split; [exact (RK 9%bv ltac:(cbn; tauto)) | exact (RK 22%bv ltac:(cbn; tauto))]. }
    destruct (cw_base_kept (fx := fx) B MT LAWS TL e lyc Sc Wc regsc memc mdc (ms_regs mB) (ms_mem mB) mdv3
      pos sp1 line c Hent HC HLN HLS HCS HJ HCRK
      (cwd_mem_kept_eq _ _ sp1 (frame_addr (e_ly e) 0 pos) KEEP)) as (HC2 & HLN2 & HLS2 & HCS2).
    cwd_reg HS (1%bv : bv 5) Rra. cwd_reg HS (10%bv : bv 5) Ra0. cwd_reg HS (11%bv : bv 5) Ra1.
    cwd_reg HS (12%bv : bv 5) Ra2. cwd_reg HS (19%bv : bv 5) R19. cwd_reg HS (21%bv : bv 5) R21.
    change (SOff 240 6864) with (SOff A_TEXT 6864) in Rra. rewrite (codeptr_val _ 6864 HEI) in Rra.
    rewrite (cwd_denot_off _ 33%nat _ 0 E33), Z.add_0_r in Ra0.
    rewrite (cwd_denot_off _ 35%nat _ 0 E35), Z.add_0_r in Ra1.
    rewrite (cwd_denot_off _ 38%nat _ 0 E38), Z.add_0_r in Ra2.
    rewrite (cwd_denot_off _ 32%nat _ 0 E32), Z.add_0_r in R19.
    rewrite (cwd_denot_off _ 37%nat _ 0 E37), Z.add_0_r in R21.
    replace (A_G_REC + 16 + 56 * c) with (A_G_REC + OFF_CALLS + CALL_SIZE * c) in Ra0
      by (unfold OFF_CALLS, CALL_SIZE; lia).
    pmkst HS. rewrite cwd_sig_chain.
    rewrite Hc0 in Hnth.
    replace (BASE + 6864) with (BASE + CW_PC_RCHAIN) in Rra by (unfold CW_PC_RCHAIN; lia).
    exact (cwd_call_chain e lyc Sc Wc (ms_regs mB) (ms_mem mB) mdv3 pos sp1 line c args HLH HREL Hent
      HC2 HLN2 HLS2 Hnth Hcr Ra0 Ra1 Ra2 Rra R19 R21).
  + (* fn <> 17 *)
    rewrite (cwd_eq_atom _ 36%nat fn 17 E36 ltac:(lia) ltac:(lia)) in Hc0. apply Z.eqb_neq in Hc0.
    paj_run_tok RUN HS HJ SHOK DBspan; [awr_ok_tac | ].
    set (mdv3 := with_vm_backing _ _ _) in *; clearbody mdv3.
    pose proof (cwd_kept_run _ _ (w_H Wc) _ _ HFr ltac:(vm_compute; reflexivity)) as K3.
    assert (K13 : forall x, 0 <= x < 2 ^ 64 ->
      rdW Wc (ms_mem ltac:(lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => exact m end)) x = rdW Wc memc x)
      by (intros x Hx; rewrite (K3 x Hx); exact (K12 x Hx)).
    clear HF HFr HG K3.
    psrr_branch_tok RUN BR HS SHOK DBspan.
    * (* fn <> 0: no call of this call's fn, straight to the latch *)
      paj_run_to_tok RUNTO HS HJ SHOK DBspan CW_PC_LATCH; [awr_ok_tac | ].
      set (mdv4 := with_vm_backing _ _ _) in *; clearbody mdv4.
      lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into mD end.
      pose proof (cwd_kept_run _ _ (w_H Wc) _ _ HFr ltac:(vm_compute; reflexivity)) as K4.
      assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem mD) x = rdW Wc memc x)
        by (intros x Hx; rewrite (K4 x Hx); exact (K13 x Hx)).
      clear HF HFr HG K4.
      pose proof (regs_kept_of_st_ok_pi _ _ _ regsc _ [2; 3; 4; 8; 9; 22]%bv HS HAE
        ltac:(vm_compute; reflexivity)) as RK.
      assert (HCRK : cw_cregs_kept regsc (ms_regs mD)).
      { split; [exact (RK 2%bv ltac:(cbn; tauto))|]. split; [exact (RK 3%bv ltac:(cbn; tauto))|].
        split; [exact (RK 4%bv ltac:(cbn; tauto))|]. split; [exact (RK 8%bv ltac:(cbn; tauto))|].
        split; [exact (RK 9%bv ltac:(cbn; tauto)) | exact (RK 22%bv ltac:(cbn; tauto))]. }
      destruct (cw_base_kept (fx := fx) B MT LAWS TL e lyc Sc Wc regsc memc mdc (ms_regs mD) (ms_mem mD) mdv4
        pos sp1 line c Hent HC HLN HLS HCS HJ HCRK
        (cwd_mem_kept_eq _ _ sp1 (frame_addr (e_ly e) 0 pos) KEEP)) as (HC2 & HLN2 & HLS2 & HCS2).
      cwd_reg HS (19%bv : bv 5) R19. cwd_reg HS (21%bv : bv 5) R21.
      rewrite (cwd_denot_off _ 32%nat _ 0 E32), Z.add_0_r in R19.
      rewrite (cwd_denot_off _ 37%nat _ 0 E37), Z.add_0_r in R21.
      assert (HNC2 : aval_mem (rdW Wc (ms_mem mD)) (A_G_REC + OFF_NCALLS) 4 (cw_ncalls e)).
      { apply (cw_aval_kept (rdW Wc memc)); [|exact VNC].
        intros k Hk. apply KEEP. unfold A_G_REC, OFF_NCALLS. lia. }
      pmkst HS.
      exact (cwd_latch (fx := fx) B MT LAWS ZSH_cw CW_PC_LATCH e lyc Sc Wc (ms_regs mD) (ms_mem mD) mdv4 pos sp1 line c
        (HLH fx) (HREL fx) (or_introl eq_refl) Hent
        (conj HC2 (conj HLN2 (conj HLS2 (conj R21 Hcr)))) R19 HNC2).
    * (* fn = 0: check_words_add at 0x87fd4 *)
      rewrite (cwd_ne_atom _ 36%nat fn 0 E36 ltac:(lia) ltac:(lia)) in Hc1.
      apply Bool.negb_false_iff in Hc1. apply Z.eqb_eq in Hc1.
      paj_run_tok RUN HS HJ SHOK DBspan; [awr_ok_tac | ].
      set (mdv4 := with_vm_backing _ _ _) in *; clearbody mdv4.
      lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into mC end.
      pose proof (cwd_kept_run _ _ (w_H Wc) _ _ HFr ltac:(vm_compute; reflexivity)) as KK.
      assert (KEEP : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem mC) x = rdW Wc memc x)
        by (intros x Hx; rewrite (KK x Hx); exact (K13 x Hx)).
      clear HF HFr HG KK.
      pose proof (regs_kept_of_st_ok SEGS _ _ _ regsc _ [2; 3; 4; 8; 9; 22]%bv HS HAE
        ltac:(vm_compute; reflexivity)) as RK.
      assert (HCRK : cw_cregs_kept regsc (ms_regs mC)).
      { split; [exact (RK 2%bv ltac:(cbn; tauto))|]. split; [exact (RK 3%bv ltac:(cbn; tauto))|].
        split; [exact (RK 4%bv ltac:(cbn; tauto))|]. split; [exact (RK 8%bv ltac:(cbn; tauto))|].
        split; [exact (RK 9%bv ltac:(cbn; tauto)) | exact (RK 22%bv ltac:(cbn; tauto))]. }
      destruct (cw_base_kept (fx := fx) B MT LAWS TL e lyc Sc Wc regsc memc mdc (ms_regs mC) (ms_mem mC) mdv4
        pos sp1 line c Hent HC HLN HLS HCS HJ HCRK
        (cwd_mem_kept_eq _ _ sp1 (frame_addr (e_ly e) 0 pos) KEEP)) as (HC2 & HLN2 & HLS2 & HCS2).
      cwd_reg HS (1%bv : bv 5) Rra. cwd_reg HS (10%bv : bv 5) Ra0. cwd_reg HS (11%bv : bv 5) Ra1.
      cwd_reg HS (12%bv : bv 5) Ra2. cwd_reg HS (19%bv : bv 5) R19. cwd_reg HS (21%bv : bv 5) R21.
      change (SOff 240 6824) with (SOff A_TEXT 6824) in Rra. rewrite (codeptr_val _ 6824 HEI) in Rra.
      rewrite (cwd_denot_off _ 33%nat _ 0 E33), Z.add_0_r in Ra0.
      rewrite (cwd_denot_off _ 35%nat _ 0 E35), Z.add_0_r in Ra1.
      rewrite (cwd_denot_off _ 38%nat _ 0 E38), Z.add_0_r in Ra2.
      rewrite (cwd_denot_off _ 32%nat _ 0 E32), Z.add_0_r in R19.
      rewrite (cwd_denot_off _ 37%nat _ 0 E37), Z.add_0_r in R21.
      replace (A_G_REC + 16 + 56 * c) with (A_G_REC + OFF_CALLS + CALL_SIZE * c) in Ra0
        by (unfold OFF_CALLS, CALL_SIZE; lia).
      pmkst HS. rewrite cwd_sig_add.
      rewrite Hc1 in Hnth.
      replace (BASE + 6824) with (BASE + CW_PC_RADD) in Rra by (unfold CW_PC_RADD; lia).
      exact (cwd_call_add e lyc Sc Wc (ms_regs mC) (ms_mem mC) mdv4 pos sp1 line c args (HLH fx) (HREL fx) Hent
        HC2 HLN2 HLS2 Hnth Hcr Ra0 Ra1 Ra2 Rra R19 R21).
Qed.
End e.
End f.
End d.
