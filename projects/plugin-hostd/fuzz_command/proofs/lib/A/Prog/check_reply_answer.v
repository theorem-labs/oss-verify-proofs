(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of check_reply_answer (plugin-hostd/fuzz_command, 0x88450, 75 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close, a caller with calls). *)
(* One symbolic run per straight piece over the position-abstract listing (lib/A/Prog/CmdList.v), the inline checks
   removed by tok_load / tok_branch, the program callee through PaNoChain's cl_callS_na (neither this function nor
   sup_reply_code allocates, so no frame chain) with its statement as a Section hypothesis,
   the runtime entries through their lib/A/Rt contracts. The kit (the entry state, the call rule of a runtime entry, the
   recorder facts) is check_reply_answer_k.v.

   Three paths (the plain walk lib/Prog/check_reply_answer.v:43-185): a call answered (g_rec.answer <> 0), then
   strcmp(reply, answer) = 0 and return; none did, then sup_reply_code(reply) < 0 and return; none did and the code is
   not negative, then the five checks, w->n = 1, strcspn(w->w[0], " \t") = 4, strncmp(w->w[0], "quit", 4) = 0 and
   return. Every abort edge is refuted at its branch from the statement's answer_ok_mA. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaSB PaCall.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo
  CmdAddr CmdZsh CmdChk PaArt PaNoChain sup_reply_code_c check_reply_answer_c check_reply_answer_k.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecBase CmdRecCells CmdRecRo CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require PaLibH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* carry every atom fact ew Eo n = v (n below the bound of HAG) to the new valuation En *)
Ltac cra_carry Eo En HAG :=
  repeat match goal with
  | H : ew Eo ?nn = ?v |- _ =>
      let H2 := fresh "Hc" in
      assert (H2 : ew En nn = v) by (rewrite HAG by lia; exact H);
      clear H; rename H2 into H
  end.
(* after a run (fresh atoms from 1024 on) or a call (CLOB values from atom k on), name the valuation of HS and carry
   the atom facts below bound and the agreement HAE with the entry registers *)
Ltac cra_reenv HAE bound :=
  let Eo := lazymatch type of HAE with env_agree 32 _ ?Eo => Eo end in
  let En := lazymatch goal with
    | HS : st_ok_pi _ _ ?En _ _ |- _ => En
    | HS : st_ok _ ?En _ _ |- _ => En end in
  tryif constr_eq En Eo then idtac else (
    let HAG := fresh "HAG" in
    assert (HAG : forall nn, (nn < bound)%nat -> ew En nn = ew Eo nn)
      by (intros nn Hnn; cbn [extK]; first [apply ew_havoc_old; lia | rewrite ?ew_ewset_other by lia; reflexivity]);
    let HAE2 := fresh "HAE" in
    lazymatch type of HAE with env_agree 32 ?E0 Eo =>
      assert (HAE2 : env_agree 32 E0 En)
        by (split; [intros nn Hnn; rewrite HAG by lia; apply (proj1 HAE); exact Hnn | exact (proj2 HAE)]) end;
    clear HAE; rename HAE2 into HAE;
    let Ex := fresh "E" in
    set (Ex := En) in *;
    cra_carry Eo Ex HAG;
    clear HAG; clearbody Ex).
(* what a run of the walk keeps: every byte outside the frame [sp - 32, sp) of the stack region (atom 2) *)
Ltac cra_kept sg spv E2 UN :=
  lazymatch goal with HFr : frame_of ?Ef _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  let Hu := fresh "Hu" in
  assert (Hu : bv_unsigned (ew Ef 2) = spv) by (rewrite E2; reflexivity);
  pose proof (kept_of_frame (segs:=sg) _ _ _ _ _ (fun a => spv - 32 <= a < spv) HFr
    ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Hu in Hrr; lia|]);
          destruct Hin)) as UN;
  clear Hu end.
(* the bytes of a literal readable, from its read-only bytes L : abytes_atR rd x RO_lit_x *)
Ltac cra_lit_rd L :=
  let i := fresh "i" in let Hi := fresh "Hi" in let Hl := fresh "Hl" in
  intros i Hi;
  assert (Hl := L (Z.to_nat i) ltac:(try unfold RO_lit_210a0; try unfold RO_lit_21100; rewrite length_map; cbn [length]; lia));
  rewrite Z2Nat.id in Hl by lia; rewrite Hl; discriminate.
(* a literal's end is one of CmdRo's literal ends *)
Ltac cra_in_ends := unfold cmd_ro_ends, astr_len; repeat (first [left; vm_compute; reflexivity | right]).

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section f.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
(* the callee and the runtime entries, as the statement names them (check_reply_answer_c.v:75-78): each holds at every
   FP state, and the walk takes it at fx, the state this call runs in (its callees do not reach printf) *)
Hypothesis SRC : forall fx0 : YK11.FPState, @tsup_reply_code_spec fx0 rc SK PI B MT.
Hypothesis ASTRCMP : forall fx0 : YK11.FPState, @astrcmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis ASTRCSPN : forall fx0 : YK11.FPState, @astrcspn_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcspn) A_SSP_GOT A_SSP_GUARD.
Hypothesis ASTRNCMP : forall fx0 : YK11.FPState, @astrncmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strncmp).
(* the per-binary facts: cmd_rec_cells (CmdRecCells.v), cmd_ro_ok_of_aro and cmd_tail_vis_at (CmdRecRo.v),
   cmd_heap_tail_vis (CmdRecImg.v) and cmd_aread_ok_chk (CmdRecBase.v) are the kit's, over `SEGS B LAWS HB` and the
   image facts IMG, and RELRO in the image is IMG's cif_relro_img; IMG and SIGP (the call target of sup_reply_code
   against the listing's base, a fact of the instance PI) are walk hypotheses of the statements CmdRecFacts.v proves *)
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis SIGP : cmd_sig_prog.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

Theorem tcheck_reply_answer_spec_holds : tcheck_reply_answer_spec B MT.
Proof.
pose proof (call_strcmp_of B RLO RHI LAWS TL (ASTRCMP fx)) as CSTRCMP.
pose proof (call_strcspn_of B RLO RHI LAWS TL (ASTRCSPN fx)) as CSTRCSPN.
pose proof (call_strncmp_of B RLO RHI LAWS TL (ASTRNCMP fx)) as CSTRNCMP.
unfold tcheck_reply_answer_spec.
intros ly S W regs mem md w ww p0 n rep ans xr w0 R O
  HPRE HRO HROK HV H10 Hw64 HREC Hry Hno0 Hrep Hrep64 Htr Hans Hans64 Hta Hw8 Hwlo HWHI Hww Hww64 Hn Hnr HN1 HAOK HEV.
unfold WORDS_W in HWHI.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (proj1 (pal_env B TL)) as Herr.
assert (HSTK : CHECK_REPLY_ANSWER_STK = 12320) by reflexivity.
destruct (cra_vals HV) as (V0 & V2 & V12 & V44 & V5 & V28).
destruct (cra_rec B LAWS ly S W mem md R O xr HAR HREC Hry Hno0)
  as [(repv & nr & Hrepv & Hinr & Hnr' & Hxr & Hr4096 & Hrceil) (ansv & Hansv & Hansr & Hans0 & Hans1)].
set (wwv := ww mod 2 ^ 64). set (p0v := p0 mod 2 ^ 64).
destruct (cra_entry B LAWS TL W ly S regs mem md w ansv repv wwv n p0v HPRE HV HROK H10 Hw8 Hwlo ltac:(lia) Hansv Hansr Hrepv
  ltac:(lia)) as [HS SHOK].
pose proof (ajournal_init_na SEGS B CHECK_REPLY_ANSWER_STK [] ly S W regs mem md HPRE) as HJ.
assert (ZSHG : range_addressable (rdW W mem) SHADOW_OFF A_G_REC 960).
{ apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xada00, 0x5e3b00 - 0xada00) A_G_REC 960 HAR);
  [vm_compute; tauto | reflexivity | reflexivity | unfold A_G_REC; cbn; lia | unfold A_G_REC; cbn; lia]. }
remember (Eimg (Ereg regs (cra_extra ansv repv wwv n p0v))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs r)
by (intros k r Hk; subst E; rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5; unfold A_TEXT; lia);
    apply ew_Ereg_nat; exact Hk).
assert (E1 : ew E 1 = getr regs 1) by (apply EE; reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply EE; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EE; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EE; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 w) by (transitivity (getr regs 10); [apply EE; reflexivity | exact H10]).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 ansv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 repv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 wwv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 p0v) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (HAE : env_agree 32 (Ereg regs (cra_extra ansv repv wwv n p0v)) E)
by (rewrite HE; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E285 : ew E (A_OBJ 44) = Z_to_bv 64 A_G_REC)
by (apply bv_eq; rewrite (HEI (A_OBJ 44) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V44, unsigned_lit_small
    by (unfold A_G_REC; lia); reflexivity).
clear HE EE.
set (sp0 := spZ regs) in *.
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
assert (UB : U E Bxc = SHADOW_OFF) by (unfold Bxc; rewrite (U_atom E 32 SB E32) by (unfold SB; lia); reflexivity).
unfold cfg_at. change (w64 (BASE + AF_check_reply_answer)) with (Z_to_bv 64 (BASE + AF_check_reply_answer)).
(* entry to `beqz a1` at 0x884a8: the frame, the two g_rec checks, the loads of answer and reply *)
paj_run_tok RUN HS HJ SHOK RBspan.
1-2: cbn [ms_mem mkst]; lazymatch goal with |- range_addressable _ _ (U ?EE (SOff ?m ?c)) _ =>
  rewrite (U_atom_off EE m A_G_REC c E285) by (unfold A_G_REC; lia);
  apply (obl_of_range SEGS (w_H W) mem EE Bxc _ 8 A_G_REC 960 ZSHG UB); unfold A_G_REC; lia end.
{ awr_ok_tac. exact Usp. }
(* the run wrote only its frame [sp0 - 32, sp0) *)
cra_kept (@pa_segs _ cmd_listing PI) sp0 E2 UN1.
clear HF HFr HG Usp UB.
cra_reenv HAE 1024%nat.
assert (Hrq : forall m, 0 < m -> req_size m = m) by (intros m Hm; unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (HTS : sp0 - CHECK_REPLY_ANSWER_STK >= alloc_ceiling) by (rewrite HSTK; lia).
psrr_branch_tok RUN BR HS SHOK RBspan.
- (* g_rec.answer = 0: no call answered *)
  rewrite branch_eq_U in Hc. rewrite (U_atom _ 33 ansv E33 Hansr) in Hc.
  lazymatch type of Hc with context [U ?Ex (SLit 0)] => replace (U Ex (SLit 0)) with 0 in Hc by reflexivity end.
  apply Z.eqb_eq in Hc.
  assert (Ea : r_answer R = None).
  { destruct (r_answer R) as [xa|] eqn:Ea; [|reflexivity]. exfalso.
    destruct (Hans1 xa eq_refl) as (na & _ & _ & _ & Ha4096 & _). lia. }
  rewrite Ea in HAOK. cbn [answer_ok_mA] in HAOK. clear Hc.
  paj_run_tok RUN HS HJ SHOK RBspan.
  { awr_ok_tac. rewrite E2. reflexivity. }
  cra_kept (@pa_segs _ cmd_listing PI) sp0 E2 UN2.
  clear HF HFr HG.
  cra_reenv HAE 1024%nat.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
  rewrite E34 in Q10. rewrite E10 in Q8. rewrite E3 in Q3. rewrite E4 in Q4.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?d) _ => set (rg := r) in *; set (mm := m) in *; set (mdq := d) in * end.
  assert (Qsp : spZ rg = sp0 + -32) by (unfold spZ; rewrite Q2, E2; apply unsigned_lit_small; lia).
  assert (RV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 32 <= a < sp0) -> rdW W mm a = rdW W mem a)
    by (intros a Ha Hlt; rewrite UN2 by lia; apply UN1; lia).
  assert (HAR1 : AR SEGS B ly S W mm mdq) by exact (proj1 HJ).
  assert (SIGP_src : SIG CS_sup_reply_code = BASE + AF_sup_reply_code)
    by (rewrite (SIGP CS_sup_reply_code) by (unfold cmd_prog_syms; repeat (first [left; reflexivity | right])); reflexivity).
  rewrite SIGP_src.
  eapply SRr_bind.
  { apply (cl_callS_na B LAWS W rg mm (Z_to_bv 64 (BASE + AF_sup_reply_code)) CHECK_REPLY_ANSWER_STK sp0 [] ly S W mem md [] ly S
      mdq 0 SUP_REPLY_CODE_STK [] EV_SUP_REPLY_CODE (-32) (Z_to_bv 64 (BASE + 8152))
      (fun ly2 S2 W2 regs2 mem2 md2 => getr regs2 10 = w64 (reply_code_a xr) /\ Permutation (ablocks B ly2 S2) (ablocks B ly S) /\
         ly2 = ly /\ S2 = S)
      HJ Qsp).
    - reflexivity.
    - lia.
    - unfold SUP_REPLY_CODE_STK, ESTACK; lia.
    - rewrite HSTK; unfold SUP_REPLY_CODE_STK, ESTACK; lia.
    - rewrite Q3; exact Hgp.
    - rewrite Q4; exact Htp.
    - exact Q1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite unsigned_lit_small by lia; lia.
    - intros HPRE1. eapply SRr_mono.
      + apply (SRC fx ly S W rg mm mdq repv xr HPRE1).
        * exact (arodata_keep SEGS B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cif_relro_img _ _ IMG) HJ HRO).
        * exact Q10.
        * lia.
        * exists repv, nr. split; [exact Hinr | lia].
        * apply (astr_atR_ext (rdW W mem)); [intros k Hk; apply RV1; lia | exact Hxr].
        * apply (cmd_heap_tail_vis SEGS B LAWS HB ly S W mm mdq repv nr); [exact HAR1 | exact Hinr | rewrite Hrq by lia; lia].
        * apply (cmd_ro_ok_ext (rdW W mem)); [intros k Hk; apply RV1; lia | exact HROK].
        * exact HV.
        * exact HEV.
      + cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & Hc2 & HJc & HPr & HK).
        exists ly2, S2, regs2, mem2, md2. split; [rewrite Hc2, Q1; reflexivity|]. split; [exact HJc|]. split; [exact HPr | exact HK].
    - intros a Ha. exfalso. exact (inFP_nil a Ha). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & (Hcode & Hperm & Hly2e & HS2e)).
  assert (HJ2' : ajournal SEGS B CHECK_REPLY_ANSWER_STK sp0 [] ly S W mem md [] ly2 S2 W2 mem2 md2 0) by exact HJ2.
  clear HJ2. rename HJ2' into HJ2.
  pose proof HJ2 as (HAR2 & Hly2 & _).
  pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop2 & Eslo2 & Eshi2 & _).
  jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
  cbn [ms_mem ms_regs restrict mkst] in HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { repeat apply Forall_cons; [|apply Forall_nil].
    lazymatch goal with |- region_kept _ ?Ex _ _ _ =>
      assert (Usp2 : bv_unsigned (ew Ex 2) = sp0) by (rewrite E2; reflexivity) end.
    eapply (region_kept_stack_sub SEGS B); [exact HJc | exact HJ2 | exact Usp2 | lia | rewrite HSTK; lia | lia | cbn; lia | cbn; lia
    | intros a _ Ha; exact (inFP_nil a Ha)]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    assert (A44 : ew En 44 = Z_to_bv 64 (reply_code_a xr))
      by (change 44%nat with (40 + 4)%nat; rewrite (ew_havoc_new _ 40 _ 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia);
          cbn [nth map]; exact Hcode) end.
  lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo ?kk ?ws) _ _ =>
    assert (HEIc : img_env VAL A_LIM (havoc Eo kk ws)) by (apply img_env_havoc; [assumption | apply Nat.leb_le; vm_compute; reflexivity]) end.
  cra_reenv HAE 40%nat.
  (* the caller's struct words w->w, w->n, unchanged by the callee (they lie above this call's frame) *)
  assert (HWW : forall k, 0 <= k < 12 -> rdW W2 mem2 (w + 16 + k) = rdW W mem (w + 16 + k))
    by (intros k Hk; apply (aj_stack_kept SEGS B CHECK_REPLY_ANSWER_STK sp0 ly S W mem md [] ly2 S2 W2 mem2 md2 0); [exact HJ2 | lia | lia]).
  assert (Vww : val_mem SEGS (mrestrict (w_H W2) mem2) (w + 16) 8 wwv).
  { apply val_mem_of_aval. apply (aval_mem_ext (rdW W mem)); [intros k Hk; apply HWW; cbn in Hk; lia|].
    apply aval_mem_mod64. exact Hww. }
  assert (Vn : val_mem SEGS (mrestrict (w_H W2) mem2) (w + 24) 4 n).
  { apply val_mem_of_aval. apply (aval_mem_ext (rdW W mem)); [|exact Hn].
    intros k Hk. cbn in Hk. replace (w + 24 + k) with (w + 16 + (8 + k)) by lia. rewrite HWW by lia. f_equal; lia. }
  pose proof (st_ok_pi_add_region _ _ _ cra_words HS ltac:(vm_compute; reflexivity)) as HS3.
  match type of HS3 with ?ro -> ?dj -> _ => assert (HRO3 : ro); [|assert (HDJ3 : dj); [|specialize (HS3 HRO3 HDJ3); clear HRO3 HDJ3]] end.
  { unfold region_ok, cra_words. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
    rewrite E10, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    pose proof (Z.mod_pos_bound ww (2 ^ 64) ltac:(lia)).
    constructor; [|constructor; [|constructor]].
    - apply (chunk_ok_val SEGS _ _ w 16 8 (SOff 35 0) wwv); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold wwv; zside | zside | exact Vww].
    - apply (chunk_ok_val SEGS _ _ w 24 4 (SOff 36 0) n); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vn]. }
  { apply all_disjoint_of_extents. unfold extent_of_region, cra_words.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint ss_mem].
    unfold zdisj. cbn [fst snd].
    rewrite E2, E10, unsigned_lit_small by lia. change (bv_unsigned (getr regs 2)) with sp0. lia. }
  lazymatch type of HS3 with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS3 end.
  clear HS. rename HS3 into HS.
  clear SHOK. lazymatch goal with HS : st_ok_pi _ _ ?En _ _ |- _ =>
    assert (SHOK : sh_ok SEGS Bxc [] En (mrestrict (w_H W2) mem2)) by constructor end.
  paj_run_tok RUN HS HJ2 SHOK RBspan.
  { awr_ok_tac. rewrite E2. reflexivity. }
  clear HF HFr HG. cra_reenv HAE 1024%nat.
  psrr_branch_tok RUN BR HS SHOK RBspan.
  + (* the reply's code is negative: return *)
    paj_run_tok RUN HS HJ2 SHOK RBspan.
    { awr_ok_tac. rewrite E2. reflexivity. }
    clear HF HFr HG. cra_reenv HAE 1024%nat.
    prreg HS (1%bv : bv 5) R1.
    eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'. unfold apost_base.
    lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly2, S2, r, m, d end.
    split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
    split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|].
    split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (cra_extra ansv repv wwv n p0v) HS); [exact HAE | vm_compute; reflexivity]|].
    exact (conj Hperm (conj Hly2e HS2e)).
  + (* the code is not negative: the message is the single word quit *)
    lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hb end.
    rewrite branch_lt_S in Hb. rewrite (Sg_atom _ 44 (reply_code_a xr) A44) in Hb by (pose proof (reply_code_a_range xr); lia).
    lazymatch type of Hb with context [Sg ?Ex (SLit 0)] => replace (Sg Ex (SLit 0)) with 0 in Hb by reflexivity end.
    apply Z.ltb_ge in Hb.
    destruct HAOK as [Hneg | [Hn1 Hw0]]; [lia|].
    pose proof HJ2 as (HAR2' & Hly2' & _).
    pose proof Hly2' as (_ & _ & _ & _ & _ & _ & _ & _ & Etop2' & Eslo2' & Eshi2' & _).
    paj_run_tok RUN HS HJ2 SHOK RBspan.
    { lazymatch goal with |- range_addressable (rd_of _ (mrestrict (w_H ?Wx) ?mx)) (U ?Ex Bxc) (U ?Ex (SOff 10 ?c)) ?len =>
        rewrite (U_atom_off Ex 10 w c E10) by lia;
        assert (UBx : U Ex Bxc = SHADOW_OFF) by (unfold Bxc; rewrite (U_atom Ex 32 SB E32) by (unfold SB; lia); reflexivity);
        apply (obl_of_range SEGS (w_H Wx) mx Ex Bxc _ len (w + 16) 12); [| exact UBx | lia | lia];
        apply (stack_addressable SEGS B LAWS ly2 S2 Wx mx _ (w + 16) 12 HAR2'); lia end. }
    { awr_ok_tac. rewrite E2. reflexivity. }
    clear HF HFr HG. cra_reenv HAE 1024%nat.
    psrr_branch_tok RUN BR HS SHOK RBspan.
    * (* w->n <> 1: refuted *)
      exfalso. lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hb2 end.
      rewrite branch_ne_U in Hb2.
      rewrite (U_sext32_small _ (SOff 36 0) n (U_atom _ 36 n E36 ltac:(lia))) in Hb2 by lia.
      lazymatch type of Hb2 with context [U ?Ex (SLit 1)] => replace (U Ex (SLit 1)) with 1 in Hb2 by reflexivity end.
      rewrite Hn1 in Hb2. discriminate Hb2.
    * (* w->n = 1: the word *)
      destruct (HN1 Hn1) as ((pw & kw & Hinw & Hpw & Hpwk) & Hww8 & Hp0m & Hp064 & (pc & kc & Hinc & Hpc & Hpck) & Hw0s & _).
      destruct (al_blocks _ _ LAWS ly S W mem md pw kw HAR Hinw) as (_ & Hpw4096 & Hpwc & _).
      destruct (al_blocks _ _ LAWS ly S W mem md pc kc HAR Hinc) as (_ & Hpc4096 & Hpcc & _).
      assert (Hrqw : kw <= req_size kw) by (unfold req_size; destruct (Z.eqb_spec kw 0); lia).
      assert (Hrqc : kc <= req_size kc) by (unfold req_size; destruct (Z.eqb_spec kc 0); lia).
      assert (Hwweq : wwv = ww) by (unfold wwv; apply Z.mod_small; lia).
      assert (Hp0eq : p0v = p0) by (unfold p0v; apply Z.mod_small; lia).
      assert (Hinw2 : In (pw, kw) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hinw).
      assert (Hinc2 : In (pc, kc) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hinc).
      (* the word w->w[0] lies in the live `copy` block (pc, kc) with its NUL (the statement's in_blockA, :112): the
         `+ 8` band room the strcspn and strncmp contracts ask past it (RtString.v:165, :128) *)
      assert (HM0 : amem_range p0v (astr_len w0 + 8)).
      { apply (PaLibH.amem8_of_blockA SEGS B LAWS ly S W mem md p0v (astr_len w0) HAR); [|unfold astr_len; lia].
        exists pc, kc. split; [exact Hinc | unfold astr_len; lia]. }
      lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
        pose proof (st_ok_pi_add_fact En _ _ 35 (mkAF 4096 (0x7fffff800000 - 8) 0) HS) as HS4 end.
      match type of HS4 with ?af -> _ => assert (HAF : af); [|specialize (HS4 HAF); clear HAF] end.
      { unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E35, unsigned_lit_small by (rewrite Hwweq; lia).
        rewrite Z.pow_0_r, Z.mod_1_r. rewrite Hwweq. lia. }
      lazymatch type of HS4 with st_ok_pi _ _ _ ?ss4 _ => let v := eval vm_compute in ss4 in change ss4 with v in HS4 end.
      clear HS. rename HS4 into HS.
      lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict (w_H _) ?msx) |- _ => set (m3 := ms_mem msx) in * end.
      assert (Vp0 : val_mem SEGS (mrestrict (w_H W2) m3) ww 8 p0v).
      { apply val_mem_of_aval. apply (aval_mem_ext (rdW W mem)).
        - intros k Hk. cbn in Hk. eapply (aj_heap_kept SEGS B CHECK_REPLY_ANSWER_STK sp0 ly S W mem md [] ly2 S2 W2 m3 _ 0 pw kw);
          [exact HJ2 | exact Hinw | exact Hinw2 | lia].
        - apply aval_mem_mod64. exact Hp0m. }
      pose proof (st_ok_pi_add_region _ _ _ cra_warr HS ltac:(vm_compute; reflexivity)) as HS3.
      match type of HS3 with ?ro -> ?dj -> _ => assert (HRO3 : ro); [|assert (HDJ3 : dj); [|specialize (HS3 HRO3 HDJ3); clear HRO3 HDJ3]] end.
      { unfold region_ok, cra_warr. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
        rewrite E35, unsigned_lit_small by (rewrite Hwweq; lia). rewrite Hwweq.
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        pose proof (Z.mod_pos_bound p0 (2 ^ 64) ltac:(lia)).
        constructor; [|constructor].
        apply (chunk_ok_val SEGS _ _ ww 0 8 (SOff 37 0) p0v); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold p0v; zside | zside |].
        rewrite Z.add_0_r. exact Vp0. }
      { apply all_disjoint_of_extents. unfold extent_of_region, cra_warr.
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint ss_mem].
        unfold zdisj. cbn [fst snd].
        rewrite E2, E10, E35, !unsigned_lit_small by (rewrite ?Hwweq; lia). rewrite Hwweq. change (bv_unsigned (getr regs 2)) with sp0. lia. }
      lazymatch type of HS3 with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS3 end.
      clear HS. rename HS3 into HS.
      pose proof HJ2 as (HAR3 & _).
      paj_run_tok RUN HS HJ2 SHOK RBspan.
      1-2: first
        [ lazymatch goal with |- range_addressable (rd_of _ (mrestrict (w_H ?Wx) ?mx)) (U ?Ex Bxc) (U ?Ex (SOff 10 ?c)) ?len =>
            rewrite (U_atom_off Ex 10 w c E10) by lia;
            assert (UBx : U Ex Bxc = SHADOW_OFF) by (unfold Bxc; rewrite (U_atom Ex 32 SB E32) by (unfold SB; lia); reflexivity);
            apply (obl_of_range SEGS (w_H Wx) mx Ex Bxc _ len (w + 16) 12); [| exact UBx | lia | lia];
            apply (stack_addressable SEGS B LAWS ly2 S2 Wx mx _ (w + 16) 12 HAR3); lia end
        | lazymatch goal with |- range_addressable (rd_of _ (mrestrict (w_H ?Wx) ?mx)) (U ?Ex Bxc) (U ?Ex (SOff 35 0)) ?len =>
            rewrite (U_atom Ex 35 wwv E35) by (rewrite Hwweq; lia); rewrite Hwweq;
            assert (UBx : U Ex Bxc = SHADOW_OFF) by (unfold Bxc; rewrite (U_atom Ex 32 SB E32) by (unfold SB; lia); reflexivity);
            apply (obl_of_block SEGS B LAWS ly2 S2 Wx mx _ Ex Bxc ww len pw kw HAR3 Hinw2 UBx); lia end ].
      { awr_ok_tac. rewrite E2. reflexivity. }
      clear HF HFr HG. cra_reenv HAE 1024%nat.
      pmkst HS.
      prreg HS (1%bv : bv 5) K1. prreg HS (2%bv : bv 5) K2. prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4.
      prreg HS (10%bv : bv 5) K10. prreg HS (11%bv : bv 5) K11.
      rewrite E37 in K10. rewrite E3 in K3. rewrite E4 in K4.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?d) _ => set (rg1 := r) in *; set (mm1 := m) in *; set (mdq1 := d) in * end.
      assert (Ksp : spZ rg1 = sp0 + -32) by (unfold spZ; rewrite K2, E2; apply unsigned_lit_small; lia).
      assert (K11' : getr rg1 11 = w64 0x210a0).
      { rewrite K11. lazymatch goal with |- context [ew ?Ex 246%nat] =>
          lazymatch goal with H : img_env _ _ Ex |- _ => pose proof (H (A_OBJ 5) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as HV246 end end.
        rewrite V5 in HV246. change (A_OBJ 5) with 246%nat in HV246.
        unfold w64. apply bv_eq. rewrite HV246. rewrite ?Z.add_0_r. repeat (rewrite unsigned_lit_small by lia). reflexivity. }
      assert (HARc : AR SEGS B ly2 S2 W2 mm1 mdq1) by exact (proj1 HJ2).
      assert (Hw0len : Z.of_nat (length w0) = 4) by (rewrite Hw0; reflexivity).
      assert (HROc : arodata_okP SEGS RLO RHI B (rdW W2 mm1)) by exact (arodata_keep SEGS B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cif_relro_img _ _ IMG) HJ2 HRO).
      destruct (cmd_ro_lits _ (cmd_ro_ok_of_aro SEGS B LAWS HB IMG ly2 S2 W2 mm1 mdq1 HARc HROc)) as [L210 _].
      assert (Sp0 : astr_at SEGS W2 mm1 p0v w0).
      { apply (proj1 (astr_atR_view SEGS W2 mm1 p0v w0)). rewrite Hp0eq.
        apply (astr_atR_ext (rdW W mem)); [|exact Hw0s].
        intros k Hk. eapply (aj_heap_kept SEGS B CHECK_REPLY_ANSWER_STK sp0 ly S W mem md [] ly2 S2 W2 mm1 _ 0 pc kc);
        [exact HJ2 | exact Hinc | exact Hinc2 | lia]. }
      assert (Sset : astr_at SEGS W2 mm1 0x210a0 [Z_to_bv 8 32; Z_to_bv 8 9]).
      { apply (proj1 (astr_atR_view SEGS W2 mm1 _ _)).
        split; [exact L210 | cbn; intros [H|[H|[]]]; apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H]. }
      destruct (cmd_aread_ok_chk SEGS B LAWS HB ly2 S2 W2 mm1 mdq1 0x210a0 3 HARc ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
        as [RA3 HV3].
      eapply SRr_bind.
      { eapply (CSTRCSPN p0v 0x210a0 w0 [Z_to_bv 8 32; Z_to_bv 8 9] W2 rg1 mm1 CHECK_REPLY_ANSWER_STK sp0 [] ly S W mem md []
          ly2 S2 mdq1 0 (-32) _ HJ2).
        - exact HROc.
        - exact Ksp.
        - reflexivity.
        - lia.
        - rewrite HSTK; unfold ESTACK; lia.
        - rewrite K3; exact Hgp.
        - rewrite K4; exact Htp.
        - exact K1.
        - apply ret_ok_codeptr_v; [lia | reflexivity].
        - split; [destruct (cmd_rec_cells SEGS B LAWS HB IMG ly2 S2 W2 mm1 mdq1 HARc) as (_ & Hg & _); exact Hg|].
          split; [exact K10|]. split; [exact K11'|]. split; [lia|]. split; [lia|].
          split; [exact Sp0|]. split; [exact Sset|].
          split; [apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) ly2 S2 W2 rg1 mm1 mdq1 pc kc p0v _ HARc Hinc2); unfold astr_len;
                  [lia | lia | lia | rewrite Ksp; unfold ESTACK; lia]|].
          split; [exact HM0|].
          split; [apply (lit_aread SEGS W2 mm1 rg1 (2 * ESTACK) 0x210a0 _); unfold astr_len; cbn [length Z.of_nat];
                  [lia | lia | lia | exact RA3 | exact HV3 | cra_lit_rd L210 | rewrite Ksp; unfold ESTACK; lia]|].
          (* the set " \t" in .rodata (0x210a0, 2 bytes): low band *)
          split; [exact (PaLibH.amem8_of_low 0x210a0 2 ltac:(lia) ltac:(unfold kLowMemEnd; lia))|].
          split; [apply (cmd_heap_tail_vis SEGS B LAWS HB ly2 S2 W2 mm1 mdq1 pc kc); [exact HARc | exact Hinc2 | unfold astr_len; lia]|].
          apply (cmd_tail_vis_at SEGS B LAWS HB IMG ly2 S2 W2 mm1 mdq1 _ HARc). cra_in_ends. }
      cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HQ3 & HK3).
      assert (A0 : getr regs3 10 = w64 4) by (rewrite HQ3, Hw0; reflexivity).
      pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPs3 & _).
      jafter_call_keep_pi HS 56%nat regs3 (mrestrict (w_H W2) mem3) HP3 [2]%nat HS2.
      cbn [ms_mem ms_regs restrict mkst] in HS2.
      match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
      { repeat apply Forall_cons; [|apply Forall_nil].
        apply (region_kept_win SEGS _ (w_H W2) mm1 mem3 2 sp0).
        - rewrite E2. reflexivity.
        - intros a Ha. apply HK3; unfold ESTACK; lia.
        - intros a Ha. apply HPs3. rewrite HSTK. lia. }
      clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
      lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
        assert (A60 : ew En 60 = Z_to_bv 64 4)
          by (change 60%nat with (56 + 4)%nat; rewrite (ew_havoc_new _ 56 _ 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia);
              cbn [nth map]; exact A0) end.
      lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo ?kk ?ws) _ _ =>
        assert (HEIc2 : img_env VAL A_LIM (havoc Eo kk ws)) by (apply img_env_havoc; [assumption | apply Nat.leb_le; vm_compute; reflexivity]) end.
      cra_reenv HAE 56%nat.
      clear SHOK. lazymatch goal with HS : st_ok_pi _ _ ?En _ _ |- _ =>
        assert (SHOK : sh_ok SEGS Bxc [] En (mrestrict (w_H W2) mem3)) by constructor end.
      paj_run_tok RUN HS HJ3 SHOK RBspan.
      { awr_ok_tac. rewrite E2. reflexivity. }
      clear HF HFr HG. cra_reenv HAE 1024%nat.
      psrr_branch_tok RUN BR HS SHOK RBspan.
      -- (* strcspn <> 4: refuted, the word is quit *)
        exfalso. lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hb3 end.
        rewrite branch_ne_U in Hb3. rewrite (U_atom _ 60 4 A60) in Hb3 by lia.
        lazymatch type of Hb3 with context [U ?Ex (SLit 4)] => replace (U Ex (SLit 4)) with 4 in Hb3 by reflexivity end.
        discriminate Hb3.
      -- (* strcspn = 4: strncmp(w0, "quit", 4) *)
        paj_run_tok RUN HS HJ3 SHOK RBspan.
        { awr_ok_tac. rewrite E2. reflexivity. }
        clear HF HFr HG. cra_reenv HAE 1024%nat.
        pmkst HS.
        prreg HS (1%bv : bv 5) M1. prreg HS (2%bv : bv 5) M2. prreg HS (3%bv : bv 5) M3. prreg HS (4%bv : bv 5) M4.
        prreg HS (10%bv : bv 5) M10. prreg HS (11%bv : bv 5) M11. prreg HS (12%bv : bv 5) M12.
        rewrite E37 in M10. rewrite E3 in M3. rewrite E4 in M4.
        lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?d) _ => set (rg2 := r) in *; set (mm2 := m) in *; set (mdq2 := d) in * end.
        assert (Msp : spZ rg2 = sp0 + -32) by (unfold spZ; rewrite M2, E2; apply unsigned_lit_small; lia).
        assert (M11' : getr rg2 11 = w64 0x21100).
        { rewrite M11. lazymatch goal with |- context [ew ?Ex 269%nat] =>
            lazymatch goal with H : img_env _ _ Ex |- _ => pose proof (H (A_OBJ 28) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) as HV269 end end.
          rewrite V28 in HV269. change (A_OBJ 28) with 269%nat in HV269.
          unfold w64. apply bv_eq. rewrite HV269. rewrite ?Z.add_0_r. repeat (rewrite unsigned_lit_small by lia). reflexivity. }
        assert (HARm : AR SEGS B ly2 S2 W2 mm2 mdq2) by exact (proj1 HJ3).
        assert (HROm : arodata_okP SEGS RLO RHI B (rdW W2 mm2)) by exact (arodata_keep SEGS B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cif_relro_img _ _ IMG) HJ3 HRO).
        destruct (cmd_ro_lits _ (cmd_ro_ok_of_aro SEGS B LAWS HB IMG ly2 S2 W2 mm2 mdq2 HARm HROm)) as [_ L211].
        assert (Sp0' : astr_at SEGS W2 mm2 p0v w0).
        { apply (proj1 (astr_atR_view SEGS W2 mm2 p0v w0)). rewrite Hp0eq.
          apply (astr_atR_ext (rdW W mem)); [|exact Hw0s].
          intros k Hk. eapply (aj_heap_kept SEGS B CHECK_REPLY_ANSWER_STK sp0 ly S W mem md [] ly2 S2 W2 mm2 _ 0 pc kc);
          [exact HJ3 | exact Hinc | exact Hinc2 | lia]. }
        assert (Squit : astr_at SEGS W2 mm2 0x21100 [Z_to_bv 8 113; Z_to_bv 8 117; Z_to_bv 8 105; Z_to_bv 8 116]).
        { apply (proj1 (astr_atR_view SEGS W2 mm2 _ _)).
          split; [exact L211 | cbn; intros [H|[H|[H|[H|[]]]]]; apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H]. }
        destruct (cmd_aread_ok_chk SEGS B LAWS HB ly2 S2 W2 mm2 mdq2 0x21100 5 HARm ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
          as [RA5 HV5].
        eapply SRr_bind.
        { eapply (CSTRNCMP p0v 0x21100 4 w0 [Z_to_bv 8 113; Z_to_bv 8 117; Z_to_bv 8 105; Z_to_bv 8 116] W2 rg2 mm2
            CHECK_REPLY_ANSWER_STK sp0 [] ly S W mem md [] ly2 S2 mdq2 0 (-32) _ HJ3).
          - exact HROm.
          - exact Msp.
          - reflexivity.
          - lia.
          - rewrite HSTK; unfold ESTACK; lia.
          - rewrite M3; exact Hgp.
          - rewrite M4; exact Htp.
          - exact M1.
          - apply ret_ok_codeptr_v; [lia | reflexivity].
          - split; [exact M10|]. split; [exact M11'|]. split; [exact M12|]. split; [lia|]. split; [lia|]. split; [lia|].
            split; [exact Sp0'|]. split; [exact Squit|].
            split; [apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) ly2 S2 W2 rg2 mm2 mdq2 pc kc p0v _ HARm Hinc2); unfold astr_len;
                    [lia | lia | lia | rewrite Msp; unfold ESTACK; lia]|].
            split; [exact HM0|].
            split; [apply (lit_aread SEGS W2 mm2 rg2 (2 * ESTACK) 0x21100 _); unfold astr_len; cbn [length Z.of_nat Z.min];
                    [lia | lia | lia | intros y Hy; apply RA5; lia
                    | apply (shadow_hull_vis_le _ 0x21100 5); [lia | lia | exact HV5]
                    | cra_lit_rd L211
                    | rewrite Msp; unfold ESTACK; lia]|].
            (* "quit" in .rodata (0x21100, 4 bytes): low band *)
            split; [exact (PaLibH.amem8_of_low 0x21100 4 ltac:(lia) ltac:(unfold kLowMemEnd; lia))|].
            split; [apply (cmd_heap_tail_vis SEGS B LAWS HB ly2 S2 W2 mm2 mdq2 pc kc); [exact HARm | exact Hinc2 | unfold astr_len; lia]|].
            apply (cmd_tail_vis_at SEGS B LAWS HB IMG ly2 S2 W2 mm2 mdq2 _ HARm). cra_in_ends. }
        cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HQ4 & HK4).
        assert (A0' : getr regs4 10 = w64 0) by (apply (proj2 HQ4); rewrite Hw0; vm_compute; reflexivity).
        pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPs4 & _).
        jafter_call_keep_pi HS 72%nat regs4 (mrestrict (w_H W2) mem4) HP4 [0]%nat HS2.
        cbn [ms_mem ms_regs restrict mkst] in HS2.
        match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
        { repeat apply Forall_cons; [|apply Forall_nil].
          apply (region_kept_win SEGS _ (w_H W2) mm2 mem4 2 sp0).
          - rewrite E2. reflexivity.
          - intros a Ha. apply HK4; unfold ESTACK; lia.
          - intros a Ha. apply HPs4. rewrite HSTK. lia. }
        clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
        lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
          assert (A76 : ew En 76 = Z_to_bv 64 0)
            by (change 76%nat with (72 + 4)%nat; rewrite (ew_havoc_new _ 72 _ 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia);
                cbn [nth map]; exact A0') end.
        lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo ?kk ?ws) _ _ =>
          assert (HEIc3 : img_env VAL A_LIM (havoc Eo kk ws)) by (apply img_env_havoc; [assumption | apply Nat.leb_le; vm_compute; reflexivity]) end.
        cra_reenv HAE 72%nat.
        clear SHOK. lazymatch goal with HS : st_ok_pi _ _ ?En _ _ |- _ =>
          assert (SHOK : sh_ok SEGS Bxc [] En (mrestrict (w_H W2) mem4)) by constructor end.
        paj_run_tok RUN HS HJ4 SHOK RBspan.
        { awr_ok_tac. rewrite E2. reflexivity. }
        clear HF HFr HG. cra_reenv HAE 1024%nat.
        psrr_branch_tok RUN BR HS SHOK RBspan.
        ++ (* strncmp <> 0: refuted *)
          exfalso. lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hb4 end.
          rewrite branch_ne_U in Hb4. rewrite (U_atom _ 76 0 A76) in Hb4 by lia.
          lazymatch type of Hb4 with context [U ?Ex (SLit 0)] => replace (U Ex (SLit 0)) with 0 in Hb4 by reflexivity end.
          discriminate Hb4.
        ++ (* strncmp = 0: return *)
          paj_run_tok RUN HS HJ4 SHOK RBspan.
          { awr_ok_tac. rewrite E2. reflexivity. }
          clear HF HFr HG. cra_reenv HAE 1024%nat.
          prreg HS (1%bv : bv 5) R1.
          eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
          intros mat'. unfold apost_base.
          lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly2, S2, r, m, d end.
          split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
          split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ4|].
          split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (cra_extra ansv repv wwv n p0v) HS); [exact HAE | vm_compute; reflexivity]|].
          exact (conj Hperm (conj Hly2e HS2e)).
- (* g_rec.answer <> 0: a call answered, strcmp(reply, answer) *)
  rewrite branch_eq_U in Hc. rewrite (U_atom _ 33 ansv E33 Hansr) in Hc.
  replace (U _ (SLit 0)) with 0 in Hc by reflexivity. apply Z.eqb_neq in Hc.
  destruct (r_answer R) as [xa|] eqn:Ea; [|exfalso; exact (Hc (Hans0 eq_refl))].
  destruct (Hans1 xa eq_refl) as (na & Hina & Hna & Hxa & Ha4096 & Haceil).
  cbn [answer_ok_mA] in HAOK.
  paj_run_tok RUN HS HJ SHOK RBspan.
  { awr_ok_tac. rewrite E2. reflexivity. }
  cra_kept (@pa_segs _ cmd_listing PI) sp0 E2 UN2.
  clear HF HFr HG.
  cra_reenv HAE 1024%nat.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  rewrite E34 in Q10. rewrite E33 in Q11. rewrite E3 in Q3. rewrite E4 in Q4.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r _ ?m _) ?d) _ => set (rg := r) in *; set (mm := m) in *; set (mdq := d) in * end.
  assert (Qsp : spZ rg = sp0 + -32) by (unfold spZ; rewrite Q2, E2; apply unsigned_lit_small; lia).
  assert (RV1 : forall a, 0 <= a < 2 ^ 64 -> a < sp0 - 32 -> rdW W mm a = rdW W mem a)
    by (intros a Ha Hlt; rewrite UN2 by lia; apply UN1; lia).
  assert (HAR1 : AR SEGS B ly S W mm mdq) by exact (proj1 HJ).
  eapply SRr_bind.
  { apply (CSTRCMP repv ansv xr xa W rg mm CHECK_REPLY_ANSWER_STK sp0 [] ly S W mem md [] ly S mdq 0 (-32)
      (Z_to_bv 64 (BASE + 8140)) HJ).
    - exact (arodata_keep SEGS B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ (cif_relro_img _ _ IMG) HJ HRO).
    - exact Qsp.
    - reflexivity.
    - lia.
    - rewrite HSTK; unfold ESTACK; lia.
    - rewrite Q3; exact Hgp.
    - rewrite Q4; exact Htp.
    - exact Q1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - split; [exact Q10|]. split; [exact Q11|]. split; [lia|]. split; [lia|].
      split; [apply (proj1 (astr_atR_view SEGS W mm repv xr)); apply (astr_atR_ext (rdW W mem)); [intros k Hk; apply RV1; lia | exact Hxr]|].
      split; [apply (proj1 (astr_atR_view SEGS W mm ansv xa)); apply (astr_atR_ext (rdW W mem)); [intros k Hk; apply RV1; lia | exact Hxa]|].
      split; [apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) ly S W rg mm mdq repv nr repv _ HAR1 Hinr); unfold astr_len;
              [lia | lia | lia | rewrite Qsp; unfold ESTACK; lia]|].
      split; [apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) ly S W rg mm mdq ansv na ansv _ HAR1 Hina); unfold astr_len;
              [lia | lia | lia | rewrite Qsp; unfold ESTACK; lia]|].
      split; [apply (cmd_heap_tail_vis SEGS B LAWS HB ly S W mm mdq repv nr); [exact HAR1 | exact Hinr | rewrite Hrq by lia; unfold astr_len; lia]|].
      apply (cmd_heap_tail_vis SEGS B LAWS HB ly S W mm mdq ansv na); [exact HAR1 | exact Hina | rewrite Hrq by lia; unfold astr_len; lia]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
  assert (A0 : getr regs2 10 = w64 0) by (apply (proj2 HQ2); exact HAOK).
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPs2 & _).
  jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
  cbn [ms_mem ms_regs restrict mkst] in HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { repeat apply Forall_cons; [|apply Forall_nil].
    apply (region_kept_win SEGS _ (w_H W) mm mem2 2 sp0).
    - rewrite E2. reflexivity.
    - intros a Ha. apply HK2; unfold ESTACK; lia.
    - intros a Ha. apply HPs2. rewrite HSTK. lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    assert (A44 : ew En 44 = Z_to_bv 64 0)
      by (change 44%nat with (40 + 4)%nat; rewrite (ew_havoc_new _ 40 _ 4 (Z_to_bv 64 0)) by (rewrite length_map; cbn; lia);
          cbn [nth map]; exact A0) end.
  lazymatch type of HS with st_ok_pi _ _ (havoc ?Eo ?kk ?ws) _ _ =>
    assert (HEIc : img_env VAL A_LIM (havoc Eo kk ws)) by (apply img_env_havoc; [assumption | apply Nat.leb_le; vm_compute; reflexivity]) end.
  cra_reenv HAE 40%nat.
  clear SHOK. lazymatch goal with HS : st_ok_pi _ _ ?En _ _ |- _ =>
    assert (SHOK : sh_ok SEGS Bxc [] En (mrestrict (w_H W) mem2)) by constructor end.
  paj_run_tok RUN HS HJ2 SHOK RBspan.
  { awr_ok_tac. rewrite E2. reflexivity. }
  clear HF HFr HG. cra_reenv HAE 1024%nat.
  psrr_branch_tok RUN BR HS SHOK RBspan.
  + (* strcmp returned 0: return *)
    paj_run_tok RUN HS HJ2 SHOK RBspan.
    { awr_ok_tac. rewrite E2. reflexivity. }
    clear HF HFr HG. cra_reenv HAE 1024%nat.
    prreg HS (1%bv : bv 5) R1.
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'. unfold apost_base.
    lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
    split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
    split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|].
    split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (cra_extra ansv repv wwv n p0v) HS); [exact HAE | vm_compute; reflexivity]|].
    split; [apply Permutation_refl | split; reflexivity].
  + (* strcmp returned non-zero: refuted, the reply is the answer *)
    exfalso. rewrite branch_eq_U in Hc0. rewrite (U_atom _ 44 0 A44) in Hc0 by lia.
    lazymatch type of Hc0 with context [U ?Ex (SLit 0)] => replace (U Ex (SLit 0)) with 0 in Hc0 by reflexivity end.
    discriminate Hc0.
Qed.
End f.
End e.
End c.
