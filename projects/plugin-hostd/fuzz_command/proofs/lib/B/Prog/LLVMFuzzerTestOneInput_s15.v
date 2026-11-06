(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment A of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86588 .. 0x86654: g_rec's address, the checked inline zero stores of g_rec.state and g_rec.host_settings, the frame words of the top loop, s0 := -1, s1 := 0, s11 := 32, a5 := 1, the mask, the fall into the loop head), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s15.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (a segment from a point of the function to its continuation) and A/ACbk.v (the walk: a run, the continuation statement applied). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibF PaLibG PaSB CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo CmdAddr CmdChk
  CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s01 LLVMFuzzerTestOneInput_s16.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the per-binary facts, with the names of a Theorem Labs lane's RULING-STMT.md section 1; the segment reaches no callee and no
   runtime entry *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis VOBJS : cmd_val_objs.
Let RUNTO := paj_run_to B LAWS.

Lemma lt_seg_A : LTA_LH B MT 0 -> LT_A_stmt B MT.
Proof.
intros HLHA. pose proof (HLHA fx) as HLH. clear HLHA.
intros cx ly S W regs mem md k acc R HB0 Hfrm HFR R25 R23 R24 HREC Hcl Han Hrp Hnr HBUD.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (GR : A_G_REC = 0x5e32c0) by reflexivity.
pose proof HB0 as (HPRE0 & _ & _ & _ & _ & _ & Hpn & Hlen & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : LTOI_STK = 32768) by reflexivity.
pose proof HFR as (HJ & Hsp & R3 & R4 & HSAV).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPJ & _).
pose proof HREC as (_ & Hsp0 & _).
assert (Hsp1 : spZ regs = x_sp0 cx - 256) by (rewrite Hsp; unfold x_sp1, x_sp0, LT_FRAME; reflexivity).
assert (SP0 : alloc_ceiling + 32768 <= x_sp0 cx <= 2 ^ 47) by (unfold x_sp0; rewrite WS in Hslo; lia).
assert (Rn : 0 <= x_n cx < 2 ^ 64) by (destruct Hpn as [[Hn0 _] | [Hn0 _]]; lia).
(* the GOT words the segment reads, at its start: cmd_ro_ok carried along the journal (_s01.v lt_ro_kept) *)
destruct (la_ro_vals _ (lt_ro_kept B MT LAWS HB IMG cx ly S W mem md [] k HB0 HJ)) as (G2 & G3 & G4).
(* the symbolic state at 0x86588 *)
assert (HS : st_ok_pi SEGS VAL (la_E regs) ss_la
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_RC1RA)) mem (seg_rom SEGS)))).
{ apply (la_seed B LAWS HB PRW VOBJS W regs mem); [lia | lia | | | exact R25 | exact G2 | exact G3 | exact G4].
  - rewrite Hsp1. replace (x_sp0 cx - 256) with (x_sp0 cx + (-16) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
  - intros a Ha. apply HPJ. rewrite WS. lia. }
assert (HEI : img_env VAL A_LIM (la_E regs)) by (unfold la_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew (la_E regs) n = ew (Ereg regs la_extra) n)
  by (intros n Hn; unfold la_E; apply Eimg_low; exact Hn).
remember (la_E regs) as E eqn:HE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EEo; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EEo; reflexivity).
assert (E23 : ew E 23 = Z_to_bv 64 (x_p cx)) by (rewrite (EEo 23%nat 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = Z_to_bv 64 (x_n cx)) by (rewrite (EEo 24%nat 24%bv eq_refl); exact R24).
assert (E25 : ew E 25 = Z_to_bv 64 LT_SB) by (rewrite (EEo 25%nat 25%bv eq_refl); exact R25).
assert (E32 : ew E 32 = Z_to_bv 64 LA_NC) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EO44 : ew E 285 = Z_to_bv 64 A_G_REC)
  by (exact (la_ew_obj VOBJS E 44 A_G_REC HEI ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(unfold A_OBJ, A_LIM; lia))).
assert (EO40 : ew E 281 = Z_to_bv 64 LT_CODES)
  by (exact (la_ew_obj VOBJS E 40 LT_CODES HEI ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(unfold A_OBJ, A_LIM; lia))).
assert (EGu : bv_unsigned (ew E 285) = A_G_REC) by (rewrite EO44; apply unsigned_lit_small; rewrite GR; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (UspA : bv_unsigned (ew E 2) = x_sp0 cx + -256) by (rewrite Usp, Hsp1; lia).
pose proof (la_shok B LAWS HB ly S W mem md E HAR E25 EO44) as SHOK.
clear HE EL.
(* 0x86588 .. 0x86650: s10 := &g_rec (GOT 0xa6bc8); the store8 checks of g_rec.state and g_rec.host_settings (their
   shadow cells saved at sp + 104 and sp + 96) vanish by la_SH, the two zero stores; s1 := 0, a5 := 1, s11 := 32,
   s0 := -1, s2 := the mask, &rec_ncodes (GOT 0xa6bd0), rec_codes (GOT 0xa6bd8) and the frame words; on to the loop
   head 0x86654 *)
paj_run_to_tok RUNTO HS HJ SHOK LAspan 0x124.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -256);
    [reflexivity | exact UspA | cbn [YP09.r_wlo]; unfold LTOI_STK, LLVMF_STK; lia | cbn [YP09.r_whi]; lia |].
  do 3 (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]).
  eapply awr_ok_cons_gen; [reflexivity | exact EGu | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. apply (la_awr_grec B HB IMG). lia. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv1 := d) in *; clearbody mdv1 end.
(* the run writes the frame words at sp + 0 .. 112 and g_rec.state, g_rec.host_settings; every other byte is kept *)
lazymatch goal with Hfr : frame_of E _ (mrestrict _ mem) (mrestrict _ ?m1) |- _ =>
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 ->
    ~ (x_sp0 cx - 256 <= a < x_sp0 cx - 144 \/ A_G_REC + 944 <= a < A_G_REC + 960) -> rdW W m1 a = rdW W mem a);
  [ intros a Ha Hn; apply (kept_of_frame (segs := SEGS) _ _ _ _ _
      (fun a => x_sp0 cx - 256 <= a < x_sp0 cx - 144 \/ A_G_REC + 944 <= a < A_G_REC + 960) Hfr);
    [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?UspA, ?EGu in Hrr;
        cbv beta; clear - Hrr; lia|]);
      destruct Hin
    | exact Ha | exact Hn ]
  | ] end.
clear HF HFr HG.
pmkst HS.
prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
prreg HS (9%bv : bv 5) F9. prreg HS (15%bv : bv 5) F15. prreg HS (18%bv : bv 5) F18. prreg HS (23%bv : bv 5) F23.
prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl) as HRF. cbn [ms_mem restrict] in HRF.
pose proof (st_ok_pi_region_nth _ _ _ 4%nat _ HS eq_refl) as HRG. cbn [ms_mem restrict] in HRG.
pose proof (la_slots_of_region E W _ (x_sp1 cx) HRF ltac:(rewrite Usp; exact Hsp) EO44 EO40 E25 E32) as HSL.
pose proof (la_zero_of_region E W _ HRG EGu) as Z16m.
change (BASE + 292) with (BASE + LO_LH).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?d3) _ =>
  apply (HLH cx ly S W r3 m3 d3 k acc (x_n cx) (lt_Rz R) [] 0); [exact HB0 | exact Hfrm | | lia | | | | | ] end.
- (* lt_body at pass 0 *)
  unfold lt_body. split; [|split; [exact HSL|]].
  + split; [exact HJ|]. split; [unfold spZ at 1; rewrite F2, Usp; exact Hsp|].
    split; [rewrite F3, E3; exact R3|]. split; [rewrite F4, E4; exact R4|].
    apply (la_saved_kept cx (rdW W mem) _ HSAV). intros a Ha. apply KEEP; [lia|].
    rewrite GR. intros [Hx|Hx]; lia.
  + split; [rewrite F8; apply bv_eq; vm_compute; reflexivity|].
    split; [rewrite F9; reflexivity|]. split; [rewrite F18; reflexivity|].
    split; [rewrite F25; exact E25|]. split; [rewrite F26; exact EO44|]. split; [rewrite F27; reflexivity|]. lia.
- rewrite F23, E23, Z.sub_diag, Z.add_0_r. reflexivity.
- rewrite F24. exact E24.
- rewrite F15. reflexivity.
- (* the recorder: g_rec.state and g_rec.host_settings zeroed, the rest of g_rec, record.spill and g_quitting kept *)
  apply (la_rec_zero B cx ly S W W mem _ R HREC Hcl Han Hrp); [|exact Z16m].
  intros a Ha. unfold A_REC_SPILL, A_G_QUITTING, OFF_STATE, SC_SIZE in Ha. rewrite GR in Ha.
  apply KEEP; [lia|]. rewrite GR. intros [Hx|Hx]; lia.
- (* the budget: the events left from R_ENTRY over the whole payload, by rkey *)
  replace (ev_from (32 - 0)%nat (lt_Rz R) (x_rest cx (x_n cx))) with (ev_from 32%nat R_ENTRY (x_pl cx)); [exact HBUD|].
  unfold x_rest, lt_rest. rewrite Z.sub_diag. cbn [Z.to_nat skipn Nat.sub].
  apply ev_from_rkey. symmetry. apply lt_Rz_rkey; [exact Hcl | exact Hsp0].
Qed.

End e.
End f.
End d.
