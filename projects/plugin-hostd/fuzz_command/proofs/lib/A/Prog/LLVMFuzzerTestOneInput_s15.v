(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment A of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x8653c .. 0x865f0: g_rec's address, the memset of g_rec.state and g_rec.host_settings, the size = 0 exit to the second rec_clear, the eleven frame words of the top loop), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (a segment from a point of the function to its continuations, a runtime entry stepped through) and A/ACbk.v (the walk: runs, branch, the continuation statements applied). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibF PaLibG PaSB CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep CmdObj CmdRo CmdAddr CmdChk
  CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s01 LLVMFuzzerTestOneInput_s16.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* the writes of a stretch of segment A: the frame words at sp + 0 .. sp + 88, sp = entry sp - 256; every other
   region of the state is read only *)
Ltac la_awr Usp :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end;
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -256);
  [reflexivity | exact Usp | cbn [YP09.r_wlo]; unfold LTOI_STK, LLVMF_STK; lia | cbn [YP09.r_whi]; lia |];
  repeat first [apply awr_ok_nil | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]].
(* what a stretch of segment A keeps: every byte outside the frame words *)
Ltac la_keep Hfr Ex Uspx lo hi :=
  intros a Ha Hn; apply (kept_of_frame (segs := _) _ _ _ _ _ (fun a => lo <= a < hi) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq0 | Hin]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?Uspx in Hrr;
      cbv beta; lia|]);
    destruct Hin
  | exact Ha | exact Hn ].

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
(* the runtime entry the segment reaches, word for word the statement's hypothesis (LLVMFuzzerTestOneInput_c.v) *)
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIG CS___asan_memset).
(* the per-binary facts, with cgif's names *)
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* a byte of g_rec is a write the journal admits: in the footprint cmd_PG, a program static, in the image *)
Lemma la_awr_grec : forall STK sp0 bl0 blc fr0 lyx own a, A_G_REC <= a < A_G_REC + 960 ->
  awr_byte SEGS B STK sp0 cmd_PG bl0 blc fr0 lyx own a.
Proof.
intros STK sp0 bl0 blc fr0 lyx own a Ha.
assert (Hfp : inFP cmd_PG a) by (exists (A_G_REC, A_G_REC + 960); split; [left; reflexivity | cbn [fst snd]; lia]).
unfold awr_byte, awr_prog_or_caller. right; right; right; right. left. split; [exact Hfp|]. split.
- rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
  unfold A_G_REC in Ha. lia.
- exact (cif_prog_img _ _ IMG a Hfp).
Qed.

Lemma lt_seg_A : LTA_LH B MT 0 -> LTA_Z B MT -> LT_A_stmt B MT.
Proof.
intros HLH HZ cx ly S W regs mem md k acc R HB0 Hfrm HF R9 R21 R26 R8 HREC Hcl Han Hrp Hnr HBUD.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (GR : A_G_REC = 0x5e3740) by reflexivity.
pose proof HB0 as (HPRE0 & _ & _ & _ & _ & _ & Hpn & Hlen & _).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : LTOI_STK = 32768) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HF as (HJ & Hsp & R3 & R4 & HSAV).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPJ & _).
pose proof HREC as (_ & Hsp0 & _).
assert (Hsp1 : spZ regs = x_sp0 cx - 256) by (rewrite Hsp; unfold x_sp1, x_sp0, LT_FRAME; reflexivity).
assert (SP0 : alloc_ceiling + 32768 <= x_sp0 cx <= 2 ^ 47) by (unfold x_sp0; rewrite WS in Hslo; lia).
assert (Rn : 0 <= x_n cx < 2 ^ 64) by (destruct Hpn as [[Hn0 _] | [Hn0 _]]; lia).
(* the image words the segment reads, at its start: cmd_ro_ok carried along the journal (_s01.v lt_ro_kept, its
   RRO and RPG from IMG's cif_relro_img and cif_prog_not_ro) *)
destruct (la_ro_vals _ (lt_ro_kept B MT LAWS HB IMG (cif_relro_img _ _ IMG) (cif_prog_not_ro _ _ IMG)
  cx ly S W mem md [] k HB0 HJ)) as (G2 & G3 & G4 & GN).
(* the symbolic state at 0x8653c *)
assert (HS : st_ok_pi SEGS VAL (la_E regs) ss_la
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_RC1RA)) mem (seg_rom SEGS)))).
{ apply (la_seed VOBJS W regs mem); [lia | lia | | | exact R9 | exact G2 | exact G3 | exact G4 | exact GN].
  - rewrite Hsp1. replace (x_sp0 cx - 256) with (x_sp0 cx + (-16) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
  - intros a Ha. apply HPJ. rewrite WS. lia. }
assert (HEI : img_env VAL A_LIM (la_E regs)) by (unfold la_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew (la_E regs) n = ew (Ereg regs la_extra) n)
  by (intros n Hn; unfold la_E; apply Eimg_low; exact Hn).
assert (HED : ed (la_E regs) = ed (Ereg regs la_extra)) by reflexivity.
remember (la_E regs) as E eqn:HE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EEo; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EEo; reflexivity).
assert (E8 : ew E 8 = getr regs 8) by (apply EEo; reflexivity).
assert (E9 : ew E 9 = Z_to_bv 64 LT_SB) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E21 : ew E 21 = getr regs 21) by (apply EEo; reflexivity).
assert (E26 : ew E 26 = Z_to_bv 64 (x_n cx)) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
assert (E32 : ew E 32 = Z_to_bv 64 LA_NC) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EO44 : ew E 285 = Z_to_bv 64 A_G_REC)
  by (exact (la_ew_obj VOBJS E 44 A_G_REC HEI ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(unfold A_OBJ, A_LIM; lia))).
assert (EO40 : ew E 281 = Z_to_bv 64 LT_CODES)
  by (exact (la_ew_obj VOBJS E 40 LT_CODES HEI ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(unfold A_OBJ, A_LIM; lia))).
assert (EG2 : bv_unsigned (ew E 243) = 0xa7068).
{ change 243%nat with (A_OBJ 2).
  rewrite (la_ew_obj VOBJS E 2 0xa7068 HEI ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(unfold A_OBJ, A_LIM; lia)).
  apply unsigned_lit_small. lia. }
assert (EG3 : bv_unsigned (ew E 244) = 0xa7070).
{ change 244%nat with (A_OBJ 3).
  rewrite (la_ew_obj VOBJS E 3 0xa7070 HEI ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(unfold A_OBJ, A_LIM; lia)).
  apply unsigned_lit_small. lia. }
assert (EG4 : bv_unsigned (ew E 245) = 0xa7078).
{ change 245%nat with (A_OBJ 4).
  rewrite (la_ew_obj VOBJS E 4 0xa7078 HEI ltac:(vm_compute; lia) ltac:(vm_compute; reflexivity) ltac:(unfold A_OBJ, A_LIM; lia)).
  apply unsigned_lit_small. lia. }
assert (EGN : bv_unsigned (ew E 32) = LA_NC) by (rewrite E32; apply unsigned_lit_small; unfold LA_NC; lia).
assert (EGu : bv_unsigned (ew E 285) = A_G_REC) by (rewrite EO44; apply unsigned_lit_small; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (UspA : bv_unsigned (ew E 2) = x_sp0 cx + -256) by (rewrite Usp, Hsp1; lia).
assert (HAE : env_agree 32 (Ereg regs la_extra) E).
{ split; [intros n Hn; rewrite EL by (unfold A_TEXT; lia); reflexivity | exact HED]. }
pose proof (la_shok B HB ly S W mem md E HAR E9 E32) as SHOK.
clear HE EL HED.
(* 0x8653c .. 0x86554: s2 := &g_rec (GOT 0xa7068), sp + 24 := &g_rec.state, then the memset entry on
   (&g_rec.state, 0, 16) *)
paj_run_tok RUN HS HJ SHOK LAspan.
{ la_awr UspA. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv1 := d) in *; clearbody mdv1 end.
lazymatch goal with Hfr : frame_of E _ (mrestrict _ mem) (mrestrict _ ?m1) |- _ =>
  assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp0 cx - 256 <= a < x_sp0 cx - 168) -> rdW W m1 a = rdW W mem a)
  by (la_keep Hfr E UspA (x_sp0 cx - 256) (x_sp0 cx - 168)) end.
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r1 _ ?m1 _) _) _ =>
  assert (Ud : getr r1 10 = w64 (A_G_REC + 944)) by (rewrite P10, EGu; reflexivity);
  assert (HspT : spZ r1 = x_sp0 cx + -256) by (unfold spZ at 1; rewrite P2; exact UspA);
  assert (Ugp : getr r1 3 = w64 (as_gp B)) by (rewrite P3, E3, R3; exact Hgp0);
  assert (Utp : getr r1 4 = w64 (as_tp B)) by (rewrite P4, E4, R4; exact Htp0);
  eapply SRr_bind;
  [ eapply (aj_intrin_at_prog SEGS B LAWS pa_segs_low OSet (SIG CS___asan_memset) AMEMSET
      W r1 m1 LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S mdv1 k
      (A_G_REC + 944) 0 16 (-256) (Z_to_bv 64 (BASE + 116)) HJ Ud P11 P12) | ] end.
{ lia. }
{ rewrite GR. lia. }
{ rewrite GR. lia. }
{ exact HspT. }
{ reflexivity. }
{ lia. }
{ rewrite Hes, WS. lia. }
{ exact Ugp. }
{ exact Utp. }
{ exact P1. }
{ apply ret_ok_codeptr_v; [lia | reflexivity]. }
{ intros a Ha. split; [apply la_awr_grec; lia | rewrite Hes; lia]. }
{ exact PRW. }
{ intros a Ha _ Hs. exfalso. lia. }
{ unfold amem_range, kLowMemEnd. rewrite GR. lia. }
{ apply (cmd_addressable_chk SEGS B LAWS HB ly S W _ mdv1 _ _ (proj1 HJ)). vm_compute. reflexivity. }
{ intros _. apply (cmd_hull_vis_chk SEGS B LAWS HB ly S W _ mdv1 _ _ (proj1 HJ)). vm_compute. reflexivity. }
{ exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & HSET & HKEEP & HPRES).
(* back at 0x86558: the frame word, the three GOT words and rec_ncodes are kept by the memset *)
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_aview (segs := SEGS)); [exact Usp | | exact HPRES].
    intros a Ha. apply HKEEP; [lia | lia | rewrite Hes; lia].
  - eapply (region_kept_aview (segs := SEGS)); [exact EG2 | | exact HPRES].
    intros a Ha. apply HKEEP; [lia | lia | rewrite Hes; lia].
  - eapply (region_kept_aview (segs := SEGS)); [exact EG3 | | exact HPRES].
    intros a Ha. apply HKEEP; [lia | lia | rewrite Hes; lia].
  - eapply (region_kept_aview (segs := SEGS)); [exact EG4 | | exact HPRES].
    intros a Ha. apply HKEEP; [lia | lia | rewrite Hes; lia].
  - eapply (region_kept_aview (segs := SEGS)); [exact EGN | | exact HPRES].
    intros a Ha. unfold LA_NC in Ha. apply HKEEP; [lia | lia | rewrite Hes; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
assert (LC : length CLOB = 16%nat) by reflexivity.
remember (havoc E 40 (map (getr regs2) CLOB)) as Ec eqn:HEc in HS.
assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEI | rewrite length_map, LC; cbv; lia]).
assert (OLDc : forall n, (n < 40)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HEc; apply YN3v.ew_havoc_old; exact Hn).
assert (HIc : forall n, (56 <= n)%nat -> ew Ec n = ew E n)
  by (intros n Hn; rewrite HEc; apply ew_havoc_above; rewrite length_map, LC; lia).
clear HEc.
assert (UspC : bv_unsigned (ew Ec 2) = x_sp0 cx + -256) by (rewrite OLDc by lia; exact UspA).
assert (Ec9 : ew Ec 9 = Z_to_bv 64 LT_SB) by (rewrite OLDc by lia; exact E9).
assert (Ec26 : ew Ec 26 = Z_to_bv 64 (x_n cx)) by (rewrite OLDc by lia; exact E26).
assert (Ec32 : ew Ec 32 = Z_to_bv 64 LA_NC) by (rewrite OLDc by lia; exact E32).
assert (Ec285 : ew Ec 285 = Z_to_bv 64 A_G_REC) by (rewrite HIc by lia; exact EO44).
assert (Ec281 : ew Ec 281 = Z_to_bv 64 LT_CODES) by (rewrite HIc by lia; exact EO40).
clear SHOK. pose proof (la_shok B HB ly S W mem2 md2 Ec (proj1 HJ2) Ec9 Ec32) as SHOK.
(* the memory the rest of the segment starts from: the memset's 16 zero bytes, the rest as at the segment's start
   outside the frame words and the runtime entry's scratch window below sp *)
assert (KEEP12 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp0 cx - 256 - 4096 <= a < x_sp0 cx - 168) ->
  ~ (A_G_REC + 944 <= a < A_G_REC + 960) -> rdW W mem2 a = rdW W mem a).
{ intros a Ha H1 H2. rewrite (HKEEP a Ha) by (rewrite ?Hes; lia). apply KEEP0; [exact Ha | lia]. }
assert (Z16m : forall i, 0 <= i < 16 -> rdW W mem2 (A_G_REC + OFF_STATE + i) = Some 0).
{ intros i Hi. unfold OFF_STATE. rewrite (HSET i Hi). reflexivity. }
clear HKEEP HSET KEEP0 HJ. rename HJ2 into HJ.
(* 0x86558: beqz s10 *)
psrr_branch_tok RUN BR HS SHOK LAspan.
- (* size = 0: 0x86a0c calls rec_clear the second time; LT_Z_stmt from the empty payload *)
  assert (Hn0 : x_n cx = 0).
  { rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. rewrite (U_atom Ec 26 (x_n cx) Ec26 Rn), U_lit in Hc by lia.
    exact Hc. }
  clear Hc.
  paj_run_tok RUN HS HJ SHOK LAspan.
  { la_awr UspC. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv3 := d) in *; clearbody mdv3 end.
  lazymatch goal with Hfr : frame_of Ec _ (mrestrict _ mem2) (mrestrict _ ?m3) |- _ =>
    assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp0 cx - 256 <= a < x_sp0 cx - 168) -> rdW W m3 a = rdW W mem2 a)
    by (la_keep Hfr Ec UspC (x_sp0 cx - 256) (x_sp0 cx - 168)) end.
  clear HF HFr HG.
  pmkst HS.
  prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
  prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9.
  rewrite (SIGP CS_rec_clear ltac:(unfold cmd_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
  replace (cmd_af CS_rec_clear) with AF_rec_clear by (vm_compute; reflexivity).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?d3) _ =>
  apply (HZ fx cx ly S W r3 m3 d3 k acc (lt_Rz R) [] 0); [ exact HB0 | exact Hfrm | | | | | | ] end.
  + split; [exact HJ|]. split; [unfold spZ at 1; rewrite F2, OLDc, Usp, Hsp by lia; reflexivity|].
    split; [rewrite F3, OLDc, E3 by lia; exact R3|]. split; [rewrite F4, OLDc, E4 by lia; exact R4|].
    apply (la_saved_kept cx (rdW W mem) _ HSAV). intros a Ha. rewrite KEEP3 by lia. apply KEEP12; lia.
  + rewrite F1. reflexivity.
  + rewrite F9, OLDc by lia. exact E9.
  + right. rewrite F8, OLDc, E8 by lia. exact R8.
  + apply (la_rec_zero B cx ly S W W mem _ R HREC Hcl Han Hrp).
    * intros a Ha. unfold A_REC_SPILL, A_G_QUITTING, OFF_STATE, SC_SIZE in Ha. rewrite KEEP3 by lia. apply KEEP12; lia.
    * intros i Hi. rewrite KEEP3 by (unfold OFF_STATE; lia). exact (Z16m i Hi).
  + assert (Hpl : x_pl cx = []).
    { pose proof Hlen as Hlen'. destruct (x_pl cx) as [|b l]; [reflexivity|]. exfalso. cbn [length] in Hlen'. lia. }
    replace (EV_REC_CLEAR (lt_Rz R)) with (ev_from 32%nat R_ENTRY (x_pl cx)); [exact HBUD|].
    rewrite Hpl, ev_from_nil. apply rkey_ev_rec_clear. symmetry. apply lt_Rz_rkey; [exact Hcl | exact Hsp0].
- (* size > 0: 0x8655c .. 0x865f0, the code count (its check vanishes by the shadow entry of rec_ncodes) and the
     eleven frame words; s0 := 32, s6 := the mask, a0 := 0; on to the loop head 0x865f4 *)
  assert (Hnz : x_n cx <> 0).
  { rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. rewrite (U_atom Ec 26 (x_n cx) Ec26 Rn), U_lit in Hc by lia.
    exact Hc. }
  clear Hc.
  destruct Hpn as [[Hn0 _] | [Hnrg Hpin]]; [exfalso; exact (Hnz Hn0)|].
  paj_run_to_tok RUNTO HS HJ SHOK LAspan 272.
  { la_awr UspC. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv3 := d) in *; clearbody mdv3 end.
  lazymatch goal with Hfr : frame_of Ec _ (mrestrict _ mem2) (mrestrict _ ?m3) |- _ =>
    assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sp0 cx - 256 <= a < x_sp0 cx - 168) -> rdW W m3 a = rdW W mem2 a)
    by (la_keep Hfr Ec UspC (x_sp0 cx - 256) (x_sp0 cx - 168)) end.
  clear HF HFr HG.
  pmkst HS.
  prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4. prreg HS (8%bv : bv 5) F8.
  prreg HS (9%bv : bv 5) F9. prreg HS (10%bv : bv 5) F10. prreg HS (18%bv : bv 5) F18.
  prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22. prreg HS (26%bv : bv 5) F26.
  pose proof (st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl) as HRF. cbn [ms_mem restrict] in HRF.
  lazymatch type of HS with st_ok_pi _ _ ?Ef _ _ =>
    assert (Ef2 : bv_unsigned (ew Ef 2) = x_sp1 cx) by (cbn [ew ewset Nat.eqb]; rewrite OLDc, Usp, Hsp by lia; reflexivity);
    assert (Ef285 : ew Ef 285 = Z_to_bv 64 A_G_REC) by (cbn [ew ewset Nat.eqb]; exact Ec285);
    assert (Ef281 : ew Ef 281 = Z_to_bv 64 LT_CODES) by (cbn [ew ewset Nat.eqb]; exact Ec281);
    assert (Ef9 : ew Ef 9 = Z_to_bv 64 LT_SB) by (cbn [ew ewset Nat.eqb]; exact Ec9) end.
  pose proof (la_slots_of_region _ W _ (x_sp1 cx) HRF Ef2 Ef285 Ef281 Ef9) as HSL.
  change (BASE + 272) with (BASE + LO_LH).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?r3 _ ?m3 _) ?d3) _ =>
  apply (HLH fx cx ly S W r3 m3 d3 k acc (x_n cx) (lt_Rz R) [] 0); [ exact HB0 | exact Hfrm | | lia | | | | | ] end.
  + unfold lt_body. split; [|split; [exact HSL|]].
    * split; [exact HJ|]. split; [unfold spZ at 1; rewrite F2, OLDc, Usp, Hsp by lia; reflexivity|].
      split; [rewrite F3, OLDc, E3 by lia; exact R3|]. split; [rewrite F4, OLDc, E4 by lia; exact R4|].
      apply (la_saved_kept cx (rdW W mem) _ HSAV). intros a Ha. rewrite KEEP3 by lia. apply KEEP12; lia.
    * split; [rewrite F8; reflexivity|]. split; [rewrite F9, OLDc by lia; exact E9|].
      split; [rewrite F18, Ec285; reflexivity|]. split; [rewrite F22; reflexivity|].
      split; [lia|]. split; [lia | exact Hpin].
  + rewrite F21, OLDc, E21, R21 by lia. rewrite Z.sub_diag, Z.add_0_r. reflexivity.
  + rewrite F26, OLDc by lia. exact E26.
  + rewrite F10. reflexivity.
  + apply (la_rec_zero B cx ly S W W mem _ R HREC Hcl Han Hrp).
    * intros a Ha. unfold A_REC_SPILL, A_G_QUITTING, OFF_STATE, SC_SIZE in Ha. rewrite KEEP3 by lia. apply KEEP12; lia.
    * intros i Hi. rewrite KEEP3 by (unfold OFF_STATE; lia). exact (Z16m i Hi).
  + replace (ev_from (32 - 0)%nat (lt_Rz R) (x_rest cx (x_n cx))) with (ev_from 32%nat R_ENTRY (x_pl cx)); [exact HBUD|].
    unfold x_rest, lt_rest. rewrite Z.sub_diag. cbn [Z.to_nat skipn Nat.sub].
    apply ev_from_rkey. symmetry. apply lt_Rz_rkey; [exact Hcl | exact Hsp0].
Qed.

End e.
End f.
End d.
