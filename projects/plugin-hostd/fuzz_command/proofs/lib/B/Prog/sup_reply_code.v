(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan walk of sup_reply_code (plugin-hostd/fuzz_command, 0x89d6c, 20 instructions), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (pb_cmpPixel, a leaf that ends in a tail jump to a runtime entry) and A/ACh2.v (the step through a call and back). *)
(* Modified by Theorem Labs, 2026-10: ported from lib/A/Prog/sup_reply_code.v (a working branch efc67a58cf8) to fuzz_command.asan-ubsan: walked again at the B addresses (0x8a398, 26 instructions, a 32-byte frame that keeps the 5 in s1), with the UBSan pointer-overflow check of reply + 5 (0x8a3e4 bgeu s1,a0 to the unimp at 0x8a3fc) shown not taken. *)
(* Modified by Theorem Labs, 2026-10: onto a working branch 917ca7ac6b1: the literal's shadow and tail come from the record's checkers (lib/B/Prog/CmdChk.v) and B's regenerated cmd_ro_ends, through the ruling's cmd_aread_ok_chk and cmd_tail_vis_at. *)
(* Modified by Theorem Labs, 2026-10: onto a working branch 6830f0bf032 (lib/B/Prog/CmdRecFacts.v): the three carried record facts are now the kit lemmas cmd_aread_ok_chk, cmd_tail_vis_at and cmd_rec_cells. The read-only view comes from cmd_rom_view_on, which replaces the local src_rom_view. The kit's extra premises are the ruling's HB and IMG. *)
(* Modified by Theorem Labs, 2026-10: onto a working branch 713692f1e0c (B statements re-aligned to a working branch 7ef75dec92f): ASTRNCMP and AATOI are the statement's new fx-generic hypotheses, word for word, and the walk applies each at its own fx. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtNumber RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_reply_code_c sup_reply_code_s1.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require __intscan_c.
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
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the runtime entries the call reaches: the statement's own hypotheses, word for word (fx-generic; applied at fx) *)
Hypothesis ASTRNCMP : forall fx0 : YK11.FPState, @astrncmp_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strncmp).
Hypothesis AATOI : forall fx0 : YK11.FPState, @aatoi_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_atoi) A_FLAG_REPLACE_STR A_SSP_GOT A_SSP_GUARD.
(* the per-binary record, as cgif's walks take it (A/AChd.v:75-76; a Theorem Labs lane's ruling a Theorem Labs lane's RULING-STMT.md §1).
   HB and IMG are the premises that lib/B/Prog/CmdRecFacts.v's lemmas take besides LAWS:
   - cmd_aread_ok_chk (CmdRecBase.v; LAWS HB): the shadow of the literal "resp " at 0x21d60, 5 bytes, which the
     strncmp wrapper reads, from cmd_addr_b 0x21d60 5 = true and cmd_hull_b 0x21d60 5 = true by computation;
   - cmd_tail_vis_at (CmdRecRo.v; LAWS HB IMG): the bytes after the literal's terminator up to the end of its
     8-byte word, which the strncmp wrapper's word loop reads, from In 0x21d65 cmd_ro_ends by computation;
   - cmd_rec_cells (CmdRecCells.v; LAWS HB IMG): the cells the atoi wrapper reads besides the string
     (A_FLAG_REPLACE_STR = 0xae455, the GOT word 0xa6bf8 of the stack guard 0x604158, lib/B/Rt/RtAPI.v:56-60);
   - cmd_rom_view_on (CmdRecImg.v; LAWS HB IMG): a Theorem Labs lane's rt_rom_view from arodata_okP *)
Hypothesis HB : YF0m.CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis IMG : cmd_img_facts SEGS B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

Theorem tsup_reply_code_spec_holds : tsup_reply_code_spec B MT.
Proof.
unfold tsup_reply_code_spec.
intros ly S W regs mem md x s HPRE HROD H10 Hx HBLK HSTR HTAIL HRO HOBJ HEV.
pose proof (cmd_rec_cells SEGS B LAWS HB IMG ly S W mem md (proj1 HPRE)) as (HFLAG & HGUARD & ev & HERR).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : SUP_REPLY_CODE_STK = 12288) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (proj1 errno_low) as [Herr0 Herr1].
(* the in-segment read-only view after the stack writes below the entry sp: cmd_rom_view_on at mem, and every image
   byte lies below the stack window (pa_img_range) *)
assert (HROMk : forall memT, kept_out (rdW W mem) (rdW W memT) (spZ regs - SUP_REPLY_CODE_STK) (spZ regs) ->
  rt_rom_view SEGS B W memT).
{ intros memT HK a Ha Ho He.
  assert (Himg : in_img SEGS a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
  pose proof (pa_img_range _ Himg) as Hr.
  rewrite (HK a) by lia. exact (cmd_rom_view_on SEGS B LAWS HB IMG RLO RHI W mem HROD a Ha Ho He). }
(* the `+ 8` band premise of the strncmp wrapper on the string (RtString.v astrncmp_realizes): the string and its
   NUL lie in a live block (a Theorem Labs lane's string-band.md section 4, 0x8a3c0, class H) *)
pose proof (PaLibH.amem8_of_blockA SEGS B LAWS ly S W mem md x (astr_len s) HAR HBLK ltac:(unfold astr_len; lia)) as HAMx.
(* the string's block *)
destruct HBLK as (p & k & Hpk & Hpx & Hxk).
destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hpk) as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _ & Hkr).
pose proof (req_size_pos k ltac:(lia)) as [_ Hreq].
assert (HTB : x + Z.of_nat (length s) - (x + Z.of_nat (length s)) mod 8 + 8 <= spZ regs - SUP_REPLY_CODE_STK).
{ assert (Hxe : 0 <= x + Z.of_nat (length s) < alloc_ceiling) by lia.
  pose proof (tail_below _ _ Hxe HAC). lia. }
(* the literal "resp " among the read-only bytes *)
assert (HLIT : abytes_atR (rdW W mem) 0x21d60 RO_lit_21d60).
{ clear - HRO. destruct HRO as [HRO _]. unfold cmd_ro_bytes in HRO.
  repeat match type of HRO with
  | abytes_atR _ 0x21d60 _ /\ _ => exact (proj1 HRO)
  | _ /\ _ => apply proj2 in HRO
  end. }
assert (HLITs : astr_atR (rdW W mem) 0x21d60 src_resp) by (split; [rewrite src_resp_ro; exact HLIT | exact src_resp_nz]).
(* its end, one of B's literal ends (CmdRo.v cmd_ro_ends) *)
assert (HE65 : In 0x21d65 cmd_ro_ends).
{ destruct (proj1 (existsb_exists (Z.eqb 0x21d65) cmd_ro_ends) ltac:(vm_compute; reflexivity)) as (e & He & Hq).
  apply Z.eqb_eq in Hq. subst e. exact He. }
(* the symbolic entry state *)
destruct (src_entry W regs mem ly Hstk Hpres) as [HS SHOK].
pose proof (ajournal_init_na SEGS B SUP_REPLY_CODE_STK [] ly S W regs mem md HPRE) as HJ.
assert (EL : forall n, (n < A_TEXT)%nat -> ew (src_E regs) n = ew (Ereg regs src_extra) n)
  by (intros n Hn; unfold src_E; apply Eimg_low; exact Hn).
assert (HED : ed (src_E regs) = ed (Ereg regs src_extra)) by reflexivity.
assert (HEI : img_env VAL A_LIM (src_E regs)) by (unfold src_E; apply Eimg_env).
remember (src_E regs) as E eqn:HE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E1 : ew E 1 = getr regs 1) by (apply EEo; reflexivity).
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E3 : ew E 3 = getr regs 3) by (apply EEo; reflexivity).
assert (E4 : ew E 4 = getr regs 4) by (apply EEo; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 x) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E289 : ew E 289 = Z_to_bv 64 0x21d60).
{ pose proof (HEI 289%nat ltac:(unfold A_TEXT, A_LIM; lia)) as H.
  change (VAL 289%nat) with (VAL (A_OBJ 48)) in H. rewrite (HOBJ 48%nat ltac:(vm_compute; lia)) in H.
  apply bv_eq. rewrite H. rewrite unsigned_lit_small by lia. vm_compute. reflexivity. }
assert (HAE : env_agree 32 (Ereg regs src_extra) E).
{ split; [intros n Hn; rewrite EL by (unfold A_TEXT; lia); reflexivity | exact HED]. }
clear HE EL HED.
unfold cfg_at, w64.
(* 0x8a398 .. 0x8a3c0: the frame (ra, s0, s1), s0 := the string, s1 := 5, then the call of the strncmp wrapper on
   (s, "resp ", 5) *)
paj_run_tok RUN HS HJ SHOK src_Bspan.
{ awr_ok_tac. exact Usp. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
lazymatch goal with Hfr : frame_of E _ (mrestrict _ _) (mrestrict _ _) |- _ =>
assert (KEEP1 : kept_out (rdW W mem) (rdW W (ms_mem ms)) (spZ regs - SUP_REPLY_CODE_STK) (spZ regs))
by (intros a Ha Hn; apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - SUP_REPLY_CODE_STK <= a < spZ regs) Hfr);
  [ intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite Usp in Hrr; rewrite WS; lia|]);
    destruct Hin
  | exact Ha | exact Hn ]) end.
assert (HspT : spZ (ms_regs ms) = spZ regs + -32).
{ unfold spZ at 1. rewrite P2, Usp. rewrite unsigned_lit_small by lia. reflexivity. }
assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, E3; exact Hgp).
assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, E4; exact Htp).
assert (P10' : getr (ms_regs ms) 10 = w64 x) by (rewrite P10, E10; reflexivity).
assert (P11' : getr (ms_regs ms) 11 = w64 0x21d60) by (rewrite P11, E289; reflexivity).
assert (P12' : getr (ms_regs ms) 12 = w64 5) by (rewrite P12; reflexivity).
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS Hsegs errno_low (2 * ESTACK) (fun _ => False) (SIG CS___interceptor_trampoline_strncmp)
    W (ms_regs ms) (ms_mem ms) SUP_REPLY_CODE_STK (spZ regs) [] ly S W mem md [] ly S _ 0 (-32)
    (Z_to_bv 64 (BASE + 16020)) _ HJ HspT eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite WS, Hes; lia) P1
    (fun a (H : False) => False_ind _ H)).
  apply (ASTRNCMP fx ly S W (ms_regs ms) (ms_mem ms) _ x 0x21d60 5 s src_resp).
  - exact (ecall_pre_stk_at SEGS B (2 * ESTACK) SUP_REPLY_CODE_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem ms) _ 0
      (ms_regs ms) (-32) HJ HspT eq_refl ltac:(lia) ltac:(rewrite Hes; lia) ltac:(rewrite WS, Hes; lia) HraT P3' P4').
  - exact P10'. - exact P11'. - exact P12'. - lia. - lia. - lia.
  - apply (astr_atR_view SEGS). exact (astr_atR_kept _ _ _ _ x s KEEP1 HSTR ltac:(lia) ltac:(lia) ltac:(lia)).
  - apply (astr_atR_view SEGS). exact (astr_atR_kept _ _ _ _ 0x21d60 src_resp KEEP1 HLITs ltac:(lia) ltac:(cbn; lia) ltac:(lia)).
  - unfold astr_len.
    apply (aread_ok_kept SEGS 0 (2 * ESTACK) W regs (ms_regs ms) mem (ms_mem ms) (spZ regs - SUP_REPLY_CODE_STK) (spZ regs)
      x _ KEEP1); [| lia | lia | lia | rewrite HspT, Hes; lia | lia].
    apply (aread_ok_of_block SEGS B LAWS 0 ly S W regs mem md p k x _ HAR Hpk Hpx); lia.
  - exact HAMx.
  - change (Z.min 5 (astr_len src_resp + 1)) with 5.
    destruct (cmd_aread_ok_chk SEGS B LAWS HB ly S W (ms_mem ms) _ 0x21d60 5 (proj1 HJ) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity)) as [Zr Zh].
    split; [lia|]. split; [lia|]. split; [lia|]. split.
    + intros a Ha. split; [|unfold ascratch_stk; rewrite HspT; lia].
      rewrite (KEEP1 a) by lia. replace a with (0x21d60 + Z.of_nat (Z.to_nat (a - 0x21d60))) by lia.
      rewrite (HLIT (Z.to_nat (a - 0x21d60))) by (cbn; lia). discriminate.
    + split; [unfold amem_range; left; lia|]. split; [exact Zr | intros _; exact Zh].
  - (* the literal "resp " in .rodata (a Theorem Labs lane's string-band.md section 4, 0x8a3c0, class R) *)
    apply PaLibH.amem8_of_low; [lia|]. change (astr_len src_resp) with 5. unfold kLowMemEnd. lia.
  - exact (atail_vis_kept SEGS W mem (ms_mem ms) _ _ _ KEEP1 HTAIL ltac:(lia) HTB ltac:(lia)).
  - change (astr_len src_resp) with 5. exact (cmd_tail_vis_at SEGS B LAWS HB IMG ly S W (ms_mem ms) _ 0x21d65 (proj1 HJ) HE65).
  - exact (HROMk _ KEEP1). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
(* back at 0x8a3c4 *)
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
  - apply (mbyte_of_aview SEGS). apply HK2; [lia | rewrite Hes; lia | tauto].
  - intros _. apply (apresent_writable SEGS). apply Hpres2. rewrite WS. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
assert (A44 : ew (havoc E 40 (map (getr regs2) CLOB)) 44 = getr regs2 10) by reflexivity.
remember (havoc E 40 (map (getr regs2) CLOB)) as Ec eqn:HEc.
assert (HEI3 : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall n, (n < 40)%nat -> ew Ec n = ew E n) by (intros n Hn; rewrite HEc; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE3 : env_agree 32 (Ereg regs src_extra) Ec).
{ destruct HAE as [HA1 HA2]. split; [intros n Hn; rewrite OLD3 by lia; exact (HA1 n Hn) | rewrite HEc; exact HA2]. }
clear HEc.
assert (Usp3 : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp).
assert (SHOK3 : sh_ok SEGS src_Bx src_SH Ec (mrestrict (w_H W) mem2)) by (unfold sh_ok, src_SH; apply Forall_nil).
assert (KEEP2 : kept_out (rdW W mem) (rdW W mem2) (spZ regs - SUP_REPLY_CODE_STK) (spZ regs)).
{ intros a Ha Hn. rewrite (HK2 a Ha); [exact (KEEP1 a Ha Hn) | rewrite WS in Hn; rewrite Hes; lia | tauto]. }
assert (HQ2' : getr regs2 10 = w64 0 <-> map bv_unsigned (firstn 5 s) = [114; 101; 115; 112; 32]).
{ rewrite HQ2. apply src_strncmp_iff. exact (proj2 HSTR). }
clear HQ2.
(* 0x8a3c4: beqz a0 on the wrapper's answer *)
psrr_branch_tok RUN BR HS SHOK3 src_Bspan.
- (* the answer is 0: s starts with "resp "; 0x8a3e0 forms s + 5, 0x8a3e4 checks it (UBSan), 0x8a3e8 .. 0x8a3f8 pop
     the frame and jump to the atoi wrapper on s + 5 *)
  assert (HZ : getr regs2 10 = w64 0).
  { rewrite branch_eq_U in Hc. apply Z.eqb_eq in Hc. unfold U in Hc. apply bv_eq in Hc. cbn [sv_denot] in Hc.
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc. rewrite A44 in Hc. exact Hc. }
  clear Hc.
  pose proof (proj1 HQ2' HZ) as HPFX.
  assert (HL5 : (5 <= length s)%nat).
  { pose proof (f_equal (@length Z) HPFX) as HLn. rewrite length_map, length_firstn in HLn.
    change (length [114; 101; 115; 112; 32]) with 5%nat in HLn. lia. }
  (* 0x8a3e0: a0 := s0 + 5 *)
  paj_run_tok RUN HS HJ2 SHOK3 src_Bspan.
  { awr_ok_tac. exact Usp3. }
  lazymatch goal with Hfr : frame_of Ec _ _ (mrestrict _ ?m3) |- _ =>
  assert (KEEP2c : kept_out (rdW W mem) (rdW W m3) (spZ regs - SUP_REPLY_CODE_STK) (spZ regs))
  by (intros a Ha Hn; rewrite (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - SUP_REPLY_CODE_STK <= a < spZ regs) Hfr);
    [ exact (KEEP2 a Ha Hn)
    | intros b wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite Usp3 in Hrr; rewrite WS; lia|]);
      destruct Hin
    | exact Ha | exact Hn ]); clear Hfr end.
  clear KEEP2.
  (* 0x8a3e4: bgeu s1,a0 to the unimp at 0x8a3fc (UBSan's pointer-overflow check of reply + 5), taken when
     5 >= s + 5 unsigned, i.e. the sum wraps or s is null. The string lies in a live block, so 4096 <= s and
     s + 5 < alloc_ceiling (YG0d.v:433-434): the check passes *)
  psrr_branch_tok RUN BR HS SHOK3 src_Bspan.
  { exfalso. rewrite branch_geu_U in Hc. unfold U in Hc. cbn [sv_denot] in Hc.
    rewrite OLD3, E10 in Hc by lia. rewrite (unsigned_lit_small x Hx), (unsigned_lit_small 5) in Hc by lia.
    rewrite (unsigned_lit_small (x + 5)) in Hc by lia.
    apply negb_true_iff, Z.ltb_ge in Hc. lia. }
  clear Hc.
  (* 0x8a3e8 .. 0x8a3f8: restore ra, s0, s1, pop the frame, jump to the atoi wrapper *)
  paj_run_tok RUN HS HJ2 SHOK3 src_Bspan.
  { awr_ok_tac. exact Usp3. }
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (10%bv : bv 5) Q10.
  lazymatch goal with Hfr : frame_of Ec _ _ (mrestrict _ ?m3) |- _ =>
  assert (KEEP3 : kept_out (rdW W mem) (rdW W m3) (spZ regs - SUP_REPLY_CODE_STK) (spZ regs))
  by (intros a Ha Hn; rewrite (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - SUP_REPLY_CODE_STK <= a < spZ regs) Hfr);
    [ exact (KEEP2c a Ha Hn)
    | intros b wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite Usp3 in Hrr; rewrite WS; lia|]);
      destruct Hin
    | exact Ha | exact Hn ]) end.
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rT _ ?mT _; cfg_model := ?dT |} _ =>
  assert (Hsp4 : spZ rT = spZ regs + 0) by (unfold spZ at 1; rewrite Q2, Usp3; lia);
  assert (Q1' : getr rT 1 = getr regs 1) by (rewrite Q1, OLD3, E1 by lia; reflexivity);
  assert (Q3' : getr rT 3 = w64 (as_gp B)) by (rewrite Q3, OLD3, E3 by lia; exact Hgp);
  assert (Q4' : getr rT 4 = w64 (as_tp B)) by (rewrite Q4, OLD3, E4 by lia; exact Htp);
  assert (Q10' : getr rT 10 = w64 (x + 5)) by (rewrite Q10, OLD3, E10 by lia; rewrite unsigned_lit_small by lia; reflexivity);
  pose proof (aregs_preserved_of_st_ok SEGS _ Ec _ _ regs src_extra HS HAE3 ltac:(vm_compute; reflexivity)) as HPT3;
  cbn [ms_regs restrict] in HPT3;
  eapply SRr_mono;
  [ eapply (aj_art_at SEGS B LAWS Hsegs errno_low (3 * ESTACK) (aerrno_cell B) (SIG CS___interceptor_trampoline_atoi)
      W rT mT SUP_REPLY_CODE_STK (spZ regs) [] ly S W mem md [] ly S dT 0 0 (getr regs 1) _ HJ2 Hsp4 eq_refl
      ltac:(lia) ltac:(lia) ltac:(rewrite WS, Hes; lia) Q1' (fun a H => H));
    apply (AATOI fx ly S W rT mT dT (x + 5) (skipn 5 s) ev)
  | ] end.
  + rewrite (KEEP3 A_FLAG_REPLACE_STR) by (unfold A_FLAG_REPLACE_STR; lia). exact HFLAG.
  + exact (aguard_ok_kept SEGS W mem _ _ _ A_SSP_GOT A_SSP_GUARD KEEP3 HGUARD
      ltac:(unfold A_SSP_GOT; lia) ltac:(unfold A_SSP_GOT; lia) ltac:(unfold A_SSP_GUARD; lia) ltac:(unfold A_SSP_GUARD; lia) ltac:(lia)).
  + eapply (ecall_pre_stk_at SEGS B (3 * ESTACK) SUP_REPLY_CODE_STK (spZ regs) [] ly S W mem md [] ly S W _ _ 0 _ 0 HJ2 Hsp4 eq_refl);
      [lia | rewrite Hes; lia | rewrite WS, Hes; lia | rewrite Q1'; exact Hra | exact Q3' | exact Q4'].
  + exact Q10'.
  + lia.
  + apply (astr_atR_view SEGS).
    pose proof (astr_atR_skipn _ x s 5 HSTR HL5) as Hsk. change (x + Z.of_nat 5) with (x + 5) in Hsk.
    assert (Hb1 : 0 <= x + 5) by lia.
    assert (Hb2 : x + 5 + Z.of_nat (length (skipn 5 s)) + 1 <= spZ regs - SUP_REPLY_CODE_STK) by (rewrite length_skipn; lia).
    exact (astr_atR_kept _ _ _ _ (x + 5) (skipn 5 s) KEEP3 Hsk Hb1 Hb2 ltac:(lia)).
  + unfold astr_len. rewrite length_skipn.
    eapply (aread_ok_kept SEGS 0 (3 * ESTACK) W regs _ mem _ (spZ regs - SUP_REPLY_CODE_STK) (spZ regs) (x + 5) _ KEEP3);
      [| lia | lia | lia | rewrite Hsp4, Hes; lia | lia].
    apply (aread_ok_of_block SEGS B LAWS 0 ly S W regs mem md p k (x + 5) _ HAR Hpk); lia.
  + (* the `+ 8` band premise of the atoi wrapper on s + 5, in the same block (a Theorem Labs lane's string-band.md section 4,
       0x8a3f8, class H) *)
    assert (Hb5 : in_blockA (ablocks B ly S) (x + 5) (astr_len (skipn 5 s) + 1)).
    { unfold in_blockA, astr_len. rewrite length_skipn. exists p, k. split; [exact Hpk | lia]. }
    exact (PaLibH.amem8_of_blockA SEGS B LAWS ly S W mem md (x + 5) (astr_len (skipn 5 s)) HAR Hb5 ltac:(unfold astr_len; lia)).
  + unfold astr_len. rewrite length_skipn. replace (x + 5 + Z.of_nat (length s - 5)) with (x + Z.of_nat (length s)) by lia.
    exact (atail_vis_kept SEGS W mem _ _ _ _ KEEP3 HTAIL ltac:(lia) HTB ltac:(lia)).
  + exact (rd32_kept _ _ _ _ (as_errno B) ev KEEP3 HERR ltac:(lia) ltac:(lia) ltac:(lia)).
  + (* the string apart from the errno cell (RtNumber.v aatoi_realizes; a Theorem Labs lane's PASS4-REFIT.md E.0.2): s + 5 lies
       in the heap block (p, k), whose bytes are not image bytes (RecBLemmas.recb_heap_noimg_m), and the errno cell
       (0x5e4074 by YF0m.ts_errno of HB) is image bytes (IMG's cif_errno: read-only image bytes) *)
    pose proof (YF0m.ts_errno B HB) as Eerr. unfold YF0m.TFIB_ERRNO in Eerr.
    unfold astr_len. rewrite length_skipn.
    destruct (Z_le_gt_dec (x + 5 + Z.of_nat (length s - 5) + 1) (as_errno B)) as [Hlo|Hlo]; [left; exact Hlo|].
    destruct (Z_le_gt_dec (as_errno B + 4) (x + 5)) as [Hhi|Hhi]; [right; exact Hhi|]. exfalso.
    assert (Hea : as_errno B <= Z.max (x + 5) (as_errno B) < as_errno B + 4) by lia.
    exact (RecBLemmas.recb_heap_noimg_m B ly S W mem md p k (Z.max (x + 5) (as_errno B)) HAR Hpk ltac:(lia)
      (seg_rom_in_img SEGS (Z.max (x + 5) (as_errno B)) ltac:(lia) (cif_errno SEGS B IMG (Z.max (x + 5) (as_errno B)) Hea))).
  + exact (HROMk _ KEEP3).
  + cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & (HQa & _) & _).
    unfold apost_base. exists ly, S, regs4, mem4, md4.
    split; [reflexivity|]. split; [exact HJ4|]. split; [exact (aregs_preserved_trans _ _ _ HPT3 HP4)|].
    split; [|split; [apply Permutation_refl | split; reflexivity]].
    rewrite HQa. unfold reply_code_a. destruct (list_eq_dec Z.eq_dec _ _) as [_|Hne]; [reflexivity | exfalso; exact (Hne HPFX)].
- (* the answer is not 0: 0x8a3c8 .. 0x8a3dc return -999 *)
  assert (HNZ : getr regs2 10 <> w64 0).
  { intros HZ. rewrite branch_eq_U in Hc. apply Z.eqb_neq in Hc. apply Hc. unfold U. f_equal. cbn [sv_denot].
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned, A44, HZ. reflexivity. }
  assert (HNP : map bv_unsigned (firstn 5 s) <> [114; 101; 115; 112; 32]) by (intros HP; exact (HNZ (proj2 HQ2' HP))).
  paj_run_tok RUN HS HJ2 SHOK3 src_Bspan.
  { awr_ok_tac. exact Usp3. }
  prreg HS (1%bv : bv 5) F1. prreg HS (10%bv : bv 5) F10.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold apost_base.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end.
  split; [rewrite F1, OLD3, E1 by lia; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ Ec _ _ regs src_extra HS); [exact HAE3 | vm_compute; reflexivity]|].
  split; [|split; [apply Permutation_refl | split; reflexivity]].
  rewrite F10. unfold reply_code_a. destruct (list_eq_dec Z.eq_dec _ _) as [HP|_];
    [exfalso; exact (HNP HP) | first [reflexivity | apply bv_eq; reflexivity]].
Qed.
End e.
End f.
End d.
