(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the snprintf call of sup_instance_verb's ASan+UBSan walk (plugin-hostd/
   fuzz_command, image fuzz_command.asan-ubsan, the inlined arg_i: `snprintf(b, 16, "%d", ledger)` at 0x8ba24, b the
   bytes 32 .. 47 of the live class-0 side-stack frame F, format "%d" at 0x21f40) in a walk's journal form, over the
   snprintf contract as a Theorem Labs lane's FR_cmd mirror states it (a working branch 0934cb146c3: lib/B/Rt/RtFormat.v
   asnprintf_realizes = RtPFCmd.asnprintf_sh = cmd_asnprintf_realizes at FR_cmd, window CMD_SNP_K = 2 * ESTACK, the
   read-only list CMD_SNP_CR, rt_rom_view for the unowned read-only bytes, the destination's slack word
   amem_range d (sn_len (n - 1) T + 8), FP-existential post).
   The journal bookkeeping around the call (ecall_pre_at, awr_byte, ajournal_after_write) is the one of the pass-3 rule
   sivb_snprintf_atS (lib/B/Prog/sup_instance_verb_aux.v, from lib/A/Prog/arg_i_s0.v aj_snprintf_atS,
   a working branch 12dc52bfe84); the contract's premises are discharged here from the journal, the frame, the
   per-binary record facts of lib/B/Prog/CmdRec*.v (by exact, at AR_laws_ok / HB / cmd_img_facts_tfib B HB) and
   arodata_okP at the call:
   - rt_rom_view: CmdRecImg.cmd_consts_view_snp from arodata_okP;
   - the format family: FR_cmd_intro, its last premise fr_lit_ok (the format a nonempty literal below the GOT word,
     no string argument) by computation (a Theorem Labs lane's PASS4-REFIT.md E.0.4);
   - the stack-protector cells 0xa6bf8 -> 0x604158: CmdRecCells.cmd_rec_cells;
   - the format's bytes: CmdRecRo.cmd_ro_obj_bytes; its shadow and hull: CmdRecBase.cmd_aread_ok_chk;
   - dest_ok, amem_range with its 8-byte slack, the shadow hull and dest_off_globals of b: the frame (AR_frames_law,
     frames_bounds, PaLibF.frame_al64 / shadow_hull_vis_of_frame, PaLibH.amem_range_sub_app / frm_off_imgP: b + 12 + 8
     <= F + 64); b's addressability: its two shadow granules;
   - the window, its presence, ecall_pre: the journal.
   The text is PF.pf_dec ledger (at most 11 bytes), so the 16-byte buffer takes it whole: the shared post's
   sn_bytes (16 - 1) T is dec ledger and its terminator. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtPFupoison RtPFPf RtPFShared RtPFSx RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdRecBase CmdRecCells CmdRecRo CmdRecImg CmdRecRest.
(* the plain proof's facts on "%d" (lib/Prog/arg_i.v:36-54); B has no arg_i walk, so the module is named by its full
   path *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require arg_i.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module PAI := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.arg_i.

(* --- the text snprintf(b, 16, "%d", ledger) writes ----------------------------------------------------------- *)
Lemma sivb_snp_dec_len : forall v, -2^31 <= v < 2^31 -> length (PF.pf_dec v) = length (dec v).
Proof. intros v Hv. rewrite <- (PAI.ai_pf_dec v Hv). unfold PF.pf_bytes. rewrite length_map. reflexivity. Qed.
(* every character of the text is a byte *)
Lemma sivb_snp_digits_rng : forall fuel x acc, 0 <= x -> Forall (fun c => 0 <= c < 256) acc ->
Forall (fun c => 0 <= c < 256) (PF.pf_digits fuel x acc).
Proof.
induction fuel as [|f IH]; intros x acc Hx Hacc; cbn [PF.pf_digits]; [exact Hacc|].
destruct (Z.ltb_spec x 10) as [Hl|Hl].
- constructor; [lia | exact Hacc].
- apply IH; [apply Z.div_pos; lia | constructor; [pose proof (Z.mod_pos_bound x 10 ltac:(lia)); lia | exact Hacc]].
Qed.
Lemma sivb_snp_pf_dec_rng : forall v, Forall (fun c => 0 <= c < 256) (PF.pf_dec v).
Proof.
intros v. unfold PF.pf_dec. destruct (Z.ltb_spec v 0) as [Hv|Hv].
- constructor; [lia | apply sivb_snp_digits_rng; [lia | constructor]].
- apply sivb_snp_digits_rng; [lia | constructor].
Qed.
(* the buffer is 16 bytes and the text at most 11: the written part is the whole text and its terminator *)
Lemma sivb_snp_sn_len : forall v, -2^31 <= v < 2^31 ->
sn_len (16 - 1) (PF.pf_dec v) = Z.of_nat (length (dec v)) + 1.
Proof.
intros v Hv. pose proof (dec_length v Hv). pose proof (sivb_snp_dec_len v Hv).
unfold sn_len, sn_bytes. rewrite length_app, firstn_all2 by (change (Z.to_nat (16 - 1)) with 15%nat; lia).
cbn [length]. lia.
Qed.
Lemma sivb_snp_sn_bytes : forall v, -2^31 <= v < 2^31 -> sn_bytes (16 - 1) (PF.pf_dec v) = PF.pf_dec v ++ [0].
Proof.
intros v Hv. pose proof (dec_length v Hv). pose proof (sivb_snp_dec_len v Hv).
unfold sn_bytes. rewrite firstn_all2 by (change (Z.to_nat (16 - 1)) with 15%nat; lia). reflexivity.
Qed.
(* the shared post's bytes at b are dec ledger and its terminator *)
Lemma sivb_snp_bytes_of_sn : forall (rd : reader) d v, -2^31 <= v < 2^31 ->
(forall i, 0 <= i < sn_len (16 - 1) (PF.pf_dec v) ->
 rd (d + i) = Some (nth (Z.to_nat i) (sn_bytes (16 - 1) (PF.pf_dec v)) 0)) ->
abytes_atR rd d (dec v ++ [Z_to_bv 8 0]).
Proof.
intros rd d v Hv H i Hi.
rewrite (sivb_snp_sn_len v Hv), (sivb_snp_sn_bytes v Hv) in H.
rewrite length_app in Hi. cbn [length] in Hi.
rewrite (H (Z.of_nat i)) by lia. rewrite Nat2Z.id. f_equal.
assert (Hr : 0 <= nth i (PF.pf_dec v ++ [0]) 0 < 256).
{ assert (HF : Forall (fun c => 0 <= c < 256) (PF.pf_dec v ++ [0]))
    by (apply Forall_app; split; [apply sivb_snp_pf_dec_rng | constructor; [lia | constructor]]).
  rewrite Forall_forall in HF. apply HF. apply nth_In. rewrite length_app. cbn [length].
  pose proof (sivb_snp_dec_len v Hv). lia. }
rewrite <- (PAI.ai_pf_dec v Hv). unfold PF.pf_bytes.
change [Z_to_bv 8 0] with (map (Z_to_bv 8) [0]). rewrite <- map_app. rewrite map_nth.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. symmetry. apply Z.mod_small. exact Hr.
Qed.

(* --- the format "%d" at 0x21f40 (CmdRo.v RO_lit_21f40) ------------------------------------------------------- *)
Lemma sivb_snp_fmt_rd : forall (rd : reader), abytes_atR rd 0x21f40 RO_lit_21f40 ->
forall i, 0 <= i <= Z.of_nat (length PAI.AI_FMT) -> rd (0x21f40 + i) = Some (nth (Z.to_nat i) (PAI.AI_FMT ++ [0]) 0).
Proof.
intros rd Hb i Hi. change (Z.of_nat (length PAI.AI_FMT)) with 2 in Hi.
replace (0x21f40 + i) with (0x21f40 + Z.of_nat (Z.to_nat i)) by lia.
rewrite (Hb (Z.to_nat i)) by (change (length RO_lit_21f40) with 3%nat; lia).
f_equal. assert (Hc : i = 0 \/ i = 1 \/ i = 2) by lia.
destruct Hc as [-> | [-> | ->]]; vm_compute; reflexivity.
Qed.

(* --- b's addressability from its two shadow granules -------------------------------------------------------- *)
Lemma sivb_snp_addr2 : forall (rd : reader) d w, d mod 8 = 0 -> 0 <= w <= 16 ->
rd (SHADOW_OFF + d / 8) = Some 0 -> rd (SHADOW_OFF + d / 8 + 1) = Some 0 ->
range_addressable rd SHADOW_OFF d w.
Proof.
intros rd d w Hd Hw H0 H1 x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr.
assert (Hq : x / 8 = d / 8 \/ x / 8 = d / 8 + 1) by (Z.div_mod_to_equations; lia).
destruct Hq as [-> | ->]; [exact H0 | rewrite Z.add_assoc; exact H1].
Qed.

(* --- the read-only words of the snprintf chain (RtPFCmd.v CMD_SNP_CR) ---------------------------------------- *)
(* they lie in the image's range *)
Lemma sivb_snp_cr_img : forall r, In r CMD_SNP_CR -> 0x10000 <= fst r /\ 0 <= snd r /\ fst r + snd r <= 0x606000.
Proof.
intros r Hr. pose proof (proj1 (forallb_forall _ _) cmd_snp_cr_img r Hr) as Hb.
unfold in_cmd_img, CMD_IMG_LO, CMD_IMG_HI in Hb. apply andb_prop in Hb as [Hb H3]. apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1, H2, H3. lia.
Qed.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* the per-binary allocator record (a Theorem Labs lane's lib/B/YF0m.v) *)
Hypothesis HB : CmdBSyms B.
(* the per-binary image facts, as the walks carry them (a Theorem Labs lane 09:2xZ): a Theorem Labs lane's CmdRecImg.v cmd_img_facts_tfib at
   the walk's abstract segments *)
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.

(* --- the snprintf call at 0x8ba24 in a walk's journal form --------------------------------------------------- *)
Lemma sivb_snprintf_atS : forall pc,
(forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B pc 0xa6bf8 0x604158) ->
forall (W : world SEGS) regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw (F : Z) pos (ledger : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> CMD_SNP_K - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 10 = w64 (F + 32) -> getr regsT 11 = w64 16 -> getr regsT 12 = w64 0x21f40 -> getr regsT 13 = w64 ledger ->
- 2 ^ 31 <= ledger < 2 ^ 31 ->
(* b's frame is this call's own class-0 frame (aj_stack_malloc_at, YCbq.v:2076, heads own with it), so a write to it
   is the journal's in_frames case of awr_byte; F is its address, and b's two shadow granules are unpoisoned (00) *)
In (0, pos) own -> F = frame_addr lyc 0 pos ->
aview SEGS (w_H W) memT (SHADOW_OFF + (F + 32) / 8) = Some 0 ->
aview SEGS (w_H W) memT (SHADOW_OFF + (F + 32) / 8 + 1) = Some 0 ->
arodata_okP SEGS CMD_RLO CMD_RHI B (aview SEGS (w_H W) memT) ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists (fx' : YK11.FPState) regs2 mem2 md2,
 c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\
 (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
 Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
 ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
 aregs_preserved regsT regs2 /\
 getr regs2 10 = w64 (Z.of_nat (length (dec ledger))) /\
 abytes_at SEGS W mem2 (F + 32) (dec ledger ++ [Z_to_bv 8 0]) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 48) ->
  ~ (sp0 + o - CMD_SNP_K <= a < sp0 + o) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
 (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
 same_but_materialized mdc md2).
Proof.
intros pc AS W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw F pos ledger
  HJ Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Ha0 Ha1 Ha2 Ha3 Hled Hown EF Hsh0 Hsh1 HROD Hfrm.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HKv : CMD_SNP_K = 8192) by reflexivity.
(* the frame: live, 64-aligned, below the allocator's ceiling, off the image *)
assert (Hin : In (0, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
destruct (frames_bounds SEGS B LAWS lyc Sc W memT mdc 0 pos HAR Hin) as (Hf0 & Hfc & Hfapp).
destruct (frame_al64 SEGS B lyc Sc W memT mdc 0 pos HAR Hin) as (Hf64 & _ & _).
rewrite Hfb in Hfc, Hfapp. rewrite <- EF in Hf0, Hfc, Hfapp, Hf64.
assert (Hoff : F + 64 <= 0x10000 \/ 0x606000 <= F)
  by (rewrite EF; exact (frm_off_imgP B lyc Sc W memT mdc 0 pos HAR Hin)).
assert (Hd8 : (F + 32) mod 8 = 0) by (Z.div_mod_to_equations; lia).
(* the text *)
pose proof (dec_length ledger Hled) as HdL.
pose proof (sivb_snp_dec_len ledger Hled) as HTL.
pose proof (sivb_snp_sn_len ledger Hled) as Hsn.
(* the window: below sp, above the frame *)
assert (HspK : ly_stk_lo lyc + CMD_SNP_K <= spZ regsT) by (rewrite Eslo, Hsp'; lia).
assert (HspF : F + 64 <= spZ regsT - CMD_SNP_K) by (rewrite Hsp'; lia).
assert (Hsp47 : spZ regsT <= 2 ^ 47) by (rewrite Hsp'; lia).
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o);
    first [exact HJ | exact Hsp' | exact Hal | exact Hneg | exact Hgp | exact Htp | (rewrite Hra; exact Hraw) | lia]. }
(* the record facts at the call *)
destruct (cmd_rec_cells (SK := SK) SEGS B LAWS HB IMG lyc Sc W memT mdc HAR) as (_ & (Hgw & cval & Hcv) & _).
destruct (cmd_aread_ok_chk SEGS B LAWS HB lyc Sc W memT mdc 0x21f40 3 HAR
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [HfA HfH].
assert (Hlit : In (0x21f40, RO_lit_21f40) cmd_ro_list)
  by (unfold cmd_ro_list; repeat (first [left; reflexivity | right])).
pose proof (cmd_ro_obj_bytes (SK := SK) SEGS B LAWS HB IMG lyc Sc W memT mdc _ HAR HROD Hlit) as Hfb3.
cbn [fst snd] in Hfb3.
pose proof (cmd_consts_view_snp (SK := SK) SEGS B LAWS HB IMG CMD_RLO CMD_RHI W memT HROD) as HCV.
(* the call *)
pose proof (AS fx) as AS0.
unfold asnprintf_realizes, RtPFCmd.asnprintf_sh, sh_asnprintf_realizes in AS0.
eapply SRr_mono.
{ refine (AS0 lyc Sc W regsT memT mdc (F + 32) 16 0x21f40 [] (map (argZ regsT) [3; 4; 5; 6; 7]) (PF.pf_dec ledger) cval
    HPRE HspK _ Ha0 Ha1 Ha2 HCV _ _ Hgw Hcv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hfrm).
  - (* the window is present *)
    intros a Ha. apply Hpres. rewrite Hsp' in Ha. lia.
  - (* the read-only words are below 2^63 *)
    apply Forall_forall. intros r Hr. destruct (sivb_snp_cr_img r Hr) as (R1 & R2 & R3). lia.
  - (* ... and apart from the window and the written part *)
    apply Forall_forall. intros r Hr. destruct (sivb_snp_cr_img r Hr) as (R1 & R2 & R3).
    apply Forall_snp. unfold zdisjoint. cbn [fst snd]. split; lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - apply Forall_snp. unfold zdisjoint. cbn [fst snd]. split; lia.
  - apply Forall_snp. unfold zdisjoint. cbn [fst snd]. split; lia.
  - (* the arguments: a3..a7, no stack slot *)
    split; [rewrite app_nil_r; reflexivity | intros i Hi; cbn [length] in Hi; lia].
  - cbn [length]. lia.
  - cbn [length]. apply Forall_snp. unfold zdisjoint. cbn [fst snd]. split; lia.
  - (* the format family: "%d" with the int ledger *)
    apply (FR_cmd_intro _ _ _ _ _ PAI.AI_FMT PAI.AI_PS [PF.AInt ledger]).
    + split; [lia|]. split; [exact (sivb_snp_fmt_rd _ Hfb3)|].
      change (Z.of_nat (length PAI.AI_FMT) + 1) with 3.
      split; [apply Forall_snp; unfold zdisjoint; cbn [fst snd]; split; lia|].
      split; [unfold amem_range; left; lia|].
      split; [exact HfA | exact HfH].
    + exact PAI.ai_parse.
    + cbn [map arg_of pf_args_asan pf_arg_asan]. split; [|exact I]. split; [exact Hled|].
      assert (E13 : argZ regsT 3 = bv_unsigned (w64 ledger)) by (unfold argZ; rewrite <- Ha3; reflexivity).
      rewrite E13. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite (Z.mod_eq ledger (2 ^ 64)) by lia.
      replace (ledger - 2 ^ 64 * (ledger / 2 ^ 64)) with (ledger + (- (2 ^ 32 * (ledger / 2 ^ 64))) * 2 ^ 32) by lia.
      rewrite Z.mod_add by lia. reflexivity.
    + exact (PAI.ai_text ledger).
    + exact I.
    + vm_compute. reflexivity.
  - lia.
  - rewrite HTL. lia.
  - lia.
  - lia.
  - (* the window and the written part are apart *)
    apply pairwise_snp. unfold zdisjoint. cbn [fst snd]. lia.
  - (* dest_ok: bytes of the live frame, none of the record's, below the window *)
    intros a Ha.
    destruct (al_frames _ _ LAWS lyc Sc W memT mdc 0 pos HAR Hin) as (_ & _ & Hb & _).
    rewrite <- EF, Hfb in Hb.
    destruct (Hb a ltac:(lia)) as [Hp Hno].
    split; [apply (apresent_writable SEGS); exact Hp|]. split; [exact Hno | lia].
  - (* b + |dec ledger| + 1 + 8 <= F + 32 + 20 <= F + 64: the slack word stays inside the frame *)
    apply (amem_range_sub_app F 64 (F + 32) _ Hfapp Hfc); lia.
  - apply sivb_snp_addr2; [exact Hd8 | lia | exact Hsh0 | exact Hsh1].
  - apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W memT mdc 0 pos (F + 32) _ HAR Hin);
      rewrite <- ?EF, ?Hfb; lia.
  - (* dest_off_globals *)
    unfold zdisjoint, CMD_IMG_LO, CMD_IMG_HI. cbn [fst snd]. lia. }
cbv beta. intros W2 c2 _ (-> & fx' & regs2 & mem2 & md2 & -> & Hf1 & Hf2 & HAR2 & HP & Hsame & Hres & Hbytes & Hfr & Hpres2).
split; [reflexivity|]. exists fx', regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact Hf1|]. split; [exact Hf2|].
assert (Hfr' : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 48) -> ~ (sp0 + o - CMD_SNP_K <= a < sp0 + o) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a).
{ intros a Ha Hnd Hns. apply (Hfr a Ha); [lia | rewrite Hsp'; exact Hns]. }
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => (F + 32 <= a < F + 48) \/ (sp0 + o - CMD_SNP_K <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply (Hfr' a Ha); intros H'; apply Hna; [left | right]; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left.
    + right; right; right; left. exists 0, pos. split; [exact Hown|]. left.
      unfold in_zr. cbn [fst snd]. rewrite <- EF, Hfb. lia.
    + left. lia.
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|].
split; [rewrite Hres, HTL; reflexivity|].
split; [apply (proj1 (abytes_atR_view SEGS W mem2 _ _)); exact (sivb_snp_bytes_of_sn _ (F + 32) ledger Hled Hbytes)|].
split; [exact Hfr'|]. split; [exact Hpres2 | exact Hsame].
Qed.
End b.
End a.

Print Assumptions sivb_snprintf_atS.
