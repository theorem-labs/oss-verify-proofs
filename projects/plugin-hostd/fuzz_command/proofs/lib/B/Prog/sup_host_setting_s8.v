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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_instance_verb_snp.v, with its module names changed; 546 of its 633 lines of code are new or changed and 193 lines of the source are left out. *)
(* A segment lemma of sup_host_setting's ASan+UBSan walk (plugin-hostd/fuzz_command, fuzz_command.asan-ubsan), on the
   points and statements of sup_host_setting_s0.v:
   - hs_seg_al: from AL (0x8b658, back from arg_line) the unpoison of b = F + 32 (`sb zero,4(s9); sb zero,5(s9)`: the
     frame's shadow bytes 4 and 5 := 0), a2 := "%d" (0x8b660/0x8b664 `auipc a0,0xfff97; addi a2,a0,-0x720`, the
     listing's object A_OBJ 51 = 0x21f40), the call snprintf(b, 16, "%d", ntok) of the snprintf wrapper (0x451d0, at
     0x8b674), then a0 := c, a1 := b and the call arg_s(c, b) (0x8a820, at 0x8b680), back at AS1 (0x8b684).
   B inlines arg_i here. The snprintf step is a Theorem Labs lane's PASS4-REFIT.md section E on the B kit (lib/B/Prog/PaFx.v):
   the shared contract hh_snprintf at the current FP state, turned into art form by srr_art_postF_of_pf and into the
   whole call's journal by aj_art_own_atF (b lies in this call's own class-0 frame (0, fpos)); the contract's
   premises are discharged as a Theorem Labs lane's sup_instance_verb lane does for the same code (a working branch
   lib/B/Prog/sup_instance_verb_snp.v sivb_snprintf_atS, compiled there): consts_view from
   CmdRecImg.cmd_consts_view_snp over hh_img, the stack-protector cells from CmdRecCells.cmd_rec_cells, the format's
   bytes and shadow from CmdRecRo.cmd_ro_obj_bytes / CmdRecBase.cmd_aread_ok_chk, b's dest_ok / amem_range / hull
   from the frame, b's addressability from the two shadow bytes the run zeroed. The rounding mode at the call is 0:
   hs_cx's last conjunct for i_fx x and FXR (fxrel_frm0). The wrapper returns at a new FP state fx1 with
   fxrel fx fx1 (PaFx's fxrel); the rest of the segment (hs8_tail, from 0x8b678 on) is proved at every FP state and
   applied at fx1, with hs_fxrel (i_fx x) fx1 = fxrel_trans of FXR and that relation. arg_s's post is apost_base (it
   reaches no printf wrapper), so it returns at fx1 and ST_AS1 is applied at fx1.
   The text is dec ntok (1 <= ntok <= 64: at most 2 digits) and its NUL at b; arg_s takes b in the frame / own form of
   its string premise (afobj: inside the live frame (0, fpos), 8-aligned, addressable by the two zero shadow bytes),
   its tail word visible because it lies in the frame. The frame chain at arg_s comes from hs3_achain.
   No report and no UBSan edge: 0x8b658 .. 0x8b684 holds no branch, no `__asan_report_*` call and no `unimp`
   (sup_host_setting.B.dis.txt: the branch list has none between 0x8b5c4 and 0x8b68c, the report calls are at
   0x8b7c4 and 0x8b8d0 .. 0x8b8f4, the one trap is 0x8b8c0). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtPFupoison RtPFPf RtPFShared RtPFSx RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaLibF PaLibG PaLibH PaSB PaArt PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdRecBase CmdRecCells CmdRecRo CmdRecImg CmdRecRest CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_calls_free_c rec_canonical_c record_c arg_line_c arg_s_c xmalloc_c mix_call_c sup_host_setting_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_host_setting_aux sup_host_setting_s1 sup_host_setting_s0 sup_host_setting_s3 sup_host_setting_s4.
(* the plain proof's facts on "%d" (lib/Prog/arg_i.v); B has no arg_i walk, so the module is named by its full path *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require arg_i.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module PAI := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.arg_i.

(* 0x8b678: back from the snprintf wrapper (`mv a0,s11; mv a1,s7; jal arg_s`) *)
Definition HS8_ARGS : Z := 0x5148.

(* ---- the text snprintf(b, 16, "%d", ntok) writes ---- *)
Lemma hs8_dec_len : forall v, -2^31 <= v < 2^31 -> length (PF.pf_dec v) = length (dec v).
Proof. intros v Hv. rewrite <- (PAI.ai_pf_dec v Hv). unfold PF.pf_bytes. rewrite length_map. reflexivity. Qed.
(* every character of the text is a nonzero byte *)
Lemma hs8_digits_rng : forall fuel x acc, 0 <= x -> Forall (fun c => 0 < c < 256) acc ->
Forall (fun c => 0 < c < 256) (PF.pf_digits fuel x acc).
Proof.
induction fuel as [|f IH]; intros x acc Hx Hacc; cbn [PF.pf_digits]; [exact Hacc|].
destruct (Z.ltb_spec x 10) as [Hl|Hl].
- constructor; [lia | exact Hacc].
- apply IH; [apply Z.div_pos; lia | constructor; [pose proof (Z.mod_pos_bound x 10 ltac:(lia)); lia | exact Hacc]].
Qed.
Lemma hs8_pf_dec_rng : forall v, Forall (fun c => 0 < c < 256) (PF.pf_dec v).
Proof.
intros v. unfold PF.pf_dec. destruct (Z.ltb_spec v 0) as [Hv|Hv].
- constructor; [lia | apply hs8_digits_rng; [lia | constructor]].
- apply hs8_digits_rng; [lia | constructor].
Qed.
(* the buffer is 16 bytes and the text at most 11: the written part is the whole text and its terminator *)
Lemma hs8_sn_len : forall v, -2^31 <= v < 2^31 ->
sn_len (16 - 1) (PF.pf_dec v) = Z.of_nat (length (dec v)) + 1.
Proof.
intros v Hv. pose proof (dec_length v Hv). pose proof (hs8_dec_len v Hv).
unfold sn_len, sn_bytes. rewrite length_app, firstn_all2 by (change (Z.to_nat (16 - 1)) with 15%nat; lia).
cbn [length]. lia.
Qed.
Lemma hs8_sn_bytes : forall v, -2^31 <= v < 2^31 -> sn_bytes (16 - 1) (PF.pf_dec v) = PF.pf_dec v ++ [0].
Proof.
intros v Hv. pose proof (dec_length v Hv). pose proof (hs8_dec_len v Hv).
unfold sn_bytes. rewrite firstn_all2 by (change (Z.to_nat (16 - 1)) with 15%nat; lia). reflexivity.
Qed.
(* the shared post's bytes at b are the string dec v *)
Lemma hs8_str_of_sn : forall (rd : reader) d v, -2^31 <= v < 2^31 ->
(forall i, 0 <= i < sn_len (16 - 1) (PF.pf_dec v) ->
 rd (d + i) = Some (nth (Z.to_nat i) (sn_bytes (16 - 1) (PF.pf_dec v)) 0)) ->
astr_atR rd d (dec v).
Proof.
intros rd d v Hv H.
assert (HR : Forall (fun c => 0 < c < 256) (PF.pf_dec v)) by apply hs8_pf_dec_rng.
split.
- intros i Hi.
  rewrite (hs8_sn_len v Hv), (hs8_sn_bytes v Hv) in H.
  rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (H (Z.of_nat i)) by lia. rewrite Nat2Z.id. f_equal.
  assert (Hr : 0 <= nth i (PF.pf_dec v ++ [0]) 0 < 256).
  { assert (HF : Forall (fun c => 0 <= c < 256) (PF.pf_dec v ++ [0])).
    { apply Forall_app. split; [|constructor; [lia | constructor]].
      apply (Forall_impl _ (fun c Hc => conj (Z.lt_le_incl _ _ (proj1 Hc)) (proj2 Hc)) HR). }
    rewrite Forall_forall in HF. apply HF. apply nth_In. rewrite length_app. cbn [length].
    pose proof (hs8_dec_len v Hv). lia. }
  rewrite <- (PAI.ai_pf_dec v Hv). unfold PF.pf_bytes.
  change [Z_to_bv 8 0] with (map (Z_to_bv 8) [0]). rewrite <- map_app. rewrite map_nth.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. symmetry. apply Z.mod_small. exact Hr.
- rewrite <- (PAI.ai_pf_dec v Hv). unfold PF.pf_bytes. intros Hin.
  apply in_map_iff in Hin as (c & Hc & Hcin).
  pose proof (proj1 (Forall_forall _ _) HR c Hcin) as Hr. cbv beta in Hr.
  assert (Hu : bv_unsigned (Z_to_bv 8 c) = c).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia. }
  rewrite Hc in Hu. vm_compute in Hu. lia.
Qed.

(* ---- the format "%d" at 0x21f40 (CmdRo.v RO_lit_21f40) ---- *)
Lemma hs8_fmt_rd : forall (rd : reader), abytes_atR rd 0x21f40 RO_lit_21f40 ->
forall i, 0 <= i <= Z.of_nat (length PAI.AI_FMT) -> rd (0x21f40 + i) = Some (nth (Z.to_nat i) (PAI.AI_FMT ++ [0]) 0).
Proof.
intros rd Hb i Hi. change (Z.of_nat (length PAI.AI_FMT)) with 2 in Hi.
replace (0x21f40 + i) with (0x21f40 + Z.of_nat (Z.to_nat i)) by lia.
rewrite (Hb (Z.to_nat i)) by (change (length RO_lit_21f40) with 3%nat; lia).
f_equal. assert (Hc : i = 0 \/ i = 1 \/ i = 2) by lia.
destruct Hc as [-> | [-> | ->]]; vm_compute; reflexivity.
Qed.

(* ---- b's addressability from its two shadow granules ---- *)
Lemma hs8_addr2 : forall (rd : reader) d w, d mod 8 = 0 -> 0 <= w <= 16 ->
rd (SHADOW_OFF + d / 8) = Some 0 -> rd (SHADOW_OFF + d / 8 + 1) = Some 0 ->
range_addressable rd SHADOW_OFF d w.
Proof.
intros rd d w Hd Hw H0 H1 x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr.
assert (Hq : x / 8 = d / 8 \/ x / 8 = d / 8 + 1) by (Z.div_mod_to_equations; lia).
destruct Hq as [-> | ->]; [exact H0 | rewrite Z.add_assoc; exact H1].
Qed.

(* ---- the read-only words of the snprintf chain (RtPFCmd.v CMD_SNP_CR) lie in the image's range ---- *)
Lemma hs8_cr_img : forall r, In r CMD_SNP_CR -> 0x10000 <= fst r /\ 0 <= snd r /\ fst r + snd r <= 0x606000.
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
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : @cmd_img_facts SK SEGS B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

(* snprintf(F + 32, 16, "%d", v) into the 16 bytes 32 .. 47 of the live class-0 frame F at (0, pos), in a Theorem Labs lane's art
   form at the FP state it returns (PaFx.v srr_art_postF_of_pf over the shared contract) *)
Lemma hs8_snp : forall ly S (W : world SEGS) regs mem md (F v pos : Z),
  asnprintf_realizes SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158 ->
  ecall_pre SEGS B ly S W regs mem md ->
  ly_stk_lo ly + CMD_SNP_K <= spZ regs ->
  (forall a, spZ regs - CMD_SNP_K <= a < spZ regs -> apresent (w_H W) mem a) ->
  F + 64 <= spZ regs - CMD_SNP_K -> alloc_ceiling + CMD_SNP_K <= spZ regs -> spZ regs <= 2 ^ 47 ->
  getr regs 10 = w64 (F + 32) -> getr regs 11 = w64 16 -> getr regs 12 = w64 0x21f40 -> getr regs 13 = w64 v ->
  -2^31 <= v < 2^31 ->
  arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem) ->
  In (0, pos) (frames S) -> F = frame_addr ly 0 pos ->
  rdW W mem (SHADOW_OFF + (F + 32) / 8) = Some 0 -> rdW W mem (SHADOW_OFF + (F + 32) / 8 + 1) = Some 0 ->
  frm0 fx ->
  SRr SEGS W (cfg_at SEGS (SIG CS___interceptor_trampoline_snprintf) regs mem md)
   (art_postF SEGS B CMD_SNP_K ly S W regs mem md (fun a => F + 32 <= a < F + 32 + sn_len (16 - 1) (PF.pf_dec v))
     (fun regs' mem' => getr regs' 10 = w64 (Z.of_nat (length (PF.pf_dec v))) /\
       forall i, 0 <= i < sn_len (16 - 1) (PF.pf_dec v) ->
       rdW W mem' (F + 32 + i) = Some (nth (Z.to_nat i) (sn_bytes (16 - 1) (PF.pf_dec v)) 0))).
Proof.
intros ly S W regs mem md F v pos AS HPRE HspK Hscr HspF HspC Hsp47 Ha0 Ha1 Ha2 Ha3 Hled HROD Hin EF Hsh0 Hsh1 Hfrm.
pose proof HPRE as (HAR & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HKv : CMD_SNP_K = 8192) by reflexivity.
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity.
destruct (frames_bounds SEGS B LAWS ly S W mem md 0 pos HAR Hin) as (Hf0 & Hfc & Hfapp).
destruct (frame_al64 SEGS B ly S W mem md 0 pos HAR Hin) as (Hf64 & _ & _).
rewrite Hfb in Hfc, Hfapp. rewrite <- EF in Hf0, Hfc, Hfapp, Hf64.
assert (Hoff : F + 64 <= 0x10000 \/ 0x606000 <= F)
  by (rewrite EF; exact (frm_off_imgP B ly S W mem md 0 pos HAR Hin)).
assert (Hd8 : (F + 32) mod 8 = 0) by (Z.div_mod_to_equations; lia).
pose proof (dec_length v Hled) as HdL.
pose proof (hs8_dec_len v Hled) as HTL.
pose proof (hs8_sn_len v Hled) as Hsn.
destruct (cmd_rec_cells (SK := SK) SEGS B LAWS HB IMG ly S W mem md HAR) as (_ & (Hgw & cval & Hcv) & _).
destruct (cmd_aread_ok_chk SEGS B LAWS HB ly S W mem md 0x21f40 3 HAR
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [HfA HfH].
assert (Hlit : In (0x21f40, RO_lit_21f40) cmd_ro_list)
  by (unfold cmd_ro_list; repeat (first [left; reflexivity | right])).
pose proof (cmd_ro_obj_bytes (SK := SK) SEGS B LAWS HB IMG ly S W mem md _ HAR HROD Hlit) as Hfb3.
cbn [fst snd] in Hfb3.
pose proof (cmd_consts_view_snp (SK := SK) SEGS B LAWS HB IMG CMD_RLO CMD_RHI W mem HROD) as HCV.
apply (srr_art_postF_of_pf SEGS B CMD_SNP_K ly S W regs mem md _ (F + 32) (sn_len (16 - 1) (PF.pf_dec v))
  (sn_bytes (16 - 1) (PF.pf_dec v)) (Z.of_nat (length (PF.pf_dec v))) Hscr).
unfold asnprintf_realizes, RtPFCmd.asnprintf_sh, sh_asnprintf_realizes in AS.
refine (AS ly S W regs mem md (F + 32) 16 0x21f40 [] (map (argZ regs) [3; 4; 5; 6; 7]) (PF.pf_dec v) cval
    HPRE HspK Hscr Ha0 Ha1 Ha2 HCV _ _ Hgw Hcv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hfrm).
- apply Forall_forall. intros r Hr. destruct (hs8_cr_img r Hr) as (R1 & R2 & R3). lia.
- apply Forall_forall. intros r Hr. destruct (hs8_cr_img r Hr) as (R1 & R2 & R3).
  apply Forall_snp. unfold zdisjoint. cbn [fst snd]. split; lia.
- lia.
- lia.
- lia.
- lia.
- apply Forall_snp. unfold zdisjoint. cbn [fst snd]. split; lia.
- apply Forall_snp. unfold zdisjoint. cbn [fst snd]. split; lia.
- split; [rewrite app_nil_r; reflexivity | intros i Hi; cbn [length] in Hi; lia].
- cbn [length]. lia.
- cbn [length]. apply Forall_snp. unfold zdisjoint. cbn [fst snd]. split; lia.
- apply (FR_cmd_intro _ _ _ _ _ PAI.AI_FMT PAI.AI_PS [PF.AInt v]).
  + split; [lia|]. split; [exact (hs8_fmt_rd _ Hfb3)|].
    change (Z.of_nat (length PAI.AI_FMT) + 1) with 3.
    split; [apply Forall_snp; unfold zdisjoint; cbn [fst snd]; split; lia|].
    split; [unfold amem_range; left; lia|].
    split; [exact HfA | exact HfH].
  + exact PAI.ai_parse.
  + cbn [map arg_of pf_args_asan pf_arg_asan]. split; [|exact I]. split; [exact Hled|].
    assert (E13 : argZ regs 3 = bv_unsigned (w64 v)) by (unfold argZ; rewrite <- Ha3; reflexivity).
    rewrite E13. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_eq v (2 ^ 64)) by lia.
    replace (v - 2 ^ 64 * (v / 2 ^ 64)) with (v + (- (2 ^ 32 * (v / 2 ^ 64))) * 2 ^ 32) by lia.
    rewrite Z.mod_add by lia. reflexivity.
  + exact (PAI.ai_text v).
  + exact I.
  + (* fr_lit_ok: "%d" at 0x21f40 in the image, nonempty, no %s argument (RtPFCmd.v FR_cmd_intro) *)
    vm_compute. reflexivity.
- lia.
- rewrite HTL. lia.
- lia.
- lia.
- apply pairwise_snp. unfold zdisjoint. cbn [fst snd]. lia.
- intros a Ha.
  destruct (al_frames _ _ LAWS ly S W mem md 0 pos HAR Hin) as (_ & _ & Hb & _).
  rewrite <- EF, Hfb in Hb.
  destruct (Hb a ltac:(lia)) as [Hp Hno].
  split; [apply (apresent_writable SEGS); exact Hp|]. split; [exact Hno | lia].
- apply (amem_range_sub_app F 64 (F + 32) _ Hfapp Hfc); lia.
- apply hs8_addr2; [exact Hd8 | lia | exact Hsh0 | exact Hsh1].
- apply (shadow_hull_vis_of_frame SEGS B LAWS ly S W mem md 0 pos (F + 32) _ HAR Hin);
    rewrite <- ?EF, ?Hfb; lia.
- unfold zdisjoint, CMD_IMG_LO, CMD_IMG_HI. cbn [fst snd]. lia.
Qed.
End b.
End a.

(* ---- 0x8b678 .. AS1: a0 := c, a1 := b, the call of arg_s, at any FP state ---- *)
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
Hypothesis HH : hs_hyps B MT.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.

Lemma hs8_tail : forall x fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0,
  ST_AS1 B MT x -> hs_cx B MT x -> hs_fxrel (i_fx x) fx ->
  hs_mid B MT x fpos lyc Sc Wc memc mdc k (hs_k1 x) (hs_m1 MT x) (hs_l1 x) O1 [(b0, hs_b0 x)] Rest ->
  rec_repA B lyc Sc (rdW Wc memc) (rec_record (i_R x) REC_HOST_SETTING (hs_A1 x)) ((b0, hs_b0 x) :: O1) ->
  hs_regsF x fpos regs1 -> getr regs1 27 = w64 (rec_slot (i_R x)) ->
  astr_atR (rdW Wc memc) (hs_F x fpos + 32) (dec (Z.of_nat (length (i_toks x)))) ->
  rdW Wc memc (SHADOW_OFF + (hs_F x fpos + 32) / 8) = Some 0 ->
  rdW Wc memc (SHADOW_OFF + (hs_F x fpos + 32) / 8 + 1) = Some 0 ->
  SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + HS8_ARGS)) memc (seg_rom SEGS)) mdc) (hs_post B MT x).
Proof.
intros x fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 AS1 CX FXR MID REP RG R27 HSTR HSH0 HSH1.
pose proof CX as (HPRE & HROD & HRO & (Hpl & Hptok) & H10 & H11 & H12 & HNT & HLINE & Hp0 & Hp8 & HTA & HLPS & HPS &
  HTOKS & HWL & HREP0 & HFRM & HEV & HLIVE & HMO & HTAIL & HRM0).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof RG as ((K2 & K9 & K8 & K3 & K4 & K24 & K25 & K26) & R18 & R19 & R20 & R21 & R22 & R23).
pose proof MID as (HJ & Hk & HMLE & HBB & HFR & HFL & HBA).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (hs_slot_bounds (i_R x)) as (SL1 & SL2 & _ & _).
destruct (hs3_sp1 (spZ (i_regs x)) Hal16 ltac:(lia)) as (S1a & S1b & S1c).
pose proof hs3_stk as FS.
assert (HASS2 : ARG_S_STK = 16464) by (vm_compute; reflexivity).
assert (HPSB : as_prog_static B = recb_PG) by (rewrite (ts_prog B (hh_HB B MT HH)); reflexivity).
destruct (hs3_frame_facts B MT x fpos lyc Sc Wc memc mdc k CX HJ) as (HFin & EFA & EFL & HF4096 & HFceil & HF64).
assert (Hntok : 1 <= Z.of_nat (length (i_toks x)) <= 64) by lia.
pose proof (dec_length (Z.of_nat (length (i_toks x))) ltac:(lia)) as HdL.
pose (E := Eimg (Ereg regs1 [])).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (HS : st_ok_pi SEGS VAL E (mkSS HS8_ARGS sr_atoms [] None (mkFacts [(26%nat, mkAF HS_SB HS_SB 0)] [] []))
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + HS8_ARGS)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact (regs_ok_Eimg_Ereg regs1 []).
  - reflexivity.
  - constructor.
  - exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (EE 26%nat 26%bv eq_refl), K26. unfold w64.
    rewrite !unsigned_lit_small by (unfold HS_SB; lia). rewrite Z.pow_0_r, !Z.mod_1_r. unfold HS_SB. lia. }
assert (SHOK : sh_ok SEGS hs3_Bx [] E (mrestrict (w_H Wc) memc)) by constructor.
clearbody E.
(* 0x8b678 .. 0x8b680: a0 := c, a1 := b, the call of arg_s *)
paj_run_tok RUN HS HJ SHOK hs3_Bspan.
{ apply awr_ok_nil. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
assert (KEQ : forall a, aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
{ intros a. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|]. intros (r & Hr & _). destruct Hr. }
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
rewrite (EE 2%nat 2%bv eq_refl), K2 in P2. rewrite (EE 3%nat 3%bv eq_refl), K3 in P3. rewrite (EE 4%nat 4%bv eq_refl), K4 in P4.
rewrite (EE 8%nat 8%bv eq_refl), K8 in P8. rewrite (EE 9%nat 9%bv eq_refl), K9 in P9.
rewrite (EE 27%nat 27%bv eq_refl), R27 in P10. rewrite (EE 23%nat 23%bv eq_refl), R23 in P11.
rewrite (EE 18%nat 18%bv eq_refl), R18 in P18. rewrite (EE 19%nat 19%bv eq_refl), R19 in P19.
rewrite (EE 20%nat 20%bv eq_refl), R20 in P20. rewrite (EE 21%nat 21%bv eq_refl), R21 in P21.
rewrite (EE 22%nat 22%bv eq_refl), R22 in P22. rewrite (EE 23%nat 23%bv eq_refl), R23 in P23.
rewrite (EE 24%nat 24%bv eq_refl), K24 in P24. rewrite (EE 25%nat 25%bv eq_refl), K25 in P25.
rewrite (EE 26%nat 26%bv eq_refl), K26 in P26. rewrite (EE 27%nat 27%bv eq_refl), R27 in P27.
assert (Qsp : spZ (ms_regs ms) = spZ (i_regs x) + (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x))).
{ unfold spZ at 1. rewrite P2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (SIGAS : SIG CS_arg_s = BASE + AF_arg_s).
{ rewrite (hh_sigp B MT HH CS_arg_s ltac:(unfold cmd_prog_syms; repeat (first [left; reflexivity | right])));
  try (f_equal; vm_compute; reflexivity). }
rewrite SIGAS.
(* arg_s's premises at the call *)
pose proof HJ as (HARc & _ & _ & _ & _ & HFRSc & HNEVc & _).
destruct (hs3_rod_now B MT HH x fpos lyc Sc Wc (ms_mem ms) mdv k CX HJ) as [HRODc HROc].
assert (HFRc : hs_frame (rdW Wc (ms_mem ms)) (spZ (i_regs x)) (i_regs x))
  by exact (hs3_frame_kept_on (rdW Wc memc) _ _ _ (fun b _ => KEQ b) HFR).
destruct (hs3_achain B MT x fpos lyc Sc Wc (ms_mem ms) mdv k (ms_regs ms) CX HJ HFRc ltac:(rewrite Qsp; lia) P8)
  as (ch1 & HCH).
assert (REPc : rec_repA B lyc Sc (rdW Wc (ms_mem ms)) (rec_record (i_R x) REC_HOST_SETTING (hs_A1 x))
  ((b0, hs_b0 x) :: O1))
  by exact (hs_rec_kept B lyc Sc lyc Sc (rdW Wc memc) (rdW Wc (ms_mem ms)) _ _ REP (fun a _ => KEQ a)
    (fun pn H => proj1 (hs_rec_own B _ _ _ _ _ REP pn H))).
(* the string b = F + 32 in the frame: its bytes, its object (afobj), its tail word *)
assert (HSTRc : astr_atR (rdW Wc (ms_mem ms)) (hs_F x fpos + 32) (dec (Z.of_nat (length (i_toks x))))).
{ destruct HSTR as [HB1 HB2]. split; [|exact HB2]. intros i Hi. rewrite KEQ. exact (HB1 i Hi). }
assert (HFOBJ : afobj SEGS B lyc Sc Wc (ms_mem ms) (hs_F x fpos + 32)
  (Z.of_nat (length (dec (Z.of_nat (length (i_toks x))))) + 1)).
{ split.
  - exists 0, fpos. split; [exact HFin|]. split; [lia|]. rewrite EFA. split; [Z.div_mod_to_equations; lia|].
    split; [lia|]. change (fs_frame_bytes 0) with 64. lia.
  - split; [Z.div_mod_to_equations; lia|].
    apply hs8_addr2; [Z.div_mod_to_equations; lia | lia | rewrite KEQ; exact HSH0 | rewrite KEQ; exact HSH1]. }
assert (HTAILc : forall y, Some (dec (Z.of_nat (length (i_toks x)))) = Some y ->
  atail_vis SEGS Wc (ms_mem ms) (hs_F x fpos + 32 + Z.of_nat (length y))).
{ intros y Hy. injection Hy as <-. intros a Ha.
  destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HARc HFin) as (_ & _ & HFpres & _).
  rewrite EFA in HFpres. change (fs_frame_bytes 0) with 64 in HFpres.
  pose proof (Z.mod_pos_bound (hs_F x fpos + 32 + Z.of_nat (length (dec (Z.of_nat (length (i_toks x)))))) 8
    ltac:(lia)) as Hm.
  destruct (HFpres a ltac:(lia)) as [Hp _]. exact (aview_some_of_apresent SEGS _ _ _ Hp). }
assert (HEVc : st_nev Sc + EV_ARG_S <= EV_MAX).
{ unfold EV_SUP_HOST_SETTING, hs_k1, hs_k0 in *. unfold EV_ARG_LINE, EV_REC_CANONICAL, EV_ARG_S, EV_XMALLOC in *. lia. }
assert (HLIVEc : blocks_bytes Sc + LIVE_ARG_S (Some (dec (Z.of_nat (length (i_toks x))))) <= LIVE_MAX).
{ unfold LIVE_SUP_HOST_SETTING, hs_l1 in *.
  pose proof (Z.le_max_l (hs_words_len (i_toks x) + 1) 1).
  pose proof (Z.le_max_l (Z.of_nat (length (sarg (Some (join_sp (i_toks x))))) + 1) 1).
  unfold LIVE_ARG_S, LIVE_XMALLOC in *. lia. }
assert (HMOc : mo_ok MT Sc (XM_ARG_S MT (Some (dec (Z.of_nat (length (i_toks x))))))).
{ pose proof (hh_MTL B MT HH) as ML.
  apply (mok_station MT (i_S x) Sc (XM_SUP_HOST_SETTING MT (i_R x) (i_line x) (i_toks x)) (hs_m1 MT x) _ ML HMO HMLE).
  - exact (hs3_xs_nonneg B MT HH (Some (dec (Z.of_nat (length (i_toks x)))))).
  - unfold XM_SUP_HOST_SETTING, hs_m1, hs_m0.
    pose proof (hs3_xs_nonneg B MT HH (Some (join_sp (i_toks x)))).
    pose proof (hs3_xx_nonneg B MT HH (hs_words_len (i_toks x) + 1)).
    pose proof (mo_free_nonneg MT ML). lia. }
assert (HLEN : Z.of_nat (length (dec (Z.of_nat (length (i_toks x))))) + 1 <= LMAX + 1) by (unfold LMAX; lia).
(* arg_s writes c->nargs and c->args[1] *)
pose (FP1 := if Z.of_nat (length (hs_A1 x)) <? REC_ARGS_MAX
  then [(rec_slot (i_R x) + CALL_OFF_NARGS, rec_slot (i_R x) + CALL_OFF_NARGS + 4);
        (rec_slot (i_R x) + CALL_OFF_ARGS + 8 * Z.of_nat (length (hs_A1 x)),
         rec_slot (i_R x) + CALL_OFF_ARGS + 8 * Z.of_nat (length (hs_A1 x)) + 8)]
  else []).
assert (HFP1 : forall a, inFP FP1 a -> rec_slot (i_R x) <= a < rec_slot (i_R x) + CALL_SIZE).
{ intros a (r & Hr & Ha). unfold FP1 in Hr. cbn in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha;
  unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia. }
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS Wc (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_arg_s)) SUP_HOST_SETTING_STK
    (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [(0, fpos)] lyc Sc _ k
    ARG_S_STK FP1 EV_ARG_S (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x)) (getr (ms_regs ms) 1) ch1 _
    HJ Qsp S1b ltac:(lia) ltac:(rewrite HASS2; lia) ltac:(rewrite HASS2, FS; lia)).
  - rewrite P3. exact Hgp.
  - rewrite P4. exact Htp.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite P1, unsigned_lit_small by lia. lia.
  - replace (spZ (i_regs x) + (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x))) with (spZ (ms_regs ms)) by lia. exact HCH.
  - intros HPRE1.
    exact (hh_arg_s B MT HH fx lyc Sc Wc (ms_regs ms) (ms_mem ms) _ ch1 (rec_slot (i_R x)) (hs_F x fpos + 32)
      REC_HOST_SETTING (hs_A1 x) (Some (dec (Z.of_nat (length (i_toks x))))) (i_R x) ((b0, hs_b0 x) :: O1)
      HPRE1 HRODc HROc P10 P11 eq_refl REPc
      (or_intror (ex_intro _ (dec (Z.of_nat (length (i_toks x)))) (conj eq_refl (conj HSTRc
        (conj HLEN HFOBJ)))))
      HTAILc HEVc HLIVEc HMOc).
  - intros a Ha. right; right; right; right; left.
    destruct (hs3_rec_fp (i_O x) a (hs3_slot_rec (i_R x) a (HFP1 a Ha))) as [Hfp Hpg].
    split; [exact Hfp|]. split; [rewrite HPSB; exact Hpg | exact (hh_prog_img B MT HH a Hpg)].
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. pose proof (HFP1 a Ha).
    rewrite FS in Hw. unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia. }
(* back at AS1 0x8b684 *)
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md3 & -> & HJ2 & HJ2c & HP2 & HK2).
cbv zeta in HK2.
destruct HK2 as (HBB2 & HMLE2 & [(Hm6 & _) | (_ & p & Hp4096 & HPERM2 & HAPART & HREP2)]);
  [unfold hs_A1 in Hm6; cbn in Hm6; unfold REC_ARGS_MAX in Hm6; lia|].
pose proof HJ2c as (HAR2 & _ & _ & _ & _ & _ & _ & _ & J1 & J2 & J3 & J4 & _).
change (Z.of_nat (length (sarg (Some (dec (Z.of_nat (length (i_toks x))))))) + 1) with (hs_b1 x) in HPERM2, HAPART, HREP2.
rewrite P1.
apply (AS1 fpos ly2 S2 W2 mem2 md3 regs2 (k + EV_ARG_S) O1 Rest b0 p CX FXR).
- refine (conj HJ2 (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  + unfold hs_k2. unfold EV_ARG_S, EV_XMALLOC. lia.
  + exact (mle_station MT _ _ _ _ _ (hh_MTL B MT HH) HMLE HMLE2).
  + unfold hs_l2. lia.
  + apply (hs3_frame_kept_on (rdW Wc memc)); [|exact HFR].
    intros bb Hbb. rewrite <- (KEQ bb). apply J1; [lia | rewrite HASS2; lia |].
    intros Hin. apply HFP1 in Hin. unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia.
  + apply (hs3_aval_on (rdW Wc memc)); [|exact HFL].
    intros bb Hbb. change (Z.of_nat 8) with 8 in Hbb. rewrite <- (KEQ bb). apply (J4 0 fpos bb HFin).
    * left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 0) with 64. lia.
    * intros Hin. apply HFP1 in Hin.
      apply (frm_img SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv 0 fpos bb HARc HFin);
        [rewrite EFA; change (fs_frame_bytes 0) with 64; lia|].
      destruct (hs3_rec_fp (i_O x) bb (hs3_slot_rec (i_R x) bb Hin)) as [_ Hpg]. exact (hh_prog_img B MT HH bb Hpg).
  + pose proof HBA as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7).
    split; [|split; [exact BA2|split; [exact BA3|split; [exact BA4|split; [exact BA5|split; [|exact BA7]]]]]].
    * eapply Permutation_trans; [exact HPERM2|]. eapply Permutation_trans; [apply perm_skip; exact BA1|].
      cbn [app]. apply perm_swap.
    * intros pn [<- | [<- | []]] Hin; [exact (BA6 _ (or_introl eq_refl) Hin)|].
      destruct (in_dec hs3_pair_dec (p, hs_b1 x) (i_O x)) as [Ho | Hno]; [exact Ho|]. exfalso.
      pose proof (Permutation_in _ (Permutation_sym BA1) (in_or_app _ _ _ (or_intror (BA3 _ Hin Hno)))) as Hc.
      pose proof (proj1 (Forall_forall _ _) HAPART _ Hc) as Hap. unfold iv_apart, hs_b1 in Hap. cbn [fst snd] in Hap. lia.
- exact HREP2.
- split.
  + split; [transitivity (getr (ms_regs ms) 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact P2]|].
    split; [transitivity (getr (ms_regs ms) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact P9]|].
    split; [transitivity (getr (ms_regs ms) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact P8]|].
    split; [transitivity (getr (ms_regs ms) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact P3]|].
    split; [transitivity (getr (ms_regs ms) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact P4]|].
    split; [transitivity (getr (ms_regs ms) 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact P24]|].
    split; [transitivity (getr (ms_regs ms) 25); [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact P25]|].
    transitivity (getr (ms_regs ms) 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact P26].
  + split; [transitivity (getr (ms_regs ms) 18); [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | exact P18]|].
    split; [transitivity (getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact P19]|].
    split; [transitivity (getr (ms_regs ms) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact P20]|].
    split; [transitivity (getr (ms_regs ms) 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact P21]|].
    split; [transitivity (getr (ms_regs ms) 22); [exact (HP2 22 ltac:(unfold acallee_saved; lia)) | exact P22]|].
    transitivity (getr (ms_regs ms) 23); [exact (HP2 23 ltac:(unfold acallee_saved; lia)) | exact P23].
- transitivity (getr (ms_regs ms) 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | exact P27].
Qed.
End e.
End f.
End d.

(* ---- AL 0x8b658 .. AS1 0x8b684 ---- *)
Definition hs8_rsh : YP09.region := YP09.mkRegion (Some 25%nat) 0 8 4 6 [].
Definition hs8_ss : sstate :=
  mkSS HS_AL sr_atoms [hs8_rsh] None (mkFacts [(26%nat, mkAF HS_SB HS_SB 0)] [] []).

Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e2.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HH : hs_hyps B MT.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.

Lemma hs_seg_al : forall x, (forall fx1 : YK11.FPState, @ST_AS1 fx1 rc SK PI B MT x) -> ST_AL B MT x.
Proof.
intros x AS1. unfold ST_AL.
intros fpos lyc Sc Wc memc mdc regs1 k O1 Rest b0 CX FXR MID REP RG R27.
pose proof CX as (HPRE & HROD & HRO & (Hpl & Hptok) & H10 & H11 & H12 & HNT & HLINE & Hp0 & Hp8 & HTA & HLPS & HPS &
  HTOKS & HWL & HREP0 & HFRM & HEV & HLIVE & HMO & HTAIL & HRM0).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof RG as ((K2 & K9 & K8 & K3 & K4 & K24 & K25 & K26) & R18 & R19 & R20 & R21 & R22 & R23).
pose proof MID as (HJ & Hk & HMLE & HBB & HFR & HFL & HBA).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (hs3_sp1 (spZ (i_regs x)) Hal16 ltac:(lia)) as (S1a & S1b & S1c).
pose proof hs3_stk as FS.
destruct (hs3_frame_facts B MT x fpos lyc Sc Wc memc mdc k CX HJ) as (HFin & EFA & EFL & HF4096 & HFceil & HF64).
pose proof HJ as (HARc & _ & _ & _ & _ & HFRSc & HNEVc & _ & _ & _ & _ & _ & _ & HJpres & _).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HARc HFin) as (_ & HFapp & HFpres & HFSpres).
rewrite EFA in HFapp, HFpres, HFSpres. change (fs_frame_bytes 0) with 64 in HFapp, HFpres, HFSpres.
change (64 / 8) with 8 in HFSpres.
assert (HF8 : 512 <= hs_F x fpos / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (ESH : shadow_addr (hs_F x fpos) = HS_SB + hs_F x fpos / 8) by (unfold shadow_addr, HS_SB, SHADOW_OFF; reflexivity).
pose (E := Eimg (Ereg regs1 [])).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (V25 : bv_unsigned (ew E 25) = HS_SB + hs_F x fpos / 8)
  by (rewrite (EE 25%nat 25%bv eq_refl), K25; unfold w64; apply unsigned_lit_small; unfold HS_SB; lia).
assert (HS : st_ok_pi SEGS VAL E hs8_ss (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + HS_AL)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold hs8_ss. apply pa_entry_st_ok_full.
  - exact (regs_ok_Eimg_Ereg regs1 []).
  - reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, hs8_rsh.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite V25. split; [unfold HS_SB; lia|]. split; [unfold HS_SB; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). rewrite <- ESH. exact (proj1 (HFSpres o ltac:(lia))).
  - apply pairwise_disjoint_of_extents. unfold hs8_rsh, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (EE 26%nat 26%bv eq_refl), K26. unfold w64.
    rewrite !unsigned_lit_small by (unfold HS_SB; lia). rewrite Z.pow_0_r, !Z.mod_1_r. unfold HS_SB. lia. }
clearbody E.
(* run 1: 0x8b658 .. 0x8b674, b's shadow bytes 4 and 5 := 0, the snprintf arguments, the call *)
paj_run_shc RUNP RUNC HS HJ.
{ unfold hs8_ss. cbn [ss_mem].
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 25%nat); [reflexivity | exact V25 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi hs8_rsh] in Ha. right; right; right; left. exists 0, fpos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite EFA. rewrite ESH.
    change (fs_frame_bytes 0 / 8) with 8. lia. }
  apply (awr_ok_nil SEGS B). }
rename ms into ms1, mat into mat1, HF into HF1, HFr into HFr1, HG into HG1.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (12%bv : bv 5) P12. prreg HS (13%bv : bv 5) P13.
prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25.
prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
rewrite (EE 2%nat 2%bv eq_refl), K2 in P2. rewrite (EE 3%nat 3%bv eq_refl), K3 in P3. rewrite (EE 4%nat 4%bv eq_refl), K4 in P4.
rewrite (EE 8%nat 8%bv eq_refl), K8 in P8. rewrite (EE 9%nat 9%bv eq_refl), K9 in P9.
rewrite (EE 23%nat 23%bv eq_refl), R23 in P10. rewrite (EE 21%nat 21%bv eq_refl), R21 in P13.
rewrite (EE 18%nat 18%bv eq_refl), R18 in P18. rewrite (EE 19%nat 19%bv eq_refl), R19 in P19.
rewrite (EE 20%nat 20%bv eq_refl), R20 in P20. rewrite (EE 21%nat 21%bv eq_refl), R21 in P21.
rewrite (EE 22%nat 22%bv eq_refl), R22 in P22. rewrite (EE 23%nat 23%bv eq_refl), R23 in P23.
rewrite (EE 24%nat 24%bv eq_refl), K24 in P24. rewrite (EE 25%nat 25%bv eq_refl), K25 in P25.
rewrite (EE 26%nat 26%bv eq_refl), K26 in P26. rewrite (EE 27%nat 27%bv eq_refl), R27 in P27.
assert (P11' : getr (ms_regs ms1) 11 = w64 16) by (rewrite P11; reflexivity).
assert (P12' : getr (ms_regs ms1) 12 = w64 0x21f40).
{ rewrite P12, (img_env_atomP E 292 HEI ltac:(unfold A_TEXT, A_LIM; lia)). change (VAL 292) with (VAL (A_OBJ 51)).
  rewrite (hh_vobjs B MT HH 51%nat ltac:(vm_compute; lia)). unfold w64. f_equal; vm_compute; reflexivity. }
clear P11 P12.
(* the frame, its shadow and the stack: where they lie *)
assert (Hv : -2^31 <= Z.of_nat (length (i_toks x)) < 2^31) by lia.
pose proof (dec_length (Z.of_nat (length (i_toks x))) Hv) as HdL.
assert (HSN : sn_len (16 - 1) (PF.pf_dec (Z.of_nat (length (i_toks x)))) =
  Z.of_nat (length (dec (Z.of_nat (length (i_toks x))))) + 1) by exact (hs8_sn_len _ Hv).
destruct (hs4_sh_bounds (hs_F x fpos) ltac:(lia) HFceil) as [Fsh1 Fsh2].
assert (HSP1 : alloc_ceiling < hs_sp1 (spZ (i_regs x))) by (clear - S1a Hceil Hslo FS; rewrite FS in Hslo; lia).
pose proof (hs4_app_apart (hs_F x fpos) (hs_sp1 (spZ (i_regs x))) ltac:(lia) HFceil HSP1) as Kapp.
pose proof (frm_off_imgP B lyc Sc Wc memc mdc 0 fpos HARc HFin) as HFoff. unfold off_img in HFoff.
rewrite EFA in HFoff. change (fs_frame_bytes 0) with 64 in HFoff.
assert (HFa : 4096 <= hs_F x fpos /\ (hs_F x fpos + 64 <= 0x7fff7000 \/ 0x10007fff8000 <= hs_F x fpos))
  by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp; lia).
assert (EQ32 : (hs_F x fpos + 32) / 8 = hs_F x fpos / 8 + 4) by (clear - HF64; Z.div_mod_to_equations; lia).
assert (ESO : SHADOW_OFF = HS_SB) by reflexivity.
(* the run wrote only b's two shadow bytes, both 0 *)
assert (KEQ1 : forall a, 0 <= a < 2 ^ 64 -> ~ (HS_SB + hs_F x fpos / 8 + 4 <= a < HS_SB + hs_F x fpos / 8 + 6) ->
  rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a Ha H1. apply aview_eq_of. apply HFr1. rewrite (unsigned_lit_small a) by lia.
  intros (r & Hr & Hrw). unfold hs8_ss in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi hs8_rsh] in Hrw; rewrite V25 in Hrw; lia. }
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
pose proof (field_of_region_any E _ 25%nat (HS_SB + hs_F x fpos / 8) _ _ _ _ _ 4 1 (SLit 0) HR0 V25
  ltac:(cbn; tauto) ltac:(cbn; lia)) as Z4.
pose proof (field_of_region_any E _ 25%nat (HS_SB + hs_F x fpos / 8) _ _ _ _ _ 5 1 (SLit 0) HR0 V25
  ltac:(cbn; tauto) ltac:(cbn; lia)) as Z5.
change (bv_unsigned (sv_denot E (SLit 0)) mod 2 ^ (8 * Z.of_N 1)) with 0 in Z4, Z5.
assert (ZS4 : rdW Wc (ms_mem ms1) (HS_SB + hs_F x fpos / 8 + 4) = Some 0) by (apply (aview_of_val_mem1 SEGS); [exact Z4 | lia]).
assert (ZS5 : rdW Wc (ms_mem ms1) (HS_SB + hs_F x fpos / 8 + 5) = Some 0) by (apply (aview_of_val_mem1 SEGS); [exact Z5 | lia]).
assert (ZS4' : rdW Wc (ms_mem ms1) (SHADOW_OFF + (hs_F x fpos + 32) / 8) = Some 0).
{ rewrite EQ32, ESO. replace (HS_SB + (hs_F x fpos / 8 + 4)) with (HS_SB + hs_F x fpos / 8 + 4) by lia. exact ZS4. }
assert (ZS5' : rdW Wc (ms_mem ms1) (SHADOW_OFF + (hs_F x fpos + 32) / 8 + 1) = Some 0).
{ rewrite EQ32, ESO. replace (HS_SB + (hs_F x fpos / 8 + 4) + 1) with (HS_SB + hs_F x fpos / 8 + 5) by lia. exact ZS5. }
(* the snprintf wrapper's premises at the call *)
assert (Qsp : spZ (ms_regs ms1) = spZ (i_regs x) + (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x))).
{ unfold spZ at 1. rewrite P2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
pose proof HJ as (HARc1 & HLY1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres1 & _).
pose proof HLY1 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HKs : CMD_SNP_K = 8192) by reflexivity.
assert (HECP : ecall_pre SEGS B lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv).
{ eapply (ecall_pre_at SEGS B SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x)
    (i_mem x) (i_md x) [(0, fpos)] lyc Sc Wc (ms_mem ms1) mdv k (ms_regs ms1) (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x)));
  [exact HJ | exact Qsp | exact S1b | lia | rewrite Hes, FS; lia
  | rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity] | rewrite P3; exact Hgp | rewrite P4; exact Htp]. }
assert (HspK : ly_stk_lo lyc + CMD_SNP_K <= spZ (ms_regs ms1)) by (rewrite Eslo, Qsp, HKs; rewrite FS in Hslo; lia).
assert (Hscr : forall a, spZ (ms_regs ms1) - CMD_SNP_K <= a < spZ (ms_regs ms1) -> apresent (w_H Wc) (ms_mem ms1) a).
{ intros a Ha. apply HJpres1. rewrite Qsp, HKs in Ha. rewrite FS. lia. }
assert (HspF : hs_F x fpos + 64 <= spZ (ms_regs ms1) - CMD_SNP_K) by (rewrite Qsp, HKs; rewrite FS in Hslo; lia).
assert (HspC : alloc_ceiling + CMD_SNP_K <= spZ (ms_regs ms1)) by (rewrite Qsp, HKs; rewrite FS in Hslo; lia).
assert (Hsp47 : spZ (ms_regs ms1) <= 2 ^ 47) by (rewrite Qsp; lia).
destruct (hs3_rod_now B MT HH x fpos lyc Sc Wc (ms_mem ms1) mdv k CX HJ) as [HRODc HROc].
pose proof (fxrel_frm0 (i_fx x) fx HRM0 FXR) as HFRM0.
(* the snprintf wrapper at 0x8b674: snprintf(b, 16, "%d", ntok), b = F + 32 in this call's own frame (0, fpos) *)
eapply SRr_bind.
{ eapply (aj_art_own_atF SEGS B LAWS pa_segs_low CMD_SNP_K
    (fun a => hs_F x fpos + 32 <= a < hs_F x fpos + 32 + sn_len (16 - 1) (PF.pf_dec (Z.of_nat (length (i_toks x)))))
    (SIG CS___interceptor_trampoline_snprintf) Wc (ms_regs ms1) (ms_mem ms1) SUP_HOST_SETTING_STK (spZ (i_regs x))
    (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [(0, fpos)] lyc Sc mdv k
    (hs_sp1 (spZ (i_regs x)) - spZ (i_regs x)) (getr (ms_regs ms1) 1) _ HJ Qsp S1b ltac:(lia) ltac:(rewrite HKs; lia)
    ltac:(rewrite HKs, FS; lia) eq_refl).
  - intros a Ha. right; right; right; left. exists 0, fpos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 0) with 64.
    rewrite HSN in Ha. lia.
  - exact (hs8_snp B (hh_HB B MT HH) (hh_img B MT HH) lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv (hs_F x fpos)
      (Z.of_nat (length (i_toks x))) fpos (hh_snprintf B MT HH fx) HECP HspK Hscr HspF HspC Hsp47 P10 P11' P12' P13
      Hv HRODc HFin (eq_sym EFA) ZS4' ZS5' HFRM0). }
(* back at 0x8b678 at the FP state fx1 the wrapper returned *)
cbv beta. intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & Hfx1 & -> & HJ2 & HP2 & (H10s & HBY) & HK2).
rewrite HSN in HK2.
rewrite P1.
apply (hs8_tail (fx := fx1) B MT HH x fpos lyc Sc Wc mem2 md2 regs2 k O1 Rest b0 (AS1 fx1) CX).
- exact (fxrel_trans (i_fx x) fx fx1 FXR Hfx1).
- refine (conj HJ2 (conj Hk (conj HMLE (conj HBB (conj _ (conj _ HBA)))))).
  + apply (hs3_frame_kept_on (rdW Wc memc)); [|exact HFR].
    intros bb Hbb. rewrite (HK2 bb ltac:(lia) ltac:(lia) ltac:(lia)). apply KEQ1; lia.
  + apply (hs3_aval_on (rdW Wc memc)); [|exact HFL].
    intros bb Hbb. change (Z.of_nat 8) with 8 in Hbb.
    rewrite (HK2 bb ltac:(lia) ltac:(lia) ltac:(lia)).
    destruct (Kapp (hs_F x fpos) 64 bb HFapp ltac:(lia) HFceil) as [Kb1 _]. apply KEQ1; [lia | exact Kb1].
- apply (hs_rec_kept B lyc Sc lyc Sc (rdW Wc memc) (rdW Wc mem2) _ _ REP);
    [| intros pn H; exact (proj1 (hs_rec_own B _ _ _ _ _ REP pn H))].
  intros a [Ha | ([q m] & Hpn & Ha)].
  + assert (Hab : 6173376 <= a < 6174616)
      by (unfold hs_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia).
    rewrite (HK2 a ltac:(lia) ltac:(lia) ltac:(lia)). apply KEQ1; lia.
  + cbn [fst snd] in Ha.
    destruct (hs_rec_own B _ _ _ _ _ REP (q, m) Hpn) as (Hin & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HARc Hin) as (_ & Hq4096 & Hqc & Hqapp & _ & _ & Hm).
    pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
    pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc q m 0 fpos HARc Hin HFin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA in Hd. change (fs_frame_bytes 0) with 64 in Hd.
    rewrite (HK2 a ltac:(lia) ltac:(lia) ltac:(lia)).
    destruct (Kapp q (req_size m) a Hqapp ltac:(lia) Hqc) as [Ka1 _]. apply KEQ1; [lia | exact Ka1].
- split.
  + split; [transitivity (getr (ms_regs ms1) 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | exact P2]|].
    split; [transitivity (getr (ms_regs ms1) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact P9]|].
    split; [transitivity (getr (ms_regs ms1) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | exact P8]|].
    split; [transitivity (getr (ms_regs ms1) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | exact P3]|].
    split; [transitivity (getr (ms_regs ms1) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | exact P4]|].
    split; [transitivity (getr (ms_regs ms1) 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact P24]|].
    split; [transitivity (getr (ms_regs ms1) 25); [exact (HP2 25 ltac:(unfold acallee_saved; lia)) | exact P25]|].
    transitivity (getr (ms_regs ms1) 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact P26].
  + split; [transitivity (getr (ms_regs ms1) 18); [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | exact P18]|].
    split; [transitivity (getr (ms_regs ms1) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | exact P19]|].
    split; [transitivity (getr (ms_regs ms1) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact P20]|].
    split; [transitivity (getr (ms_regs ms1) 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact P21]|].
    split; [transitivity (getr (ms_regs ms1) 22); [exact (HP2 22 ltac:(unfold acallee_saved; lia)) | exact P22]|].
    transitivity (getr (ms_regs ms1) 23); [exact (HP2 23 ltac:(unfold acallee_saved; lia)) | exact P23].
- transitivity (getr (ms_regs ms1) 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | exact P27].
- exact (hs8_str_of_sn (rdW Wc mem2) (hs_F x fpos + 32) (Z.of_nat (length (i_toks x))) Hv HBY).
- rewrite EQ32, ESO. replace (HS_SB + (hs_F x fpos / 8 + 4)) with (HS_SB + hs_F x fpos / 8 + 4) by lia.
  rewrite (HK2 (HS_SB + hs_F x fpos / 8 + 4) ltac:(lia) ltac:(lia) ltac:(lia)). exact ZS4.
- rewrite EQ32, ESO. replace (HS_SB + (hs_F x fpos / 8 + 4) + 1) with (HS_SB + hs_F x fpos / 8 + 5) by lia.
  rewrite (HK2 (HS_SB + hs_F x fpos / 8 + 5) ltac:(lia) ltac:(lia) ltac:(lia)). exact ZS5.
Qed.
End e2.
End f2.
End d2.
