(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the snprintf call step of answer's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, 0x8ab90 `jal snprintf (buf, 4096, "resp %d", g_rec.code)`) under the stream's SHARED
   snprintf contract (lib/B/Rt/RtFormat.v asnprintf_realizes = RtPFCmd.asnprintf_sh = RtPFShared.sh_asnprintf_realizes
   at the format family FR_cmd, the window CMD_SNP_K, the stack-protector cells 0xa6bf8 / 0x604158, the image range
   0x10000 .. 0x606000 and the read-only words CMD_SNP_CR), for a destination inside a side-stack frame the walk's
   journal holds. The post is FP-existential: the step is PaFx.v's srr_art_postF_of_pf (the shared post as
   art_postF) and aj_art_own_atF (the journal step), as a Theorem Labs lane's PASS4-REFIT.md section E gives it; the walk continues
   with PaFx.v's srr_after_artF at the FP state fx1 the call returns.
   The contract's premises are discharged here from the caller's facts: ecall_pre and the window from the journal,
   the read-only view rt_rom_view (a Theorem Labs lane 0934cb146c3's contract form) by a Theorem Labs lane's CmdRecImg.cmd_consts_view_snp, the guard words by
   CmdRecCells.cmd_rec_cells, va_words with no stack words, the disjointness of the read-only words, the guard cells,
   the window and the destination (the image lies below the fake stack, the fake stack below the machine stack),
   dest_ok / shadow_hull_vis from the frame (AR's frame law), the band premise `amem_range d (sn_len (n - 1) T + 8)`
   of the shared contract at a Theorem Labs lane fc8bcbd8b42 (a Theorem Labs lane's final snprintf `+ 8`: the destination's 8 bytes past its
   written part lie in the same class-7 fake frame, a Theorem Labs lane's PASS4-REFIT.md E.0, the frame's room PaLibH.v's
   amem_range_sub_app), and dest_off_globals by a Theorem Labs lane's lib/B/Rt/RtPFDog.v pa_dest_off_globals_frame (the image hull
   below the fake stack, the frame's place in it: pa_frame_above_img), over this walk's image instance. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s YG0t.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YG05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtStack RtShadow RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtPFShared RtPFCmd RtPFSx RtPFDog.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the shared contract's read-only words, guard cells, window and destination are apart ---- *)
(* the read-only words the snprintf chain reads lie in the image's range *)
Lemma an_snp_cr_img : forall r, In r RtPFCmd.CMD_SNP_CR -> 0x10000 <= fst r /\ 0 <= snd r /\ fst r + snd r <= 0x606000.
Proof.
intros r Hr. pose proof RtPFCmd.cmd_snp_cr_img as H. rewrite forallb_forall in H. specialize (H r Hr).
unfold RtPFCmd.in_cmd_img, RtPFCmd.CMD_IMG_LO, RtPFCmd.CMD_IMG_HI in H.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2, H3. lia.
Qed.
(* an image range is apart from a window and a destination both above the image *)
Lemma an_snp_img_apart : forall lo n K sp d w, 0x10000 <= lo -> lo + n <= 0x606000 -> 0x606000 <= sp - K ->
0x606000 <= d -> Forall (zdisjoint (lo, n)) (RtPFShared.snp_out K sp d w).
Proof. intros lo n K sp d w H1 H2 H3 H4. apply RtPFSx.Forall_snp. unfold zdisjoint. cbn [fst snd]. split; lia. Qed.
Lemma an_snp_cr_bounds : Forall (fun r => 0 <= fst r /\ fst r + snd r <= 2 ^ 63) RtPFCmd.CMD_SNP_CR.
Proof. apply Forall_forall. intros r Hr. destruct (an_snp_cr_img r Hr) as (Q1 & Q2 & Q3). lia. Qed.
Lemma an_snp_cr_apart : forall K sp d w, 0x606000 <= sp - K -> 0x606000 <= d ->
Forall (fun r => Forall (zdisjoint r) (RtPFShared.snp_out K sp d w)) RtPFCmd.CMD_SNP_CR.
Proof.
intros K sp d w HK Hd. apply Forall_forall. intros r Hr. destruct (an_snp_cr_img r Hr) as (Q1 & Q2 & Q3).
destruct r as [lo n]. cbn [fst snd] in *. apply an_snp_img_apart; lia.
Qed.
(* the destination's written part: at most n bytes, at least the terminator *)
Lemma an_sn_len_bounds : forall n T, 1 <= n -> 1 <= RtPFShared.sn_len (n - 1) T <= n.
Proof.
intros n T Hn. unfold RtPFShared.sn_len, RtPFShared.sn_bytes. rewrite length_app, length_firstn. cbn [length].
pose proof (Nat.le_min_l (Z.to_nat (n - 1)) (length T)). lia.
Qed.

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
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's snprintf contract, at every FP state (answer_c.v:99) *)
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis HB : CmdBSyms B.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.

(* snprintf (d, n, f, a3 ..) at the current FP state, with d inside the frame (cid, pos) the walk's journal holds
   and the format family's facts at the call: the journal holds at the memory the call returns, a0 is |T|, the
   destination holds the first n - 1 bytes of T and the terminator, every byte outside the destination and the
   window is kept; the FP state is the one the contract returns (fxrel). *)
Lemma aj_snprintf_frameF : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n f T (o : Z) raw cid pos,
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> RtPFCmd.CMD_SNP_K - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 n -> getr regsT 12 = w64 f ->
arodata_okP SEGS RLO RHI B (rdW W memT) ->
RtPFCmd.FR_cmd (rdW W memT) (RtPFShared.snp_out RtPFCmd.CMD_SNP_K (spZ regsT) d (RtPFShared.sn_len (n - 1) T)) f
  (map (argZ regsT) [3; 4; 5; 6; 7] ++ []) T ->
1 <= n < 2 ^ 31 -> Z.of_nat (length T) < 2 ^ 31 - 1 ->
In (cid, pos) own -> frame_addr lyc cid pos <= d ->
d + RtPFShared.sn_len (n - 1) T + 8 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
range_addressable (rdW W memT) SHADOW_OFF d (RtPFShared.sn_len (n - 1) T) ->
frm0 fx ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIG CS___interceptor_trampoline_snprintf)) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists (fx1 : YK11.FPState) regs2 mem2 md2, fxrel fx fx1 /\
c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\
(getr regs2 10 = w64 (Z.of_nat (length T)) /\
 forall i, 0 <= i < RtPFShared.sn_len (n - 1) T ->
 rdW W mem2 (d + i) = Some (nth (Z.to_nat i) (RtPFShared.sn_bytes (n - 1) T) 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - RtPFCmd.CMD_SNP_K <= a < sp0 + o) ->
 ~ (d <= a < d + RtPFShared.sn_len (n - 1) T) -> rdW W mem2 a = rdW W memT a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n f T o raw cid pos
  HJ Hsp Hal Hneg Hbud Hgp Htp Hra Hraw H10 H11 H12 HROD HFF Hn HTl Hown Hd1 Hd2 HRA Hfrm.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HK : RtPFCmd.CMD_SNP_K = 8192) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (an_sn_len_bounds n T ltac:(lia)) as Hw.
set (w := RtPFShared.sn_len (n - 1) T) in *.
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memT mdc cid pos HAR Hin) as (HFal & HFapp & HFpres & _).
destruct (frames_bounds SEGS B LAWS lyc Sc W memT mdc cid pos HAR Hin) as (HF4096 & HFceil & _).
pose proof (RtPFDog.pa_frame_above_img (PI := PI) B lyc Sc W memT mdc cid pos HAR Hin) as HFimg.
unfold RtPFCmd.CMD_IMG_HI in HFimg.
eapply (aj_art_own_atF SEGS B LAWS pa_segs_low RtPFCmd.CMD_SNP_K (fun a => d <= a < d + w)
  (SIG CS___interceptor_trampoline_snprintf) W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw _
  HJ Hsp Hal Hneg ltac:(rewrite HK; lia) Hbud Hra).
- intros a Ha. right; right; right; left. exists cid, pos. split; [exact Hown|]. left. unfold in_zr. cbn [fst snd]. lia.
- apply (srr_art_postF_of_pf SEGS B RtPFCmd.CMD_SNP_K lyc Sc W regsT memT mdc _ d w
    (RtPFShared.sn_bytes (n - 1) T) (Z.of_nat (length T))).
  { intros a Ha. apply Hpres. rewrite Hsp in Ha. lia. }
  destruct (cmd_rec_cells (SK := SK) SEGS B LAWS HB IMG lyc Sc W memT mdc HAR) as (_ & (Hgot & cval & Hcan) & _).
  apply (ASNPRINTF fx lyc Sc W regsT memT mdc d n f [] (map (argZ regsT) [3; 4; 5; 6; 7] ++ []) T cval).
  + eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o);
      [exact HJ | exact Hsp | exact Hal | exact Hneg | rewrite Hes; rewrite HK in Hbud; lia
      | rewrite Hra; exact Hraw | exact Hgp | exact Htp].
  + rewrite Eslo, Hsp. lia.
  + intros a Ha. apply Hpres. rewrite Hsp in Ha. lia.
  + exact H10.
  + exact H11.
  + exact H12.
  + exact (cmd_consts_view_snp (SK := SK) SEGS B LAWS HB IMG RLO RHI W memT HROD).
  + exact an_snp_cr_bounds.
  + apply an_snp_cr_apart; [rewrite HK, Hsp; lia | lia].
  + exact Hgot.
  + exact Hcan.
  + lia.
  + lia.
  + lia.
  + lia.
  + apply an_snp_img_apart; [lia | lia | rewrite HK, Hsp; lia | lia].
  + apply an_snp_img_apart; [lia | lia | rewrite HK, Hsp; lia | lia].
  + split; [reflexivity | intros i Hi; cbn [length] in Hi; lia].
  + cbn [length Z.of_nat]. rewrite Hsp. lia.
  + apply RtPFSx.Forall_snp. unfold zdisjoint. cbn [fst snd length Z.of_nat]. rewrite HK. split; lia.
  + exact HFF.
  + exact Hn.
  + exact HTl.
  + lia.
  + lia.
  + apply RtPFSx.pairwise_snp. unfold zdisjoint. cbn [fst snd]. rewrite HK, Hsp. lia.
  + intros a Ha. destruct (HFpres a ltac:(lia)) as [Hp Hno].
    split; [apply (apresent_writable SEGS); exact Hp|]. split; [exact Hno|]. rewrite Hes, Hsp. lia.
  + apply (amem_range_sub_app (frame_addr lyc cid pos) (fs_frame_bytes cid)); [exact HFapp | exact HFceil | lia | lia | lia].
  + exact HRA.
  + apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc W memT mdc cid pos d w HAR Hin); lia.
  + exact (RtPFDog.pa_dest_off_globals_frame (PI := PI) B lyc Sc W memT mdc cid pos d w HAR Hin Hd1).
  + exact Hfrm.
Qed.
End e.
End f.
End d.
