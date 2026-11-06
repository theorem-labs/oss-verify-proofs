(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: check_reply's ASan walk (fuzz_command.asan, 0x86d78) assembled from its
   segments, as proofs/cgif/cgif_file_fuzzer/lib/A/ACh5.v assembles cgif_close's (pb_cgif_closeX):
     s1 the entry to the memchr call, s2 memchr / check_reply_answer / sup_reply_code, s3 the code's split,
     s4 snprintf, s4b rec_code_declared, s5 strcmp, s6 strlen / rec_shape_of, s7 syntax_reply_matches twice,
     s8 the frame's release and the return.
   snprintf is the only call that changes the FP state, so s4b, s5 and s8 (the segments after it) are taken at every
   FP state and s4 uses them at the state the wrapper returns.
   `pb_check_reply` is tcheck_reply_spec (lib/A/Prog/check_reply_c.v). The walk's facts at the entry that the
   statement no longer states come from its premises: the record's cells (replace_str flag byte, stack guard, errno)
   from CmdRecCells' cmd_rec_cells, the recorder's GOT words from cmd_ro_ok's RO_ptr_a70xx bytes, the read-only
   ranges from CmdRecRo's cmd_ro_in_img, and the words' shadow from AR's zshadow_ok of the stack window
   [ly_stk_lo, ly_stk_hi) (the words lie in it: spZ regs <= w and w + WORDS_W + 12 <= ly_stk_hi ly). The kit lemmas
   take the image facts IMG (cmd_img_facts); the segments take CmdRecImg's cmd_heap_tail_vis, and its
   cmd_prog_unowned and cmd_rom_view_on at IMG, so no record fact is a Section hypothesis (the walk hypotheses keep
   cgif's names; the record facts are lemmas of lib/A/Prog/CmdRecFacts.v). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply.v, with its module paths and module names changed; 280 of its 308 lines of code are new or changed and 124 lines of the source are left out. *)
(* sup_add's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan): the lemmas its two
   snprintf stages share. sup_add_s3.v calls the wrapper on (b, 16, "%d", id) at 0x8a570 with b = F + 32, sup_add_s8.v
   on (buf, 32, "resp %d", v) at 0x8a628 with buf = F + 64; F is the call's class-1 side-stack frame.

   - the texts, the format's bytes, the written part of snprintf and RtPFCmd.v's read-only words are CmdSnText.v's
     (snt_pf_dec: printf_facts_c's %d text as bytes is RecFacts' dec; "resp %d" is RecAns.v's own pf_resp).
   - sas_snp_call: the call of the wrapper from a state of the walk (the journal of sup_add_s0.v's mid-states, the
     destination inside the frame with its shadow bytes 0, the format a read-only literal of CmdRo.v) to the next
     stage at the FP state fx1 the wrapper returns. The contract is the statement's ASNPRINTF, RtPFCmd.v's
     asnprintf_sh: RtPFShared.v's sh_asnprintf_realizes at FR_cmd with the window CMD_SNP_K = 2 * ESTACK, the
     stack-protector cells 0xa6bf8 / 0x604158 (CmdRecCells.v cmd_rec_cells) and the image range 0x10000 .. 0x606000.
     The step is PaFx.v's: aj_art_own_atF (the written cells [d, d + |T| + 1) are bytes of the call's own frame
     (1, pos)), srr_art_postF_of_pf and srr_after_artF; rounding mode 0 at fx is the stage's premise, at fx1
     fxrel_frm0. The destination's 8 bytes of band slack (the contract's amem_range d (sn_len (n - 1) T + 8)) stay in
     the 128-byte frame (doff + nsz <= 120): PaLibH.v's amem_range_sub_app over the frame.
   - sas_kept: the facts every mid-state carries in memory (the saved registers, the frame's flag pointer, buf's
     shadow, the recorder) survive a step that writes only the call's stack window, a part of the frame below its
     flag pointer and b's two shadow bytes.

   The read-only premise of the contract (RtDefs.rt_rom_view) is CmdRecImg.v's cmd_consts_view_snp at the call's
   arodata_okP, which the journal carries from the entry (CmdBase.v arodata_ok_journalP). FR_cmd_intro's boolean
   check fr_lit_ok holds by the format's bounds (0x10000 <= f, f + |fmt| + 1 <= 0x30000 < CMD_GOTW), the format being
   nonempty (pf_text [] [AInt v] = None) and v an int. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YG0t.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaNoChain PaLibF.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import
RtDefs RtFormat RtPFPf RtPFShared RtPFSx RtPFCmd RtPFDog.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdBase CmdRep CmdObj CmdRo CmdChk CmdAddr PaArt PaArtOwn PaCallPg RecBLemmas PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
record_c arg_s_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_add_s0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts CmdSnText.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require PaLibH.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module RA := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.RecAns.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis IMG : cmd_img_facts SEGS B.
(* the statement's own (sup_add_c.v), at every FP state *)
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.

(* the read-only bytes are none of the footprint's: g_rec and record.spill lie above them, the recorder's blocks
   off the image *)
Lemma sas_ro_not_fp : forall ly S (W : world SEGS) mem md R O, AR SEGS B ly S W mem md ->
  rec_repA B ly S (rdW W mem) R O -> forall a, in_roP SEGS RLO RHI a -> ~ inFP (sa_FP O) a.
Proof using IMG.
intros ly S W mem md R O HAR (Q & HA & HO) a Hro Hfp.
pose proof (cif_ro_end _ _ IMG a Hro) as Hra.
unfold sa_FP in Hfp.
apply inFP_cons in Hfp as [Hq | Hfp]; [unfold A_G_REC, OFF_NCALLS in Hq; lia|].
apply inFP_cons in Hfp as [Hq | Hfp]; [unfold A_G_REC, OFF_CALLS, OFF_ANSWER in Hq; lia|].
apply inFP_cons in Hfp as [Hq | Hfp]; [unfold A_G_REC, OFF_STATE in Hq; lia|].
apply inFP_cons in Hfp as [Hq | Hfp]; [unfold A_REC_SPILL, SC_SIZE in Hq; lia|].
destruct Hfp as (r & Hr & Hr1 & Hr2). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hqm).
cbn [fst snd] in Hr1, Hr2.
pose proof (lay_blocks_in _ _ _ _ _ _ HA (q, m) (proj1 (HO (q, m)) Hqm)) as Hin.
pose proof (blk_off_imgP B ly S W mem md q m HAR Hin) as Hoff. unfold off_img in Hoff. lia.
Qed.
(* arodata_okP at a state of the walk, from the entry's through the journal (CmdBase.v arodata_ok_journalP) *)
Lemma sas_aro_at : forall ly S (W : world SEGS) regs mem md ch pu id pp pc uri placement client R O
  STK sp0 own lyc Sc Wc memc mdc k,
  sa_cx B MT ly S W regs mem md ch pu id pp pc uri placement client R O ->
  ajournal SEGS B STK sp0 (sa_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
  arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof using HB LAWS IMG.
intros ly S W regs mem md ch pu id pp pc uri placement client R O STK sp0 own lyc Sc Wc memc mdc k HCX HJ.
unfold sa_cx in HCX. cbv zeta in HCX.
destruct HCX as (HPRE & _ & HROD & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREP & _).
destruct HPRE as (HAR0 & _).
exact (arodata_ok_journalP (RO := ROB SEGS B LAWS HB IMG) SEGS CMD_RLO CMD_RHI (cif_relro_img _ _ IMG) B
  STK sp0 (sa_FP O) ly S W mem md own lyc Sc Wc memc mdc k HJ (sas_ro_not_fp ly S W mem md R O HAR0 HREP) HROD).
Qed.

(* the call of the snprintf wrapper (at its trampoline, after `jal`) on a destination d = F + doff of the call's own
   frame, with the size nsz, the format f (a literal of CmdRo.v: lit, its bytes fmt and its terminator) and the
   argument v; the rest of the walk is the continuation, at the FP state fx1 the wrapper returns *)
Lemma sas_snp_call : forall ly S (W : world SEGS) regs mem md ch pu id pp pc uri placement client R O
  lyc Sc Wc (regsT : bvmap 5 word) memT mdc pos k (doff nsz f v : Z) (lit : list byte) (fmt T : list Z)
  (ps : list PF.pf_piece),
  sa_cx B MT ly S W regs mem md ch pu id pp pc uri placement client R O ->
  frm0 fx ->
  ajournal SEGS B SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md [(1, pos)] lyc Sc Wc memT mdc k ->
  getr regsT 2 = w64 (sa_s1 (spZ regs)) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  YK0s.ret_ok (getr regsT 1) ->
  getr regsT 10 = w64 (frame_addr lyc 1 pos + doff) -> getr regsT 11 = w64 nsz -> getr regsT 12 = w64 f ->
  getr regsT 13 = w64 v -> -2 ^ 31 <= v < 2 ^ 31 ->
  0 <= doff -> doff mod 8 = 0 -> 8 <= nsz -> nsz mod 8 = 0 -> doff + nsz <= 120 ->
  (forall i, 0 <= i < nsz / 8 -> rdW Wc memT (SHADOW_OFF + frame_addr lyc 1 pos / 8 + doff / 8 + i) = Some 0) ->
  (forall rd, cmd_ro_ok rd -> abytes_atR rd f lit) -> map (fun b : byte => bv_unsigned b) lit = fmt ++ [0] ->
  cmd_addr_b f (Z.of_nat (length fmt) + 1) = true -> cmd_hull_b f (Z.of_nat (length fmt) + 1) = true ->
  0x10000 <= f -> f + Z.of_nat (length fmt) + 1 <= 0x30000 ->
  PF.pf_parse fmt = Some ps -> PF.pf_text ps [PF.AInt v] = Some T ->
  pf_prec_pos (map piece_of ps) (map arg_of [PF.AInt v]) ->
  Z.of_nat (length T) + 1 <= nsz ->
  (forall (fx1 : YK11.FPState) (regs2 : bvmap 5 word) mem2 md2, fxrel fx fx1 -> frm0 fx1 ->
    ajournal SEGS B SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md [(1, pos)] lyc Sc Wc mem2 md2 k ->
    aregs_preserved regsT regs2 ->
    (forall i, 0 <= i <= Z.of_nat (length T) ->
      rdW Wc mem2 (frame_addr lyc 1 pos + doff + i) = Some (nth (Z.to_nat i) (T ++ [0]) 0)) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sa_s1 (spZ regs) - CMD_SNP_K <= a < sa_s1 (spZ regs)) ->
      ~ (frame_addr lyc 1 pos + doff <= a < frame_addr lyc 1 pos + doff + Z.of_nat (length T) + 1) ->
      rdW Wc mem2 a = rdW Wc memT a) ->
    SRr SEGS Wc (mkCfg (@mkst fx1 regs2 (getr regsT 1) mem2 (seg_rom SEGS)) md2)
      (sa_final (fx := fx1) B MT ly S W regs mem md R O uri id placement client)) ->
  SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (SIG CS___interceptor_trampoline_snprintf)) memT (seg_rom SEGS)) mdc)
    (sa_final B MT ly S W regs mem md R O uri id placement client).
Proof using HB LAWS IMG ASNPRINTF.
intros ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regsT memT mdc pos k doff nsz f v lit fmt T
  ps HCX H0 HJ Q2 Q3 Q4 HRA R10 R11 R12 R13 Hv Hd0 Hd8 Hn8 Hn8m Hdn HSH HSEL HLITb HCK1 HCK2 Hf0 Hf1 HPARSE HTEXT
  HPREC HTL HK.
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HCEIL : ASAN_CEIL = alloc_ceiling) by reflexivity.
assert (HLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (HSTK : SUP_ADD_STK = 16736) by reflexivity.
assert (HK2 : CMD_SNP_K = 8192) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (sas_aro_at ly S W regs mem md ch pu id pp pc uri placement client R O SUP_ADD_STK (spZ regs) [(1, pos)]
  lyc Sc Wc memT mdc k HCX HJ) as HROD1.
pose proof HCX as HCX'. unfold sa_cx in HCX'. cbv zeta in HCX'.
destruct HCX' as (HPRE & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
set (sp0 := spZ regs) in *. set (s1 := sa_s1 sp0) in *. set (F := frame_addr lyc 1 pos) in *.
assert (Hs1 : s1 = sp0 - 128 \/ s1 = sp0 - 144) by (clear - Hal16; unfold s1, sa_s1; Z.div_mod_to_equations; lia).
assert (Hal1 : (s1 - sp0) mod 16 = 0).
{ destruct Hs1 as [E1 | E1]; rewrite E1;
  [replace (sp0 - 128 - sp0) with (-128) by lia | replace (sp0 - 144 - sp0) with (-144) by lia]; reflexivity. }
assert (HspT : spZ regsT = sp0 + (s1 - sp0)).
{ unfold spZ at 1. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
(* the frame at the call *)
pose proof HJ as (HARc & _ & _ & _ & _ & Hfrsc & _).
assert (HFin : In (1, pos) (frames Sc)) by (rewrite Hfrsc; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 pos HARc HFin) as (HF32 & HFapp & HFpres & _).
change (fs_frame_bytes 1) with 128 in HFapp, HFpres. fold F in HF32, HFapp, HFpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HARc HFin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFceil. fold F in HF4096, HFceil.
pose proof (pa_frame_above_img B lyc Sc Wc memT mdc 1 pos HARc HFin) as HFimg. fold F in HFimg.
unfold CMD_IMG_HI in HFimg.
(* the runtime-call pre-state with the window CMD_SNP_K *)
destruct (ecall_pre_stk_at SEGS B CMD_SNP_K SUP_ADD_STK sp0 (sa_FP O) ly S W mem md [(1, pos)] lyc Sc Wc memT mdc k
  regsT (s1 - sp0) HJ HspT Hal1 ltac:(destruct Hs1; lia) ltac:(rewrite HK2, Hes; lia)
  ltac:(rewrite HK2, HSTK; destruct Hs1; lia) HRA Q3 Q4) as (HPRE1 & HLO1 & HWIN1).
(* the read-only view, the guard cells, the format *)
pose proof (cmd_consts_view_snp SEGS B LAWS HB IMG CMD_RLO CMD_RHI Wc memT HROD1) as HCV.
destruct (cmd_rec_cells SEGS B LAWS HB IMG _ _ _ _ _ HARc) as (_ & (HG1 & cval & HG2) & _).
pose proof (HSEL _ (cmd_ro_ok_of_aro SEGS B LAWS HB IMG _ _ _ _ _ HARc HROD1)) as HLIT.
pose proof (snt_fmt_bytes _ f lit fmt HLIT HLITb) as HFB.
destruct (cmd_aread_ok_chk SEGS B LAWS HB _ _ _ _ _ f (Z.of_nat (length fmt) + 1) HARc HCK1 HCK2) as [HFA HFH].
destruct (snt_sn_fit nsz T HTL) as [ESL ESB].
unfold in_app in HFapp. destruct HFapp as (HFa & HFb).
assert (HFdiv : 8 * (F / 8) <= F /\ 0 <= F / 8) by (split; [apply Z.mul_div_le; lia | apply Z.div_pos; lia]).
(* the step: the wrapper writes the text and its terminator into the frame, the call's own bytes *)
unfold sa_final.
eapply (srr_after_artF SEGS Wc _ (getr regsT 1)).
- eapply (aj_art_own_atF SEGS B LAWS Hsegs CMD_SNP_K (fun a => F + doff <= a < F + doff + sn_len (nsz - 1) T)
    (SIG CS___interceptor_trampoline_snprintf) Wc regsT memT
    SUP_ADD_STK sp0 (sa_FP O) ly S W mem md [(1, pos)] lyc Sc mdc k (s1 - sp0) (getr regsT 1) _ HJ HspT Hal1
    ltac:(destruct Hs1; lia) ltac:(rewrite HK2; lia) ltac:(rewrite HK2, HSTK; destruct Hs1; lia) eq_refl).
  + intros a Ha. cbv beta in Ha. rewrite ESL in Ha.
    right; right; right; left. exists 1, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold F. lia.
  + apply (srr_art_postF_of_pf SEGS B CMD_SNP_K lyc Sc Wc regsT memT mdc _ (F + doff) (sn_len (nsz - 1) T)
      (sn_bytes (nsz - 1) T) (Z.of_nat (length T)) HWIN1).
    apply (ASNPRINTF fx lyc Sc Wc regsT memT mdc (F + doff) nsz f [] (map (argZ regsT) [3; 4; 5; 6; 7] ++ []) T cval).
    * exact HPRE1.
    * exact HLO1.
    * exact HWIN1.
    * exact R10.
    * exact R11.
    * exact R12.
    * exact HCV.
    * exact snt_cr_bounds.
    * apply snt_cr_disj. unfold snp_out. rewrite HspT, HK2.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; destruct Hs1; lia.
    * exact HG1.
    * exact HG2.
    * lia.
    * lia.
    * lia.
    * lia.
    * unfold snp_out. rewrite HspT, HK2, ESL.
      repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; destruct Hs1; lia.
    * unfold snp_out. rewrite HspT, HK2, ESL.
      repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; destruct Hs1; lia.
    * split; [reflexivity|]. intros i Hi. cbn [length] in Hi. lia.
    * cbn [length Z.of_nat]. rewrite HspT. lia.
    * unfold snp_out. rewrite HspT, HK2, ESL. cbn [length Z.of_nat].
      repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; destruct Hs1; lia.
    * apply (FR_cmd_intro _ _ f _ T fmt ps [PF.AInt v]).
      -- split; [lia|]. split; [exact HFB|].
         split; [unfold snp_out; rewrite HspT, HK2, ESL;
                 repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; destruct Hs1; lia|].
         split; [unfold amem_range; left; lia|].
         split; [exact HFA | exact HFH].
      -- exact HPARSE.
      -- cbn [map arg_of pf_args_asan app]. split; [|exact I].
         cbn [pf_arg_asan]. split; [exact Hv|]. unfold argZ.
         replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
         rewrite R13. unfold w64. apply RA.lit_mod32.
      -- exact HTEXT.
      -- exact HPREC.
      -- destruct fmt as [|b0 fmt0]; [cbn in HPARSE; injection HPARSE as <-; cbn in HTEXT; discriminate HTEXT|].
         assert (E1 : (CMD_IMG_LO <=? f) = true) by (apply Z.leb_le; unfold CMD_IMG_LO; lia).
         assert (E2 : (f + Z.of_nat (length (b0 :: fmt0)) + 1 <=? CMD_GOTW) = true)
           by (apply Z.leb_le; unfold CMD_GOTW; lia).
         unfold fr_lit_ok. rewrite E1, E2. reflexivity.
    * lia.
    * lia.
    * lia.
    * rewrite ESL. lia.
    * unfold snp_out. rewrite HspT, HK2, ESL. cbn [pairwise].
      split; [repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; destruct Hs1; lia|].
      split; [constructor | exact I].
    * intros a Ha. rewrite ESL in Ha. destruct (HFpres a ltac:(lia)) as [Hp Hno].
      split; [exact (apresent_writable SEGS _ _ _ Hp)|]. split; [exact Hno|]. rewrite HspT. destruct Hs1; lia.
    * (* the destination's 8 bytes of band slack: d + |T| + 1 + 8 <= F + doff + nsz + 8 <= F + 128 *)
      rewrite ESL. exact (PaLibH.amem_range_sub_app F 128 (F + doff) (Z.of_nat (length T) + 1 + 8) (conj HFa HFb) HFceil
        ltac:(lia) ltac:(lia) ltac:(lia)).
    * intros x Hx. rewrite ESL in Hx. exists 0. split; [|left; reflexivity].
      unfold shadow_of_addr.
      assert (Hj : 0 <= x / 8 - F / 8 - doff / 8 < nsz / 8) by (clear - Hx HF32 Hd8 Hn8m Hd0 HTL; Z.div_mod_to_equations; lia).
      replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + doff / 8 + (x / 8 - F / 8 - doff / 8)) by lia.
      exact (HSH _ Hj).
    * rewrite ESL.
      exact (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc Wc memT mdc 1 pos (F + doff) (Z.of_nat (length T) + 1)
        HARc HFin ltac:(fold F; lia) ltac:(change (fs_frame_bytes 1) with 128; fold F; lia) ltac:(lia)).
    * unfold zdisjoint, CMD_IMG_LO, CMD_IMG_HI. cbn [fst snd]. right. lia.
    * exact H0.
- intros fx1 regs2 mem2 md2 H01 (HJ2 & HP2 & (HQa & HQb) & HK2r).
  apply (HK fx1 regs2 mem2 md2 H01 (fxrel_frm0 fx fx1 H0 H01) HJ2 HP2).
  + intros i Hi. rewrite <- ESB. apply HQb. rewrite ESL. lia.
  + intros a Ha Hw Hd. apply HK2r; [exact Ha | intros Hc; apply Hw; lia |].
    cbv beta. rewrite ESL. intros Hc. apply Hd. lia.
Qed.

(* the facts every mid-state carries in memory, after a step that writes only the call's stack window, a part
   [lo, hi) of the frame below its flag pointer and b's two shadow bytes: the saved registers, the frame's flag
   pointer, buf's shadow and the recorder *)
Lemma sas_kept : forall ly S (W : world SEGS) regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc memc mdc
  pos k memx lo hi R2 O2,
  sa_cx B MT ly S W regs mem md ch pu id pp pc uri placement client R O ->
  ajournal SEGS B SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md [(1, pos)] lyc Sc Wc memc mdc k ->
  frame_addr lyc 1 pos <= lo -> hi <= frame_addr lyc 1 pos + 120 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sa_s1 (spZ regs) - CMD_SNP_K <= a < sa_s1 (spZ regs)) -> ~ (lo <= a < hi) ->
    ~ (SHADOW_OFF + frame_addr lyc 1 pos / 8 + 4 <= a < SHADOW_OFF + frame_addr lyc 1 pos / 8 + 6) ->
    rdW Wc memx a = rdW Wc memc a) ->
  sa_frame (rdW Wc memc) (spZ regs) regs ->
  rdword (rdW Wc memc) (frame_addr lyc 1 pos + fs_frame_bytes 1 - 8) = Some (flag_addr lyc 1 pos) ->
  sa_buf0 (rdW Wc memc) (frame_addr lyc 1 pos) ->
  rec_repA B lyc Sc (rdW Wc memc) R2 O2 -> (forall pn, In pn O2 -> In pn (ablocks B lyc Sc)) ->
  sa_frame (rdW Wc memx) (spZ regs) regs /\
  rdword (rdW Wc memx) (frame_addr lyc 1 pos + fs_frame_bytes 1 - 8) = Some (flag_addr lyc 1 pos) /\
  sa_buf0 (rdW Wc memx) (frame_addr lyc 1 pos) /\ rec_repA B lyc Sc (rdW Wc memx) R2 O2.
Proof using LAWS.
intros ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc memc mdc pos k memx lo hi R2 O2
  HCX HJ Hlo Hhi KEEP HFRM HFLG HBUF HREP2 HO2.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (HCEIL : ASAN_CEIL = alloc_ceiling) by reflexivity.
assert (HSTK : SUP_ADD_STK = 16736) by reflexivity.
assert (HK2 : CMD_SNP_K = 8192) by reflexivity.
unfold sa_cx in HCX. cbv zeta in HCX. destruct HCX as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
set (sp0 := spZ regs) in *. set (s1 := sa_s1 sp0) in *. set (F := frame_addr lyc 1 pos) in *.
assert (Hs1 : s1 = sp0 - 128 \/ s1 = sp0 - 144) by (clear - Hal16; unfold s1, sa_s1; Z.div_mod_to_equations; lia).
pose proof HJ as (HARc & _ & _ & _ & _ & Hfrsc & _).
assert (HFin : In (1, pos) (frames Sc)) by (rewrite Hfrsc; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HARc HFin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in HFceil, HFapp. fold F in HF4096, HFceil, HFapp.
pose proof (pa_frame_above_img B lyc Sc Wc memc mdc 1 pos HARc HFin) as HFimg. fold F in HFimg.
unfold CMD_IMG_HI in HFimg.
unfold in_app in HFapp. destruct HFapp as (HFa & HFb).
assert (HFdiv : 8 * (F / 8) <= F /\ 0 <= F / 8) by (split; [apply Z.mul_div_le; lia | apply Z.div_pos; lia]).
(* the frame's shadow bytes lie below the stack and outside the frame *)
assert (SHN : forall j, 0 <= j < 16 ->
  SHADOW_OFF + F / 8 + j < alloc_ceiling /\ SHADOW_OFF + F / 8 + j < kHighMemBeg /\
  ~ (F <= SHADOW_OFF + F / 8 + j < F + 128)).
{ intros j Hj. destruct HFb as [Hl | [Hh1 Hh2]]; repeat split; lia. }
pose proof (SHN 4 ltac:(lia)) as (N4a & N4b & N4c). pose proof (SHN 5 ltac:(lia)) as (N5a & N5b & N5c).
split.
{ intros j r Hj kk Hkk.
  assert (Hjlt : (j < 13)%nat)
    by (change 13%nat with (length sa_saved); apply nth_error_Some; rewrite Hj; discriminate).
  rewrite KEEP; [exact (HFRM j r Hj kk Hkk) | destruct Hs1; lia | destruct Hs1; lia | destruct Hs1; lia | destruct Hs1; lia]. }
split.
{ rewrite (YCbq.rdword_ext (rdW Wc memc) (rdW Wc memx)); [exact HFLG|].
  intros kk Hkk. change (fs_frame_bytes 1) with 128.
  apply KEEP; [lia | destruct Hs1; lia | lia | lia]. }
split.
{ intros i Hi. pose proof (SHN (8 + i) ltac:(lia)) as (N1 & N2 & N3).
  rewrite KEEP; [exact (HBUF i Hi) | lia | destruct Hs1; lia | lia | lia]. }
apply (rec_repA_kept B lyc Sc (rdW Wc memc) lyc Sc (rdW Wc memx) R2 O2 HREP2 HO2).
intros a [Ha | [Ha | Ha]].
- unfold A_G_REC, REC_SIZE in Ha. apply KEEP; [lia | destruct Hs1; lia | lia | lia].
- unfold A_REC_SPILL, SC_SIZE in Ha. apply KEEP; [lia | destruct Hs1; lia | lia | lia].
- destruct Ha as (r & Hr & Hr1 & Hr2). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hqm).
  cbn [fst snd] in Hr1, Hr2.
  pose proof (HO2 (q, m) Hqm) as Hin.
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc q m HARc Hin) as (_ & Hq4096 & Hqceil & Hqapp & _).
  pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc q m 1 pos HARc Hin HFin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 1) with 128 in Hd. fold F in Hd.
  unfold in_app in Hqapp. destruct Hqapp as (Hqa & Hqb).
  apply KEEP; [lia | destruct Hs1; lia | lia | destruct Hqb as [Hl | [Hh1 Hh2]]; lia].
Qed.
End e.
End f.
End d.
