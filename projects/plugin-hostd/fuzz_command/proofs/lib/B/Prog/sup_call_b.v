(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the fifth segment of check_reply's walk (fuzz_command.asan, 0x86d78), the
   strcmp call of the refusal path (0x86fb8) and the branch into the epilogue, ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (the step through a call and back) and A/ACh5.v (a segment that ends
   in another segment's statement), at c8557374ad2e.

   The code of the segment is
     0x86fb8  jal  wrapper_strcmp       a0 = g_rec.reply, a1 = s3 = F + 32, which holds "resp <code>"
     0x86fbc  beqz a0, 0x86ff8          equal: the epilogue; else j 0x870d8, the abort
   The entry facts give `xr = refusal_text (reply_code_a xr)` for a negative code (reply_okA), and the frame holds
   `refusal_text code ++ [0]` (the snprintf step of segment 4), so the two strings are equal, the interceptor
   returns 0, and the abort edge 0x86fc0 is not taken.

   The walk runs with the symbolic regions dropped (`st_ok_pi_submem` with []): the two instructions write no
   memory, so the engine's frame is empty and every byte the walk reads is the byte of the state the segment was
   entered in. The interceptor's own writes are the ones its contract allows, inside its scratch window below sp. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s5.v, with its module paths and module names changed; 652 of its 703 lines of code are new or changed and 361 lines of the source are left out. *)
(* sup_call's walk on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan), part b
   (sup_call_s3.v): 0x8b030 .. 0x8b058 and the snprintf wrapper's return 0x8b05c.

   From sc_at_a (0x8b030): `li a0,1` and `jal record` (0x8b034, REC_CALL = 1). record's statement (record_c.v
   trecord_spec, post apost_base: the call returns at the same FP state) is composed by PaCallPg.v's cl_callS_pg
   (record writes g_rec's ncalls and the slot, program statics, and in its spill arm the recorder's blocks), with the
   frame chain of s0 = sp0 from sup_call_s0.v's sc_chain. Back at 0x8b038: `mv s6,a0`, `sb zero,4(s7)`,
   `sb zero,5(s7)` (b's two shadow bytes usable), a2 := "%d" (0x21f40 = A_OBJ 51), a1 := 16, a0 := s5 = b = F + 32,
   a3 := s4 = id, `jal` to the snprintf wrapper (0x8b058). The wrapper (the statement's ASNPRINTF at the ambient FP
   state: RtPFShared.v's sh_asnprintf_realizes at FR_cmd) writes the decimal text of id and its terminator into
   b, the call's own frame (0, fpos); the step is PaFx.v's aj_art_own_atF, srr_art_postF_of_pf and srr_after_artF,
   and the rest of the walk is the hypothesis SC_B_stmt at the FP state fx1 the wrapper returns (rounding mode 0 at
   fx1 by fxrel_frm0).

   Each of the two runs starts from a seed of its own whose only region is the one the run writes (none for the
   first, the frame's eight shadow bytes with write window [4, 6) for the second), as sup_add's B walk does
   (that walk's lib/B/Prog/sup_add_s3.v); the plain runner (PaCallRun.v paj_run_shc) runs
   them. The facts sc_at_b carries in memory are carried by the steps' kept bytes: the saves below sp0 and the
   frame's flag word at F + 56 by the runs, record's journal (bytes at and above its sp, the frames) and the
   wrapper's post (its stack window and b only); the line by the journal from the entry (a live block that is none
   of the recorder's keeps its bytes); the recorder by rec_repA_kept. The snprintf step is sup_add_sn.v's
   sas_snp_call for the class-0 frame; the text of "%d" and the other snprintf helpers are the kit's CmdSnText.v,
   record()'s footprint and the block helpers CmdRecAns.v. The destination's `+ 8` slack word (the snprintf
   contract) lies inside the frame: amem_range_sub_app (PaLibH.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YG0t YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaCallRun PaCall PaNoChain PaCallPg PaArt PaArtOwn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh CmdChk CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat RtPFPf RtPFShared RtPFSx RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c rec_canonical_c hand_back_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import record_c arg_s_c arg_line_c answer_c sup_call_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSnText CmdRecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtPFDog.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_call_s3 sup_call_s0 sup_call_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Module RA := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.RecAns.

(* ---- the text of "%d", the snprintf helpers: CmdSnText.v (the snt_ lemmas); record()'s footprint and the block helpers:
   CmdRecAns.v (the rca_ lemmas); the frame above the image: RtPFDog.v (pa_frame_above_img); NoDup of the live blocks:
   RecBLemmas.v (recb_ablocks_nodup_m) ---- *)

(* ---- record()'s footprint (record_c.v:104-105) is CmdRecAns.v's rca_recFP ---- *)
(* record()'s footprint lies in sup_call's: g_rec's ncalls, the slot (a call of the table or the spill), and in the
   spill arm the recorder's blocks *)
Lemma scb_recfp : forall R O a, inFP (rca_recFP R O) a ->
inFP (SC_FP O) a /\ (inFP cmd_PG a \/ inFP (ablocks_fp O) a).
Proof.
intros R O a H. unfold rca_recFP, rec_slot in H. unfold SC_FP, cmd_PG. rewrite !inFP_cons.
revert H. destruct (Nat.ltb (length (r_calls R)) 16) eqn:Elt; intros H; cbv beta iota in H; rewrite !inFP_cons in H.
- apply PeanoNat.Nat.ltb_lt in Elt.
  unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_STATE, CALL_SIZE, SC_SIZE in *.
  destruct H as [H | [H | H]].
  + split; [left; lia | left; left; lia].
  + split; [right; left; lia | left; left; lia].
  + destruct (inFP_nil a H).
- unfold A_G_REC, A_REC_SPILL, A_G_QUITTING, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_STATE, CALL_SIZE, SC_SIZE in *.
  destruct H as [H | [H | H]].
  + split; [left; lia | left; left; lia].
  + split; [right; right; right; left; lia | left; right; left; lia].
  + split; [right; right; right; right; exact H | right; exact H].
Qed.
Local Ltac scb_cs := unfold acallee_saved;
  match goal with |- context[bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.

(* ---- the two seeds: 0x8b030 (no region) and 0x8b038 (the frame's shadow at s7, write window [4, 6)) ---- *)
(* 0x8b038 - 0x8af34 *)
Definition SCB_PC1 : Z := 0x104.
Definition ss_scb0 : sstate := mkSS (AF_sup_call + SC_PC_A) sr_atoms [] None (mkFacts [] [] []).
Definition scb_shadow : YP09.region := YP09.mkRegion (Some 23%nat) 0 8 4 6 [].
Definition ss_scb1 : sstate := mkSS (AF_sup_call + SCB_PC1) sr_atoms [scb_shadow] None (mkFacts [] [] []).

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Lemma scb_seed0 : forall (W : world SEGS) (regs : bvmap 5 word) mem,
  st_ok_pi SEGS VAL (snt_E regs) ss_scb0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_call + SC_PC_A)) mem (seg_rom SEGS))).
Proof.
intros W regs mem. rewrite <- Z.add_assoc.
unfold ss_scb0. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold snt_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn [pairwise_disjoint]. exact I.
- vm_compute. repeat split.
Qed.
Lemma scb_seed1 : forall (W : world SEGS) (regs : bvmap 5 word) mem sb,
  getr regs 23 = w64 sb -> 0 <= sb -> sb + 8 <= 2 ^ 64 ->
  (forall o, 4 <= o < 6 -> writable_at SEGS (mrestrict (w_H W) mem) (sb + o)) ->
  st_ok_pi SEGS VAL (snt_E regs) ss_scb1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF_sup_call + SCB_PC1))) mem (seg_rom SEGS))).
Proof.
intros W regs mem sb H23 Hsb0 Hsb1 Hw.
assert (E23 : ew (snt_E regs) 23 = getr regs 23).
{ unfold snt_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ 23 23%bv eq_refl). }
unfold ss_scb1. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold snt_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold scb_shadow, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E23, H23. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [exact Hw | apply Forall_nil].
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- vm_compute. repeat split.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses (sup_call_c.v:87-93), word for word *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis VOBJS : cmd_val_objs.
(* the walk hypotheses, with cgif's names *)
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.

(* record()'s footprint at the call: below alloc_ceiling and off the side-stack frame (0, fpos) *)
Lemma scb_recfp_off : forall ly S (W : world SEGS) mem md R O fpos a,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) -> In (0, fpos) (frames S) ->
inFP (rca_recFP R O) a -> a < alloc_ceiling /\ ~ (frame_addr ly 0 fpos <= a < frame_addr ly 0 fpos + 64).
Proof using LAWS IMG.
intros ly S W mem md R O fpos a HAR HOb Hin Ha.
pose proof asan_consts as (C1 & _).
destruct (scb_recfp R O a Ha) as (_ & [Hpg | Hb]).
- pose proof (CmdRecBase.cif_prog_img _ _ IMG a Hpg) as Himg.
  split.
  + unfold cmd_PG in Hpg. rewrite !inFP_cons in Hpg. pose proof (inFP_nil a).
    unfold A_G_REC, A_REC_SPILL, A_G_QUITTING in Hpg. intuition lia.
  + intros Hf. apply (frm_img SEGS B LAWS ly S W mem md 0 fpos a HAR Hin); [change (fs_frame_bytes 0) with 64; lia | exact Himg].
- destruct (inFP_ablocks_fp_inv O a Hb) as (p & n & Hpn & Hr).
  pose proof (HOb _ Hpn) as Hbl.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hbl) as (_ & _ & Hc & _).
  split; [lia|].
  pose proof (sep_block_frame SEGS B LAWS ly S W mem md p n 0 fpos HAR Hbl Hin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd. lia.
Qed.
(* the stack at and above the callee's sp and the side-stack frame are kept by a call whose footprint lies below
   alloc_ceiling and off the frame *)
Lemma scb_call_agree : forall STK1 sp1 FP1 lyc Sc (W : world SEGS) memc mdc ly2 S2 W2 mem2 md2 k1 fpos lo hi,
ajournal SEGS B STK1 sp1 FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 k1 ->
In (0, fpos) (frames Sc) ->
alloc_ceiling <= lo -> sp1 <= lo -> hi <= 2 ^ 64 ->
(forall a, inFP FP1 a -> a < alloc_ceiling /\ ~ (frame_addr lyc 0 fpos <= a < frame_addr lyc 0 fpos + 64)) ->
(forall a, lo <= a < hi -> rdW W2 mem2 a = rdW W memc a) /\
(forall a, frame_addr lyc 0 fpos <= a < frame_addr lyc 0 fpos + 64 -> rdW W2 mem2 a = rdW W memc a).
Proof.
intros STK1 sp1 FP1 lyc Sc W memc mdc ly2 S2 W2 mem2 md2 k1 fpos lo hi HJc Hin Hlo Hsp Hhi HFP.
pose proof HJc as (HAR2 & _ & _ & _ & _ & _ & _ & _ & G1 & _ & _ & G4 & _).
split.
- intros a Ha. apply G1; [lia | lia | intros Hf; pose proof (HFP a Hf); lia].
- intros a Ha. apply (G4 0 fpos a Hin).
  + left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 0) with 64. lia.
  + intros Hf. pose proof (HFP a Hf). lia.
Qed.
(* the block accounting after record(): its post (record_c.v:112-117) against the entry *)
Lemma scb_blk : forall ly S (O : list (Z * Z)) lyc Sc ly2 S2 (Fr O1 : list (Z * Z)),
List.NoDup (ablocks B lyc Sc) -> ablocks B lyc Sc = ablocks B ly S ->
Permutation (ablocks B lyc Sc) (ablocks B ly2 S2 ++ Fr) ->
(forall pn, In pn Fr -> In pn O) -> (forall pn, In pn O1 <-> In pn O /\ ~ In pn Fr) ->
sc_blk B ly S O ly2 S2 O1.
Proof.
intros ly S O lyc Sc ly2 S2 Fr O1 HND Eab HP HFO HO1.
assert (HND2 : List.NoDup (ablocks B ly2 S2 ++ Fr)) by exact (Permutation_NoDup HP HND).
assert (Hin2 : forall pn, In pn (ablocks B ly2 S2) -> In pn (ablocks B ly S)).
{ intros pn Hpn. rewrite <- Eab. eapply Permutation_in; [apply Permutation_sym; exact HP | apply in_or_app; left; exact Hpn]. }
assert (Hin1 : forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly2 S2) \/ In pn Fr).
{ intros pn Hpn. rewrite <- Eab in Hpn. apply in_app_or. eapply Permutation_in; [exact HP | exact Hpn]. }
unfold sc_blk. split; [|split].
- intros pn Hpn. left. exact (proj1 (proj1 (HO1 pn) Hpn)).
- intros pn Hpn. destruct (rca_in_dec pn O) as [Hi | Hi].
  + right. apply HO1. split; [exact Hi|]. intros HF. exact (list_nodup_app_disj _ _ pn HND2 Hpn HF).
  + left. split; [exact (Hin2 pn Hpn) | exact Hi].
- intros pn Hpn Hno. destruct (Hin1 pn Hpn) as [H | H]; [exact H | exfalso; exact (Hno (HFO pn H))].
Qed.
(* the recorder's representation through a reader that agrees below alloc_ceiling off the frame (0, fpos) and off
   its eight shadow bytes *)
Lemma scb_rep_kept : forall lyc Sc (Wc : world SEGS) memc mdc (rd' : reader) R2 O2 fpos,
  AR SEGS B lyc Sc Wc memc mdc -> rec_repA B lyc Sc (rdW Wc memc) R2 O2 -> In (0, fpos) (frames Sc) ->
  (forall a, 0 <= a < alloc_ceiling ->
     ~ (frame_addr lyc 0 fpos <= a < frame_addr lyc 0 fpos + 64) ->
     ~ (SB + frame_addr lyc 0 fpos / 8 <= a < SB + frame_addr lyc 0 fpos / 8 + 8) -> rd' a = rdW Wc memc a) ->
  rec_repA B lyc Sc rd' R2 O2.
Proof using LAWS.
intros lyc Sc Wc memc mdc rd' R2 O2 fpos HAR HREP HFin KEEP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (HCEIL : ASAN_CEIL = alloc_ceiling) by reflexivity.
assert (HO2 : forall pn, In pn O2 -> In pn (ablocks B lyc Sc)).
{ intros pn Hpn. pose proof HREP as (Q & HA & HOq). exact (lay_blocks_in _ _ _ _ _ _ HA pn (proj1 (HOq pn) Hpn)). }
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HAR HFin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 0) with 64 in HFceil, HFapp.
pose proof (pa_frame_above_img B lyc Sc Wc memc mdc 0 fpos HAR HFin) as HFimg. unfold CMD_IMG_HI in HFimg.
remember (frame_addr lyc 0 fpos) as F eqn:HFa.
unfold in_app in HFapp. destruct HFapp as (HFa1 & HFb).
assert (HFdiv : 8 * (F / 8) <= F /\ 0 <= F / 8) by (split; [apply Z.mul_div_le; lia | apply Z.div_pos; lia]).
apply (rec_repA_kept B lyc Sc (rdW Wc memc) lyc Sc rd' R2 O2 HREP HO2).
intros a [Ha | [Ha | Ha]].
- unfold A_G_REC, REC_SIZE in Ha. apply KEEP; [lia | lia | unfold SB; lia].
- unfold A_REC_SPILL, SC_SIZE in Ha. apply KEEP; [lia | lia | unfold SB; lia].
- destruct Ha as (r & Hr & Hr1 & Hr2). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hqm).
  cbn [fst snd] in Hr1, Hr2.
  pose proof (HO2 (q, m) Hqm) as Hin.
  destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc q m HAR Hin) as (_ & Hq4096 & Hqceil & Hqapp & _).
  pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc q m 0 fpos HAR Hin HFin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd. rewrite <- HFa in Hd.
  unfold in_app in Hqapp. destruct Hqapp as (Hqa & Hqb).
  apply KEEP; [lia | lia |].
  unfold SB. destruct Hqb as [Hl | [Hh1 Hh2]]; destruct HFb as [Hl' | [Hh1' Hh2']]; lia.
Qed.
(* the line keeps its bytes at every state of the walk: it lies in a live block that is none of the recorder's
   (the statement's in_blockA and its iv_apart against O), so off the footprint, and the journal from the entry
   keeps such a block's bytes while the block stays live *)
Lemma scb_line_kept : forall ly S (W : world SEGS) regs mem md ch id pl line R O t own lyc Sc (Wc : world SEGS)
  memc mdc k,
  sc_pre B MT ly S W regs mem md ch id pl line R O t ->
  ajournal SEGS B SUP_CALL_STK (spZ regs) (SC_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
  (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
  astr_atR (rdW Wc memc) pl line.
Proof using LAWS IMG.
intros ly S W regs mem md ch id pl line R O t own lyc Sc Wc memc mdc k HPRE0 HJ HKB.
destruct HPRE0 as (HPRE & _ & _ & _ & _ & _ & _ & _ & (HBLK & HAP & HSTR & _) & HREP & _).
pose proof HPRE as (HAR0 & _).
destruct HBLK as (p & kk & Hpk & Hp & Hk).
pose proof (Zle_0_nat (length line)) as Hlen0.
assert (HnO : ~ In (p, kk) O).
{ intros HO. rewrite Forall_forall in HAP. specialize (HAP (p, kk) HO). cbn [fst snd] in HAP. unfold iv_apart in HAP. lia. }
pose proof (HKB (p, kk) Hpk HnO) as Hpk'.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (Hreq : kk <= req_size kk) by (unfold req_size; destruct (Z.eqb_spec kk 0); lia).
apply (astr_atR_kept_r (rdW W mem)); [|exact HSTR].
intros x Hx.
replace x with (p + (x - p)) by lia.
apply (F2 p kk (x - p) Hpk Hpk'); [lia|].
replace (p + (x - p)) with x by lia. intros Hf.
destruct (sc_fp_cases O x Hf) as [Hs | (q & n & Hqn & Hr)].
- apply (blk_img SEGS B LAWS ly S W mem md p kk x HAR0 Hpk ltac:(lia)).
  apply (CmdRecBase.cif_prog_img _ _ IMG x).
  apply Exists_exists in Hs as (r & Hr & Har). unfold TFIB_PROG_STATIC in Hr. unfold in_zr in Har.
  unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING. rewrite !inFP_cons.
  destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fst snd] in Har; [left | right; left | right; right; left]; lia.
- assert (Hne : (p, kk) <> (q, n)) by (intros E; apply HnO; rewrite E; exact Hqn).
  pose proof HREP as (Q & HA & HOq).
  pose proof (lay_blocks_in _ _ _ _ _ _ HA (q, n) (proj1 (HOq (q, n)) Hqn)) as Hqn'.
  pose proof (sep_blocks SEGS B LAWS ly S W mem md p kk q n HAR0 Hpk Hqn' Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* the call of the snprintf wrapper (at its trampoline, after `jal` 0x8b058) on b = F + 32 of the call's own frame
   (0, fpos), the size 16, the format "%d" (0x21f40, CmdRo.v's RO_lit_21f40) and id; the rest of the walk is the
   continuation, at the FP state fx1 the wrapper returns (sup_add_sn.v's sas_snp_call for the class-0 frame) *)
Lemma scb_snp : forall ly S (W : world SEGS) regs mem md ch id pl line R O t
  lyc Sc Wc (regsT : bvmap 5 word) memT mdc fpos F k,
  sc_pre B MT ly S W regs mem md ch id pl line R O t -> frm0 fx ->
  ajournal SEGS B SUP_CALL_STK (spZ regs) (SC_FP O) ly S W mem md [(0, fpos)] lyc Sc Wc memT mdc k ->
  frame_addr lyc 0 fpos = F ->
  getr regsT 2 = w64 (sc_sp1 (spZ regs)) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  YK0s.ret_ok (getr regsT 1) ->
  getr regsT 10 = w64 (F + 32) -> getr regsT 11 = w64 16 -> getr regsT 12 = w64 0x21f40 -> getr regsT 13 = w64 id ->
  (forall i, 0 <= i < 2 -> rdW Wc memT (SB + F / 8 + 4 + i) = Some 0) ->
  (forall (fx1 : YK11.FPState) (regs2 : bvmap 5 word) mem2 md2, fxrel fx fx1 -> frm0 fx1 ->
    ajournal SEGS B SUP_CALL_STK (spZ regs) (SC_FP O) ly S W mem md [(0, fpos)] lyc Sc Wc mem2 md2 k ->
    aregs_preserved regsT regs2 -> astr_atR (rdW Wc mem2) (F + 32) (dec id) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sc_sp1 (spZ regs) - CMD_SNP_K <= a < sc_sp1 (spZ regs)) ->
      ~ (F + 32 <= a < F + 48) -> rdW Wc mem2 a = rdW Wc memT a) ->
    SRr SEGS Wc (mkCfg (@mkst fx1 regs2 (getr regsT 1) mem2 (seg_rom SEGS)) md2)
      (sc_post (fx := fx1) B MT ly S W regs mem md id line R O t)) ->
  SRr SEGS Wc (mkCfg (mkst regsT (Z_to_bv 64 (SIG CS___interceptor_trampoline_snprintf)) memT (seg_rom SEGS)) mdc)
    (sc_post B MT ly S W regs mem md id line R O t).
Proof using HB LAWS IMG ASNPRINTF.
intros ly S W regs mem md ch id pl line R O t lyc Sc Wc regsT memT mdc fpos F k
  HPRE0 H0 HJ HFa Q2 Q3 Q4 HRA R10 R11 R12 R13 HSH HK.
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HCEIL : ASAN_CEIL = alloc_ceiling) by reflexivity.
assert (HLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (HK2 : CMD_SNP_K = 8192) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HSTK : SUP_CALL_STK = 16704) by reflexivity.
pose proof HPRE0 as (HPRE & _ & HROD & _ & _ & Hid & _ & _ & _ & HREP & _).
pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (HO : forall pn, In pn O -> In pn (ablocks B ly S)).
{ intros pn Hpn. pose proof HREP as (Q & HA & HOq). exact (lay_blocks_in _ _ _ _ _ _ HA pn (proj1 (HOq pn) Hpn)). }
pose proof (sc_aro B HB LAWS IMG ly S W mem md O SUP_CALL_STK (spZ regs) [(0, fpos)] lyc Sc Wc memT mdc k
  HAR0 HO HJ HROD) as HROD1.
(* the realigned sp: 96 to 112 bytes below the entry sp, 16-aligned *)
destruct (snt_sp1_facts (spZ regs - 96) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (Hb1 & _ & H161).
change (32 * ((spZ regs - 96) / 32)) with (sc_sp1 (spZ regs)) in Hb1, H161.
assert (Hal1 : (sc_sp1 (spZ regs) - spZ regs) mod 16 = 0) by (rewrite Zminus_mod, H161, Hal16; reflexivity).
assert (HspT : spZ regsT = spZ regs + (sc_sp1 (spZ regs) - spZ regs)).
{ unfold spZ at 1. rewrite Q2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
(* the frame at the call *)
pose proof HJ as (HARc & _ & _ & _ & _ & Hfrsc & _).
assert (HFin : In (0, fpos) (frames Sc)) by (rewrite Hfrsc; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HARc HFin) as (HF32 & HFapp & HFpres & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HARc HFin) as (HF4096 & HFceil & _).
destruct (frame_al64 SEGS B _ _ _ _ _ 0 fpos HARc HFin) as (HF64 & _ & _).
pose proof (pa_frame_above_img B lyc Sc Wc memT mdc 0 fpos HARc HFin) as HFimg.
change (fs_frame_bytes 0) with 64 in HFapp, HFpres, HFceil.
rewrite HFa in HF32, HFapp, HFpres, HF4096, HFceil, HF64, HFimg.
unfold CMD_IMG_HI in HFimg.
(* the runtime-call pre-state with the window CMD_SNP_K *)
destruct (ecall_pre_stk_at SEGS B CMD_SNP_K SUP_CALL_STK (spZ regs) (SC_FP O) ly S W mem md [(0, fpos)] lyc Sc Wc memT
  mdc k regsT (sc_sp1 (spZ regs) - spZ regs) HJ HspT Hal1 ltac:(lia) ltac:(rewrite HK2, Hes; lia)
  ltac:(rewrite HK2, HSTK; lia) HRA Q3 Q4) as (HPRE1 & HLO1 & HWIN1).
(* the read-only view, the guard cells, the format *)
pose proof (cmd_consts_view_snp SEGS B LAWS HB IMG CMD_RLO CMD_RHI Wc memT HROD1) as HCV.
destruct (cmd_rec_cells SEGS B LAWS HB IMG _ _ _ _ _ HARc) as (_ & (HG1 & cval & HG2) & _).
assert (HLIT : abytes_atR (rdW Wc memT) 0x21f40 RO_lit_21f40).
{ pose proof (cmd_ro_ok_of_aro SEGS B LAWS HB IMG _ _ _ _ _ HARc HROD1) as Hro.
  clear - Hro. destruct Hro as [Hro _]. unfold cmd_ro_bytes in Hro.
  repeat match type of Hro with
  | abytes_atR _ 0x21f40 _ /\ _ => exact (proj1 Hro)
  | abytes_atR _ 0x21f40 _ => exact Hro
  | _ /\ _ => apply proj2 in Hro
  end. }
pose proof (snt_fmt_bytes _ 0x21f40 RO_lit_21f40 [37; 100] HLIT ltac:(vm_compute; reflexivity)) as HFB.
destruct (cmd_aread_ok_chk SEGS B LAWS HB _ _ _ _ _ 0x21f40 (Z.of_nat (length [37; 100]) + 1) HARc
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [HFA HFH].
(* the text of "%d" on id *)
pose proof (dec_length id Hid) as HDL.
pose proof (snt_pf_dec id Hid) as HPD.
assert (HTLen : length (PF.pf_dec id) = length (dec id))
  by (rewrite <- HPD; unfold PF.pf_bytes; rewrite length_map; reflexivity).
destruct (snt_sn_fit 16 (PF.pf_dec id) ltac:(rewrite HTLen; lia)) as [ESL ESB].
unfold in_app in HFapp. destruct HFapp as (HFa1 & HFb).
assert (HFdiv : 8 * (F / 8) <= F /\ 0 <= F / 8) by (split; [apply Z.mul_div_le; lia | apply Z.div_pos; lia]).
(* the step: the wrapper writes the text and its terminator into b, the call's own frame bytes *)
unfold sc_post.
eapply (srr_after_artF SEGS Wc _ (getr regsT 1)).
- eapply (aj_art_own_atF SEGS B LAWS Hsegs CMD_SNP_K (fun a => F + 32 <= a < F + 32 + sn_len (16 - 1) (PF.pf_dec id))
    (SIG CS___interceptor_trampoline_snprintf) Wc regsT memT
    SUP_CALL_STK (spZ regs) (SC_FP O) ly S W mem md [(0, fpos)] lyc Sc mdc k (sc_sp1 (spZ regs) - spZ regs)
    (getr regsT 1) _ HJ HspT Hal1 ltac:(lia) ltac:(rewrite HK2; lia) ltac:(rewrite HK2, HSTK; lia) eq_refl).
  + intros a Ha. cbv beta in Ha. rewrite ESL in Ha.
    right; right; right; left. exists 0, fpos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. rewrite HFa. lia.
  + apply (srr_art_postF_of_pf SEGS B CMD_SNP_K lyc Sc Wc regsT memT mdc _ (F + 32) (sn_len (16 - 1) (PF.pf_dec id))
      (sn_bytes (16 - 1) (PF.pf_dec id)) (Z.of_nat (length (PF.pf_dec id))) HWIN1).
    apply (ASNPRINTF fx lyc Sc Wc regsT memT mdc (F + 32) 16 0x21f40 [] (map (argZ regsT) [3; 4; 5; 6; 7] ++ [])
      (PF.pf_dec id) cval).
    * exact HPRE1.
    * exact HLO1.
    * exact HWIN1.
    * exact R10.
    * exact R11.
    * exact R12.
    * exact HCV.
    * exact snt_cr_bounds.
    * apply snt_cr_disj. unfold snp_out. rewrite HspT, HK2.
      repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia.
    * exact HG1.
    * exact HG2.
    * lia.
    * lia.
    * lia.
    * lia.
    * unfold snp_out. rewrite HspT, HK2, ESL.
      repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; lia.
    * unfold snp_out. rewrite HspT, HK2, ESL.
      repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; lia.
    * split; [reflexivity|]. intros i Hi. cbn [length] in Hi. lia.
    * cbn [length Z.of_nat]. rewrite HspT. lia.
    * unfold snp_out. rewrite HspT, HK2, ESL. cbn [length Z.of_nat].
      repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; lia.
    * apply (FR_cmd_intro _ _ 0x21f40 _ (PF.pf_dec id) [37; 100] [PF.Pd] [PF.AInt id]).
      -- split; [lia|]. split; [exact HFB|].
         split; [unfold snp_out; rewrite HspT, HK2, ESL;
                 repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd length]; lia|].
         split; [unfold amem_range; left; cbn [length]; lia|].
         split; [exact HFA | exact HFH].
      -- exact snt_parse_d.
      -- cbn [map arg_of pf_args_asan app]. split; [|exact I].
         cbn [pf_arg_asan]. split; [exact Hid|]. unfold argZ.
         replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity).
         rewrite R13. unfold w64. apply RA.lit_mod32.
      -- exact (snt_text_d id).
      -- vm_compute. exact I.
      -- (* the format's place in the image and no string argument (FR_cmd_intro's boolean check, 0934cb146c3) *)
         vm_compute. reflexivity.
    * lia.
    * lia.
    * lia.
    * rewrite ESL. lia.
    * unfold snp_out. rewrite HspT, HK2, ESL. cbn [pairwise].
      split; [repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint; cbn [fst snd]; lia|].
      split; [constructor | exact I].
    * intros a Ha. rewrite ESL in Ha. destruct (HFpres a ltac:(lia)) as [Hp Hno].
      split; [exact (apresent_writable SEGS _ _ _ Hp)|]. split; [exact Hno|]. rewrite HspT. lia.
    * (* the destination's slack word (the `+ 8`): b's text, its NUL and 8 more bytes end at F + 52 at most, inside
         the 64-byte class-0 frame, which lies in application memory below alloc_ceiling (measured on A: arg_i's
         twin, room 8) *)
      rewrite ESL. apply (amem_range_sub_app F 64 (F + 32) _ (conj HFa1 HFb) HFceil); lia.
    * intros x Hx. rewrite ESL in Hx. exists 0. split; [|left; reflexivity].
      unfold shadow_of_addr.
      assert (Hj : 0 <= x / 8 - F / 8 - 4 < 2) by (clear - Hx HF64 HDL HTLen; Z.div_mod_to_equations; lia).
      replace (SHADOW_OFF + x / 8) with (SB + F / 8 + 4 + (x / 8 - F / 8 - 4)) by (rewrite HSB; unfold SB; lia).
      exact (HSH _ Hj).
    * rewrite ESL.
      exact (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc Wc memT mdc 0 fpos (F + 32) (Z.of_nat (length (PF.pf_dec id)) + 1)
        HARc HFin ltac:(rewrite HFa; lia) ltac:(change (fs_frame_bytes 0) with 64; rewrite HFa; lia) ltac:(lia)).
    * unfold zdisjoint, CMD_IMG_LO, CMD_IMG_HI. cbn [fst snd]. right. lia.
    * exact H0.
- intros fx1 regs2 mem2 md2 H01 (HJ2 & HP2 & (HQa & HQb) & HK2r).
  apply (HK fx1 regs2 mem2 md2 H01 (fxrel_frm0 fx fx1 H0 H01) HJ2 HP2).
  + apply (snt_astr_of_text SEGS (w_H Wc) mem2 (F + 32) (PF.pf_dec id) (dec id) HPD (dec_no0 id)).
    intros i Hi. rewrite <- ESB. apply HQb. rewrite ESL. lia.
  + intros a Ha Hw Hd. apply HK2r; [exact Ha | intros Hc; apply Hw; lia |].
    cbv beta. rewrite ESL. intros Hc. apply Hd. lia.
Qed.

(* Part b: from sc_at_a (0x8b030) through record() and the snprintf wrapper to sc_at_b (0x8b05c), at the FP state
   the wrapper returns *)
Lemma sc_stage_b : (forall fx0 : YK11.FPState, @SC_B_stmt fx0 rc SK PI B MT) -> SC_A_stmt B MT.
Proof.
intros HBs ly S W regs mem md ch id pl line R O fpos F FL lyc Sc Wc regsc memc mdc.
cbv zeta. intros HFRM HPRE0 HAT.
set (t := snd (sup_call_m R id line)) in *.
assert (HPRE0c : sc_pre B MT ly S W regs mem md ch id pl line R O t) by exact HPRE0.
assert (HATc : sc_at_a B MT ly S W regs mem md pl line R O fpos F FL lyc Sc Wc regsc memc mdc) by exact HAT.
clear HPRE0c HATc.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO.
pose proof pa_B_ok as (HBa & HBb & HBc).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HCEIL : ASAN_CEIL = alloc_ceiling) by reflexivity.
assert (HLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (HK2 : CMD_SNP_K = 8192) by reflexivity.
assert (HSTK : SUP_CALL_STK = 16704) by reflexivity.
assert (FRS : RECORD_STK = 16560) by reflexivity.
pose proof HPRE0 as HPREs.
destruct HPRE0 as (HPRE & Hfr7 & HROD & HRO & H10 & Hid & H11 & Hpl & HLINE & HREP & HEV & HLIVE & HMOK).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HAT as ((HJ & HFa & HFla & HRG & HFR & HFW) & Eab & Ebb & Hmle0 & HREPc & _).
pose proof HRG as (Esp & E8 & E18 & E24 & E19 & E20 & E21 & E23 & E25 & E3 & E4 & E26 & E27).
assert (HO : forall pn, In pn O -> In pn (ablocks B ly S)).
{ intros pn Hpn. pose proof HREP as (Q & HA & HOq). exact (lay_blocks_in _ _ _ _ _ _ HA pn (proj1 (HOq pn) Hpn)). }
assert (HOc : forall pn, In pn O -> In pn (ablocks B lyc Sc)) by (intros pn Hpn; rewrite Eab; exact (HO pn Hpn)).
(* the realigned sp: 96 to 112 bytes below the entry sp, 16-aligned *)
destruct (snt_sp1_facts (spZ regs - 96) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (Hb1 & _ & H161).
change (32 * ((spZ regs - 96) / 32)) with (sc_sp1 (spZ regs)) in Hb1, H161.
assert (Hal1 : (sc_sp1 (spZ regs) - spZ regs) mod 16 = 0) by (rewrite Zminus_mod, H161, Hal16; reflexivity).
(* the frame (0, fpos) at 0x8b030 *)
pose proof HJ as (HARc & HLYc & _ & HWLEc & _ & Hfrsc & Hnevc & _).
assert (HFin : In (0, fpos) (frames Sc)) by (rewrite Hfrsc; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HARc HFin) as (HF32 & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 fpos HARc HFin) as (HF4096 & HFceil & _).
destruct (frame_al64 SEGS B _ _ _ _ _ 0 fpos HARc HFin) as (HF64 & _ & _).
pose proof (pa_frame_above_img B lyc Sc Wc memc mdc 0 fpos HARc HFin) as HFimg.
change (fs_frame_bytes 0) with 64 in HFapp, HFpres, HFceil.
rewrite HFa in HF32, HFapp, HFpres, HF4096, HFceil, HF64, HFimg.
unfold CMD_IMG_HI in HFimg.
unfold in_app in HFapp. destruct HFapp as (HFapp1 & HFb).
assert (HFdiv : 8 * (F / 8) <= F /\ 0 <= F / 8) by (split; [apply Z.mul_div_le; lia | apply Z.div_pos; lia]).
(* the frame's eight shadow bytes lie below alloc_ceiling and apart from the frame *)
assert (SHD : SB + F / 8 + 8 <= F \/ F + 64 <= SB + F / 8).
{ unfold SB. destruct HFb as [Hl | [Hh1 Hh2]]; [right | left]; lia. }
assert (SHC : SB + F / 8 + 8 <= alloc_ceiling) by (unfold SB; destruct HFb as [Hl | [Hh1 Hh2]]; lia).
(* ---- 0x8b030 .. 0x8b034: a0 := 1, `jal record` ---- *)
pose proof (scb_seed0 Wc regsc memc) as HS.
assert (HEI : img_env VAL A_LIM (snt_E regsc)) by (unfold snt_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew (snt_E regsc) n = ew (Ereg regsc []) n)
  by (intros n Hn; unfold snt_E; apply Eimg_low; exact Hn).
remember (snt_E regsc) as E eqn:HE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regsc rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
clear HE EL.
paj_run_shc RUNP RUNC HS HJ.
{ intros a (r & Hin & Hr). vm_compute in Hin. destruct Hin. }
lazymatch goal with |- SRr _ _ {| cfg_model := ?m |} _ => set (md1 := m) in *; clearbody md1 end.
pmkst HS.
rename ms into ms1.
(* the run writes nothing *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms1) a = rdW Wc memc a).
{ intros a Ha. refine (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms1) (fun _ => False) HFr _ a Ha (fun x => x)).
  intros b wlo whi x Hwin _. vm_compute in Hwin. destruct Hwin. }
prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3. prreg HS (4%bv : bv 5) U4.
prreg HS (8%bv : bv 5) U8. prreg HS (10%bv : bv 5) U10.
prreg HS (18%bv : bv 5) U18. prreg HS (19%bv : bv 5) U19. prreg HS (20%bv : bv 5) U20. prreg HS (21%bv : bv 5) U21.
prreg HS (23%bv : bv 5) U23. prreg HS (24%bv : bv 5) U24. prreg HS (25%bv : bv 5) U25.
prreg HS (26%bv : bv 5) U26. prreg HS (27%bv : bv 5) U27.
assert (V1_2 : getr (ms_regs ms1) 2 = getr regsc 2) by (rewrite U2; exact (EEo 2%nat 2%bv eq_refl)).
assert (V1_3 : getr (ms_regs ms1) 3 = getr regsc 3) by (rewrite U3; exact (EEo 3%nat 3%bv eq_refl)).
assert (V1_4 : getr (ms_regs ms1) 4 = getr regsc 4) by (rewrite U4; exact (EEo 4%nat 4%bv eq_refl)).
assert (V1_8 : getr (ms_regs ms1) 8 = getr regsc 8) by (rewrite U8; exact (EEo 8%nat 8%bv eq_refl)).
assert (V1_18 : getr (ms_regs ms1) 18 = getr regsc 18) by (rewrite U18; exact (EEo 18%nat 18%bv eq_refl)).
assert (V1_19 : getr (ms_regs ms1) 19 = getr regsc 19) by (rewrite U19; exact (EEo 19%nat 19%bv eq_refl)).
assert (V1_20 : getr (ms_regs ms1) 20 = getr regsc 20) by (rewrite U20; exact (EEo 20%nat 20%bv eq_refl)).
assert (V1_21 : getr (ms_regs ms1) 21 = getr regsc 21) by (rewrite U21; exact (EEo 21%nat 21%bv eq_refl)).
assert (V1_23 : getr (ms_regs ms1) 23 = getr regsc 23) by (rewrite U23; exact (EEo 23%nat 23%bv eq_refl)).
assert (V1_24 : getr (ms_regs ms1) 24 = getr regsc 24) by (rewrite U24; exact (EEo 24%nat 24%bv eq_refl)).
assert (V1_25 : getr (ms_regs ms1) 25 = getr regsc 25) by (rewrite U25; exact (EEo 25%nat 25%bv eq_refl)).
assert (V1_26 : getr (ms_regs ms1) 26 = getr regsc 26) by (rewrite U26; exact (EEo 26%nat 26%bv eq_refl)).
assert (V1_27 : getr (ms_regs ms1) 27 = getr regsc 27) by (rewrite U27; exact (EEo 27%nat 27%bv eq_refl)).
clear U2 U3 U4 U8 U18 U19 U20 U21 U23 U24 U25 U26 U27 EEo HEI HF HFr HG.
pose proof HJ as (HARc1 & _).
(* the frame state at record's entry *)
assert (HL1 : sc_live B ly S W regs mem md O fpos F FL lyc Sc Wc (ms_regs ms1) (ms_mem ms1) md1 0).
{ split; [exact HJ|]. split; [exact HFa|]. split; [exact HFla|].
  split.
  { unfold sc_regs. split; [unfold spZ at 1; rewrite V1_2; exact Esp|].
    rewrite V1_8, V1_18, V1_24, V1_19, V1_20, V1_21, V1_23, V1_25, V1_3, V1_4, V1_26, V1_27. exact (proj2 HRG). }
  split; [apply (sc_frame_ext (rdW Wc memc)); [intros a Ha; apply K1; lia | exact HFR]|].
  apply (sc_rdword_ext (rdW Wc memc)); [intros x Hx; apply K1; lia | exact HFW]. }
destruct (sc_chain B LAWS ly S W regs mem md ch O fpos F FL lyc Sc Wc (ms_regs ms1) (ms_mem ms1) md1 0 HPRE HO HL1)
  as (ch1 & HCH).
(* record's premises at the call *)
pose proof (sc_aro B HB LAWS IMG ly S W mem md O SUP_CALL_STK (spZ regs) [(0, fpos)] lyc Sc Wc (ms_mem ms1) md1 0
  HAR0 HO HJ HROD) as HRODc.
assert (HREP1c : rec_repA B lyc Sc (rdW Wc (ms_mem ms1)) R O).
{ apply (scb_rep_kept lyc Sc Wc memc mdc (rdW Wc (ms_mem ms1)) R O fpos HARc HREPc HFin).
  intros a Ha _ _. apply K1. lia. }
assert (HEVc : st_nev Sc + EV_RECORD R <= EV_MAX).
{ unfold EV_SUP_CALL in HEV.
  assert (0 <= EV_ARG_S + EV_ARG_LINE + EV_ANSWER) by (apply Z.leb_le; vm_compute; reflexivity). lia. }
assert (HXM : forall n, 0 <= XM_XMALLOC MT n)
  by (intros n; unfold XM_XMALLOC, LIVE_XMALLOC; apply (mo_malloc_nonneg MT MTL); lia).
pose proof (mo_free_nonneg MT MTL) as HFnn.
assert (HXR : 0 <= XM_RECORD MT R) by (unfold XM_RECORD, rec_spill_frees; destruct (Nat.ltb _ _); nia).
assert (HXS : 0 + XM_RECORD MT R <= XM_SUP_CALL MT R id line t).
{ unfold XM_SUP_CALL, XM_ARG_S, XM_ARG_LINE, XM_ANSWER, XM_REC_CANONICAL, XM_HAND_BACK.
  repeat match goal with |- context [XM_XMALLOC MT ?n] =>
    let H := fresh "HX" in pose proof (HXM n) as H; revert H; generalize (XM_XMALLOC MT n); intros end.
  lia. }
pose proof (mok_station MT S Sc _ 0 (XM_RECORD MT R) MTL HMOK Hmle0 HXR HXS) as HMOc.
assert (HRA1 : YK0s.ret_ok (getr (ms_regs ms1) 1)) by (rewrite U1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (HRA14 : 4096 <= bv_unsigned (getr (ms_regs ms1) 1)) by (rewrite U1, unsigned_lit_small by lia; lia).
assert (Hspc : spZ (ms_regs ms1) = spZ regs + (sc_sp1 (spZ regs) - spZ regs)).
{ unfold spZ at 1. rewrite V1_2. change (bv_unsigned (getr regsc 2)) with (spZ regsc). rewrite Esp. lia. }
assert (HG3 : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite V1_3, E3; exact Hgp).
assert (HG4 : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite V1_4, E4; exact Htp).
assert (H10c : getr (ms_regs ms1) 10 = w64 REC_CALL) by (rewrite U10; reflexivity).
(* ---- record(REC_CALL) (0x8b034): footprint g_rec's ncalls, the slot and (spill arm) the recorder's blocks ---- *)
eapply SRr_bind.
{ eapply (cl_callS_pg B LAWS Wc (ms_regs ms1) (ms_mem ms1) (Z_to_bv 64 (SIG CS_record)) SUP_CALL_STK (spZ regs)
    (SC_FP O) ly S W mem md [(0, fpos)] lyc Sc md1 0 RECORD_STK (rca_recFP R O) (EV_RECORD R)
    (sc_sp1 (spZ regs) - spZ regs) (getr (ms_regs ms1) 1) ch1 _ HJ Hspc Hal1).
  - lia.
  - rewrite FRS. lia.
  - rewrite FRS, HSTK. lia.
  - exact HG3.
  - exact HG4.
  - reflexivity.
  - exact HRA1.
  - exact HRA14.
  - replace (spZ regs + (sc_sp1 (spZ regs) - spZ regs)) with (sc_sp1 (spZ regs)) by lia. exact HCH.
  - intros HPREc. rewrite (rca_sig_record SIGP).
    pose proof (TRECORD fx lyc Sc Wc (ms_regs ms1) (ms_mem ms1) md1 ch1 REC_CALL R O HPREc HRODc H10c
      ltac:(unfold REC_CALL, REC_FN_COUNT; lia) HREP1c HEVc HMOc) as HCL.
    unfold cfg_at in HCL. unfold apost_base in HCL. exact HCL.
  - intros a Ha. left. destruct (scb_recfp R O a Ha) as (HfpO & [Hpg | Hbk]).
    + split; [exact HfpO|]. right. split; [exact (rca_HPROG B HB a Hpg) | exact (CmdRecBase.cif_prog_img _ _ IMG a Hpg)].
    + split; [exact HfpO|]. left. destruct (inFP_ablocks_fp_inv O a Hbk) as (p & n & Hpn & Hr).
      exists p, n. split; [exact (HOc _ Hpn) | exact Hr]. }
cbv beta. intros W2 c2 _ (ly2 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 &
  (Fr & O1 & Hslot & HPerm & HlenF & HFO & HREP1 & HO1 & Hbb3 & Hmle3)).
(* ---- back at 0x8b038 ---- *)
pose proof HJc3 as (HAR3 & HLY3 & _ & _ & _ & Hfrs3 & _).
pose proof HLY3 as (_ & _ & _ & _ & _ & EF3 & _).
assert (EFa3 : frame_addr ly2 0 fpos = F) by (rewrite <- HFa; unfold frame_addr; rewrite EF3; reflexivity).
assert (EFl3 : flag_addr ly2 0 fpos = FL) by (rewrite <- HFla; unfold flag_addr; rewrite EF3; reflexivity).
assert (HFin3 : In (0, fpos) (frames S3)) by (rewrite Hfrs3; exact HFin).
destruct (scb_call_agree RECORD_STK (spZ regs + (sc_sp1 (spZ regs) - spZ regs)) (rca_recFP R O) lyc Sc Wc (ms_mem ms1)
  md1 ly2 S3 W2 mem3 md3 (EV_RECORD R) fpos (sc_sp1 (spZ regs)) (2 ^ 64) HJc3 HFin ltac:(lia) ltac:(lia) ltac:(lia)
  (fun a Ha => scb_recfp_off lyc Sc Wc (ms_mem ms1) md1 R O fpos a HARc1 HOc HFin Ha)) as (KS3 & KF3).
rewrite HFa in KF3.
assert (CS3 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs3 rr = getr (ms_regs ms1) rr)
  by (intros rr Hr; pose proof (HP3 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx).
rewrite U1.
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
  change (Z_to_bv 64 (BASE + k)) with (Z_to_bv 64 (BASE + (AF_sup_call + SCB_PC1))) end.
clear HS U1 U10.
(* ---- 0x8b038 .. 0x8b058: s6 := c, b's shadow 00, a2 := "%d", a1 := 16, a0 := b, a3 := id, `jal` ---- *)
assert (HFSp3 : forall o, 4 <= o < 6 -> writable_at SEGS (mrestrict (w_H W2) mem3) (SB + F / 8 + o)).
{ intros o Ho. destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR3 HFin3) as (_ & _ & _ & HFS3).
  change (fs_frame_bytes 0 / 8) with 8 in HFS3. unfold shadow_addr in HFS3. rewrite <- SB_SHADOW_OFF, EFa3 in HFS3.
  exact (apresent_writable SEGS _ _ _ (proj1 (HFS3 o ltac:(lia)))). }
assert (R23 : getr regs3 23 = w64 (SB + F / 8)) by (rewrite (CS3 23%bv ltac:(scb_cs)), V1_23; exact E23).
pose proof (scb_seed1 W2 regs3 mem3 (SB + F / 8) R23 ltac:(unfold SB; lia) ltac:(unfold SB in *; lia) HFSp3) as HS.
assert (HEI2 : img_env VAL A_LIM (snt_E regs3)) by (unfold snt_E; apply Eimg_env).
assert (EL2 : forall n, (n < A_TEXT)%nat -> ew (snt_E regs3) n = ew (Ereg regs3 []) n)
  by (intros n Hn; unfold snt_E; apply Eimg_low; exact Hn).
remember (snt_E regs3) as E2 eqn:HE2.
assert (EEo2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E2 n = getr regs3 rr).
{ intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite EL2 by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
clear HE2 EL2.
assert (U23v : bv_unsigned (ew E2 23) = SB + F / 8).
{ rewrite (EEo2 23%nat 23%bv eq_refl), R23. unfold w64. apply unsigned_lit_small. unfold SB in *. lia. }
paj_run_shc RUNP RUNC HS HJ3.
{ intros a (r & Hin & Hr). vm_compute in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U23v in Hr.
  right; right; right; left. exists 0, fpos. split; [left; reflexivity|]. right.
  unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 0 / 8) with 8. rewrite EFa3, <- SB_SHADOW_OFF. lia. }
lazymatch goal with |- SRr _ _ {| cfg_model := ?m |} _ => set (md4 := m) in *; clearbody md4 end.
pmkst HS.
rename ms into ms2.
(* b's two shadow bytes after the stores: the region's chunks *)
assert (HB0 : forall i, 0 <= i < 2 -> rdW W2 (ms_mem ms2) (SB + F / 8 + 4 + i) = Some 0).
{ destruct (st_ok_mem_ok SEGS _ _ _ HS) as (_ & HFA & _).
  rewrite Forall_forall in HFA.
  lazymatch type of HFA with forall x, In x ?rs0 -> _ =>
    let rs := eval vm_compute in rs0 in
    lazymatch rs with context [YP09.mkRegion (Some 23%nat) ?lo ?hi ?wlo ?whi ?cs] =>
      pose proof (HFA (YP09.mkRegion (Some 23%nat) lo hi wlo whi cs) ltac:(vm_compute; tauto)) as HR23
    end end.
  cbn [ms_mem restrict] in HR23.
  intros i Hi. assert (Hi2 : i = 0 \/ i = 1) by lia.
  destruct Hi2 as [-> | ->].
  - pose proof (field_of_region_any (segs := SEGS) E2 _ 23 (SB + F / 8) _ _ _ _ _ 4 1%N (SLit 0) HR23 U23v
      ltac:(vm_compute; tauto) ltac:(lia)) as Hv.
    lazymatch type of Hv with val_mem _ _ _ _ ?y => replace y with 0 in Hv by (vm_compute; reflexivity) end.
    rewrite Z.add_0_r. exact (aview_of_val_mem1 SEGS (w_H W2) (ms_mem ms2) _ 0 Hv ltac:(lia)).
  - pose proof (field_of_region_any (segs := SEGS) E2 _ 23 (SB + F / 8) _ _ _ _ _ 5 1%N (SLit 0) HR23 U23v
      ltac:(vm_compute; tauto) ltac:(lia)) as Hv.
    lazymatch type of Hv with val_mem _ _ _ _ ?y => replace y with 0 in Hv by (vm_compute; reflexivity) end.
    replace (SB + F / 8 + 4 + 1) with (SB + F / 8 + 5) by lia.
    exact (aview_of_val_mem1 SEGS (w_H W2) (ms_mem ms2) _ 0 Hv ltac:(lia)). }
(* the run writes b's two shadow bytes only *)
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (SB + F / 8 + 4 <= a < SB + F / 8 + 6) -> rdW W2 (ms_mem ms2) a = rdW W2 mem3 a).
{ intros a Ha Hs.
  refine (kept_of_frame (segs := SEGS) E2 _ (w_H W2) mem3 (ms_mem ms2)
    (fun x => SB + F / 8 + 4 <= x < SB + F / 8 + 6) HFr _ a Ha Hs).
  intros b wlo whi x Hwin Hx. vm_compute in Hwin.
  destruct Hwin as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hx. rewrite U23v in Hx. exact Hx. }
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
prreg HS (13%bv : bv 5) P13.
prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
(* the registers at the wrapper's call *)
assert (T2 : getr (ms_regs ms2) 2 = w64 (sc_sp1 (spZ regs))).
{ rewrite P2, (EEo2 2%nat 2%bv eq_refl), (CS3 2%bv ltac:(scb_cs)), V1_2. unfold w64. rewrite <- Esp.
  unfold spZ. symmetry. apply Z_to_bv_bv_unsigned. }
assert (T3 : getr (ms_regs ms2) 3 = w64 (as_gp B))
  by (rewrite P3, (EEo2 3%nat 3%bv eq_refl), (CS3 3%bv ltac:(scb_cs)), V1_3, E3; exact Hgp).
assert (T4 : getr (ms_regs ms2) 4 = w64 (as_tp B))
  by (rewrite P4, (EEo2 4%nat 4%bv eq_refl), (CS3 4%bv ltac:(scb_cs)), V1_4, E4; exact Htp).
assert (T10 : getr (ms_regs ms2) 10 = w64 (F + 32))
  by (rewrite P10, (EEo2 21%nat 21%bv eq_refl), (CS3 21%bv ltac:(scb_cs)), V1_21; exact E21).
assert (T11 : getr (ms_regs ms2) 11 = w64 16) by (rewrite P11; reflexivity).
assert (T12 : getr (ms_regs ms2) 12 = w64 0x21f40) by (rewrite P12; exact (snt_fmt_d VOBJS E2 HEI2)).
assert (T13 : getr (ms_regs ms2) 13 = w64 id)
  by (rewrite P13, (EEo2 20%nat 20%bv eq_refl), (CS3 20%bv ltac:(scb_cs)), V1_20, E20; exact H10).
assert (HRA2 : YK0s.ret_ok (getr (ms_regs ms2) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
(* ---- the snprintf wrapper (0x8b058) writes dec id and its terminator into b ---- *)
eapply (scb_snp ly S W regs mem md ch id pl line R O t ly2 S3 W2 (ms_regs ms2) (ms_mem ms2) md4 fpos F (0 + EV_RECORD R)
  HPREs HFRM HJ3 EFa3 T2 T3 T4 HRA2 T10 T11 T12 T13 HB0).
(* ---- back at 0x8b05c, at the FP state fx1 the wrapper returned ---- *)
intros fx1 regs2 mem2 md2 H01 HFRM1 HJ2 HP2 HSTR2 HKP.
rewrite P1.
assert (EPB : BASE + AF_sup_call + SC_PC_B = BASE + (AF_sup_call + SC_PC_B)) by lia.
lazymatch goal with |- context [Z_to_bv 64 (BASE + ?k)] =>
  change (Z_to_bv 64 (BASE + k)) with (Z_to_bv 64 (BASE + (AF_sup_call + SC_PC_B))) end.
rewrite <- EPB.
refine (HBs fx1 ly S W regs mem md ch id pl line R O fpos F FL ly2 S3 W2 regs2 mem2 md2 HFRM1 HPREs _).
assert (CS2 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs2 rr = getr (ms_regs ms2) rr)
  by (intros rr Hr; pose proof (HP2 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx).
assert (G2 : getr regs2 2 = getr regsc 2)
  by (rewrite (CS2 2%bv ltac:(scb_cs)), P2, (EEo2 2%nat 2%bv eq_refl), (CS3 2%bv ltac:(scb_cs)), V1_2; reflexivity).
assert (G3 : getr regs2 3 = getr regsc 3)
  by (rewrite (CS2 3%bv ltac:(scb_cs)), P3, (EEo2 3%nat 3%bv eq_refl), (CS3 3%bv ltac:(scb_cs)), V1_3; reflexivity).
assert (G4 : getr regs2 4 = getr regsc 4)
  by (rewrite (CS2 4%bv ltac:(scb_cs)), P4, (EEo2 4%nat 4%bv eq_refl), (CS3 4%bv ltac:(scb_cs)), V1_4; reflexivity).
assert (G8 : getr regs2 8 = getr regsc 8)
  by (rewrite (CS2 8%bv ltac:(scb_cs)), P8, (EEo2 8%nat 8%bv eq_refl), (CS3 8%bv ltac:(scb_cs)), V1_8; reflexivity).
assert (G18 : getr regs2 18 = getr regsc 18)
  by (rewrite (CS2 18%bv ltac:(scb_cs)), P18, (EEo2 18%nat 18%bv eq_refl), (CS3 18%bv ltac:(scb_cs)), V1_18; reflexivity).
assert (G19 : getr regs2 19 = getr regsc 19)
  by (rewrite (CS2 19%bv ltac:(scb_cs)), P19, (EEo2 19%nat 19%bv eq_refl), (CS3 19%bv ltac:(scb_cs)), V1_19; reflexivity).
assert (G20 : getr regs2 20 = getr regsc 20)
  by (rewrite (CS2 20%bv ltac:(scb_cs)), P20, (EEo2 20%nat 20%bv eq_refl), (CS3 20%bv ltac:(scb_cs)), V1_20; reflexivity).
assert (G21 : getr regs2 21 = getr regsc 21)
  by (rewrite (CS2 21%bv ltac:(scb_cs)), P21, (EEo2 21%nat 21%bv eq_refl), (CS3 21%bv ltac:(scb_cs)), V1_21; reflexivity).
assert (G23 : getr regs2 23 = getr regsc 23)
  by (rewrite (CS2 23%bv ltac:(scb_cs)), P23, (EEo2 23%nat 23%bv eq_refl), (CS3 23%bv ltac:(scb_cs)), V1_23; reflexivity).
assert (G24 : getr regs2 24 = getr regsc 24)
  by (rewrite (CS2 24%bv ltac:(scb_cs)), P24, (EEo2 24%nat 24%bv eq_refl), (CS3 24%bv ltac:(scb_cs)), V1_24; reflexivity).
assert (G25 : getr regs2 25 = getr regsc 25)
  by (rewrite (CS2 25%bv ltac:(scb_cs)), P25, (EEo2 25%nat 25%bv eq_refl), (CS3 25%bv ltac:(scb_cs)), V1_25; reflexivity).
assert (G26 : getr regs2 26 = getr regsc 26)
  by (rewrite (CS2 26%bv ltac:(scb_cs)), P26, (EEo2 26%nat 26%bv eq_refl), (CS3 26%bv ltac:(scb_cs)), V1_26; reflexivity).
assert (G27 : getr regs2 27 = getr regsc 27)
  by (rewrite (CS2 27%bv ltac:(scb_cs)), P27, (EEo2 27%nat 27%bv eq_refl), (CS3 27%bv ltac:(scb_cs)), V1_27; reflexivity).
(* the block accounting against the entry *)
pose proof (scb_blk ly S O lyc Sc ly2 S3 Fr O1 (recb_ablocks_nodup_m B lyc Sc Wc memc mdc HARc) Eab HPerm HFO HO1) as HBLK.
unfold sc_at_b, sc_live.
split.
{ split; [replace (EV_RECORD R) with (0 + EV_RECORD R) by lia; exact HJ2|].
  split; [exact EFa3|]. split; [exact EFl3|].
  split.
  { unfold sc_regs. split; [unfold spZ at 1; rewrite G2; exact Esp|].
    rewrite G8, G18, G24, G19, G20, G21, G23, G25, G3, G4, G26, G27. exact (proj2 HRG). }
  split.
  { (* the saves below sp0: above the wrapper's window, record's sp and the run's shadow bytes *)
    apply (sc_frame_ext (rdW Wc memc)); [|exact HFR].
    intros a Ha.
    rewrite (HKP a ltac:(lia) ltac:(lia) ltac:(lia)).
    rewrite (K2 a ltac:(lia) ltac:(lia)).
    rewrite (KS3 a ltac:(lia)).
    apply K1. lia. }
  (* the frame's flag word at F + 56: a frame byte past b, none of record's footprint *)
  apply (sc_rdword_ext (rdW Wc memc)); [|exact HFW].
  intros x Hx.
  rewrite (HKP x ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite (K2 x ltac:(lia) ltac:(destruct SHD; lia)).
  rewrite (KF3 x ltac:(lia)).
  apply K1. lia. }
split; [rewrite (CS2 22%bv ltac:(scb_cs)), P22, (EEo2 10%nat 10%bv eq_refl); exact Hslot|].
exists O1.
split.
{ (* the recorder: the wrapper and the run write none of its bytes *)
  apply (scb_rep_kept ly2 S3 W2 mem3 md3 (rdW W2 mem2) _ O1 fpos HAR3 HREP1 HFin3).
  intros a Ha Hf Hs. rewrite EFa3 in Hf, Hs.
  rewrite (HKP a ltac:(lia) ltac:(lia) ltac:(lia)).
  apply K2; lia. }
split; [exact HBLK|].
split; [lia|].
split.
{ replace (XM_RECORD MT R) with (0 + XM_RECORD MT R) by lia.
  exact (mle_station MT S Sc S3 0 (XM_RECORD MT R) MTL Hmle0 Hmle3). }
split.
{ destruct HBLK as (_ & _ & HKB).
  exact (scb_line_kept ly S W regs mem md ch id pl line R O t [(0, fpos)] ly2 S3 W2 mem2 md2 (0 + EV_RECORD R)
    HPREs HJ2 HKB). }
split; [exact HSTR2|].
split.
- rewrite (HKP (SB + F / 8 + 4) ltac:(unfold SB; lia) ltac:(lia) ltac:(destruct SHD; lia)).
  pose proof (HB0 0 ltac:(lia)) as Hb. rewrite Z.add_0_r in Hb. exact Hb.
- rewrite (HKP (SB + F / 8 + 5) ltac:(unfold SB; lia) ltac:(lia) ltac:(destruct SHD; lia)).
  replace (SB + F / 8 + 5) with (SB + F / 8 + 4 + 1) by lia. exact (HB0 1 ltac:(lia)).
Qed.
End e.
End f.
End w.
