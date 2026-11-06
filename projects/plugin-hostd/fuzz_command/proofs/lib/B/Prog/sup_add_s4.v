(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of arg_line (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, entry 0x8b128 = BASE + AF_arg_line, 304 bytes, 76 instructions): targ_line_spec of a Theorem Labs lane's
   lib/B/Prog/arg_line_c.v, proved as stated, over its callee contract rec_canonical_c and the strlen wrapper, each
   taken at the walk's FP state (the statement states them at every FP state).

   The B re-walk of the A walk lib/A/Prog/arg_line.v (a Theorem Labs lane a60bdbabd8f), on B's code as measured with capstone
   (symbol-keyed; B adds five UBSan trap branches and a fourth inline check, the store4 of c->nargs; the calls and the
   shadow-check pattern are A's). arg_line(c, line) (recorder.c:229-233): c in a0, line in a1; s1 = c, s0 = c + 4,
   s4 = the shadow byte address of c + 4, s3 = the shadow base (through the GOT word 0xa5f50 = A_OBJ 0 and the cell
   0xb0c38 = A_OBJ 12: an auipc-paired object slot, so no A_HI value is read). c->nargs is read once before the calls
   and once after them; the path splits on it (c->nargs = 6: return, al_walk6; c->nargs < 6: strlen, rec_canonical,
   c->nargs := m + 1, c->args[m] := p, al_walk_lt). On the second path c->nargs is an atom of value 0..5 up to the
   last segment, where the walk splits it into its six values, so that the stores' addresses are constant offsets
   of c.

   Report and UBSan trap edges, each refuted at its branch by the token executor's run (CmdPaLib.v's paj_run, sound by
   SRr_run_pi_tok_AJ), which decides the branch from the symbolic state's shadow entry al_SH (a check) or its facts
   (a trap):
     0x8b224 (__asan_report_load4; guards 0x8b174 bnez, 0x8b21c blt): refuted by the check token of the run at
       al_walk6 / al_walk_lt's first paj_run_tok, from sh_ok al_SH of al_entry / al_entry_lt, i.e. al_slot_addressable
       (the slot premise: c + 4 is in g_rec's or record.spill's zero-shadow range, CmdZsh.cmd_addressable_in).
     0x8b238 (__asan_report_load4; guards 0x8b19c bnez, 0x8b230 blt), 0x8b24c (__asan_report_store4; guards 0x8b1b0
       bnez, 0x8b244 blt), 0x8b254 (__asan_report_store8; guard 0x8b1e8 bnez): refuted by the check tokens of
       al_walk_lt's last paj_run_tok, from SHOK3 (al_slot_addressable at the state after rec_canonical; c + 4 and
       c + 8 + 8m lie in [c, c + 56)), from the slot premise.
     0x8b144 (beqz c -> unimp 0x8b210): refuted by the run's facts: atom 10 = c lies in [A_G_REC, A_REC_SPILL]
       (al_facts / al_facts_lt, facts_ok by al_entry / al_entry_lt's HG), from the slot premise (al_slot_facts).
     0x8b150 (bnez (c & 7) -> unimp): refuted by the same facts' alignment (af_al2 = 3: c mod 8 = 0, al_slot_facts).
     0x8b1a8 (blt (m + 1) m, the signed overflow of c->nargs++): refuted by al_walk_lt's last run on the literal m,
       one of 0..5 (the nargs premise m <= 6 and the branch at 0x8b180, which the first run decides on atom 33's fact
       0 <= m <= 5; the slot is outside rec_canonical's footprint, so the value reloaded at 0x8b1a0 is m: VN).
     0x8b1c4 (beqz (c + 8 + 8m)) and 0x8b1d8 (the pointer c + 8 + 8m wraps below c + 8): refuted by al_walk_lt's last
       run, from the facts on atom 10 (c in [A_G_REC, A_REC_SPILL]) and the literal m.

   Section hypotheses beyond the statement's (named as the lemmas a Theorem Labs lane states only at PI := PB_cmd): HB (CmdBSyms,
   the per-binary allocator record), MTL (the meter's laws), cmd_val_objs_PB (CmdObj.v's cmd_val_objs: the GOT word and
   the shadow cell), cmd_sig_prog_PB (CmdObj.v's cmd_sig_prog: rec_canonical's call target), cmd_img_facts_tfib
   (a Theorem Labs lane's CmdRecImg.v lemma, at this walk's abstract segments) and PRW (the core's prog_rw, for CmdRecCells'
   PROG_WRITABLE: the two stores into the slot). LAWS is AR_laws_ok; PALib's fields are CmdRecCells' cmd_cf_got,
   cmd_cf_cell and cmd_cf_env. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/arg_line.v, with its module paths, module names and addresses changed; 923 of its 1002 lines of code are new or changed and 649 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_add_s3a.v, with its module paths and module names changed; 78 of its 125 lines of code are new or changed and 955 lines of the source are left out. *)
(* sup_add's walk on the ASan+UBSan build of plugin-hostd/fuzz_command, stage M3 (0x8a574) -> M4 (0x8a580):
   arg_s(c, b), b = F + 32 the buffer of this call's side-stack frame that holds the decimal text of id.

   The run 0x8a574 .. 0x8a57c (`mv a0,s8`, `mv a1,s7`, `jal arg_s`) writes no memory: the seed has no region and
   no fact. arg_s takes the string by its frame-object arm (arg_s_c.v:109-110): the frame (1, pos) is live, F is
   32-aligned (AR_frames_law), b = F + 32 holds dec id (sa_M3m) and its 16 bytes are addressable because b's two
   shadow bytes are 0 (sa_b0); the word tail is in the frame (cmd_fobj_tail). The call itself is sup_add_ag.v's
   saa_call; the recorder then holds [sarg uri; dec id]. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaDenot PaLibG PaLibF PaLibH PaCall PaCallPg PaCallRun PaNoChain CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c record_c arg_s_c mix_call_c hand_back_c answer_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_add_s0 sup_add_lem sup_add_ag.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts RecBLemmas.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}. Context {SK : YI16.sink_head}.
Section f. Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e. Variable B : asyms. Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO. #[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.

Lemma sa_m3_ok : SA_M4_stmt B MT -> SA_M3_at B MT.
Proof using HB LAWS MTL SIGP IMG TARG_S.
intros HM4 ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos HCX Hfrm HM3.
pose proof HCX as HCX0.
unfold sa_cx in HCX. cbv zeta in HCX.
destruct HCX as (HPRE & _ & _ & _ & _ & _ & H11 & Hid & _).
unfold sa_M3m in HM3. cbv zeta in HM3.
destruct HM3 as (HCORE & R20 & R21 & R24 & HBUF & HB0 & HSTR & O2 & HREP2 & HACCT & HMLE).
pose proof HCORE as HCORE0.
unfold sa_core in HCORE. cbv zeta in HCORE.
destruct HCORE as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R23 & R25 & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrsc & _).
assert (Hin1pos : In (1, pos) (frames Sc)) by (rewrite Hfrsc; left; reflexivity).
pose proof (saa_budgets MT MTL R uri id placement client) as Hbud. cbv zeta in Hbud.
destruct Hbud as (_ & EV4 & _ & _ & _ & LV4 & _ & _ & _ & AC4 & _).
(* the seed at M3: the registers as atoms, no region, no fact *)
pose proof (saa_seed0 Wc regs1 memc L_M3 (mkFacts [] [] []) ltac:(split; [exact I | split; exact I])) as HS.
set (E1 := Eimg (Ereg regs1 [])) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by apply Eimg_env.
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs1 r).
{ intros n r Hn'. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E1. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn'. }
pose proof (fun r => st_ok_pi_restrict_reg _ _ _ _ r HS) as HRA.
clearbody E1.
(* 0x8a574 .. 0x8a57c: `mv a0,s8`, `mv a1,s7`, `jal arg_s` *)
paj_run_shc (SRr_run_pi_AJ B LAWS) (SRr_run_pi_AJ_call B LAWS) HS HJ.
{ apply awr_ok_nil. }
try (set (mdv := with_vm_backing _ _ _) in *; clearbody mdv).
pose proof (frame_of_read_only _ [] _ _ eq_refl HF) as HmemE.
pose proof (fun r => st_ok_restrict_reg SEGS _ E1 _ _ r HS) as HRB.
pose proof (saa_regs_eq E1 _ _ regs1 (ms_regs ms) saa_kz HRA HRB ltac:(vm_compute; reflexivity)) as KR.
pose proof (saa_regs_eq E1 _ _ regs1 (ms_regs ms) [20; 21; 22; 24] HRA HRB ltac:(vm_compute; reflexivity)) as KR3.
prreg HS (1%bv : bv 5) A1. prreg HS (10%bv : bv 5) A10. prreg HS (11%bv : bv 5) A11.
rewrite (EE1 24%nat 24%bv eq_refl), R24 in A10.
rewrite (EE1 23%nat 23%bv eq_refl), R23 in A11.
assert (A1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + L_M4)) by (rewrite A1; reflexivity).
pmkst HS.
rewrite HmemE in HJ |- *.
pose proof (proj1 HJ) as HARc.
pose proof (saa_core_kept B LAWS ly S W regs mem md O lyc Sc Wc regs1 (ms_regs ms) memc mdc memc mdv (sa_ev2 R) pos
  (fun _ => False) HCORE0 HJ (fun a H => False_ind _ H) (fun a _ _ => eq_refl) KR) as HCORE1.
(* b = F + 32 as an object of the frame (1, pos) *)
destruct (al_frames _ _ LAWS lyc Sc Wc memc mdv 1 pos HARc Hin1pos) as (HF32 & _ & _ & _).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdv 1 pos HARc Hin1pos) as (HF0 & HFc & _).
change (fs_frame_bytes 1) with 128 in HFc.
pose proof (dec_length id Hid) as Hdl.
assert (E8 : frame_addr lyc 1 pos = 8 * (frame_addr lyc 1 pos / 8)) by (Z.div_mod_to_equations; lia).
assert (HFOBJ : afobj SEGS B lyc Sc Wc memc (frame_addr lyc 1 pos + 32) (Z.of_nat (length (dec id)) + 1)).
{ split; [|split].
  - exists 1, pos. split; [exact Hin1pos|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|].
    change (fs_frame_bytes 1) with 128. lia.
  - Z.div_mod_to_equations. lia.
  - intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    destruct (Z_lt_le_dec x (frame_addr lyc 1 pos + 40)) as [Hx1|Hx1].
    + assert (Hq : x / 8 = frame_addr lyc 1 pos / 8 + 4 + 0)
        by (symmetry; apply Z.div_unique with (r := x - frame_addr lyc 1 pos - 32); lia).
      rewrite Hq. rewrite !Z.add_assoc. exact (HB0 0 ltac:(lia)).
    + assert (Hq : x / 8 = frame_addr lyc 1 pos / 8 + 4 + 1)
        by (symmetry; apply Z.div_unique with (r := x - frame_addr lyc 1 pos - 40); lia).
      rewrite Hq. rewrite !Z.add_assoc. exact (HB0 1 ltac:(lia)). }
assert (HTAIL : forall x, Some (dec id) = Some x ->
  atail_vis SEGS Wc memc (frame_addr lyc 1 pos + 32 + Z.of_nat (length x))).
{ intros x Hx. injection Hx as <-. exact (cmd_fobj_tail SEGS B LAWS HB lyc Sc Wc memc mdv _ (dec id) HARc HFOBJ HSTR). }
assert (HLEN : Z.of_nat (length (dec id)) + 1 <= LMAX + 1) by (unfold LMAX; lia).
(* arg_s(c, b) *)
apply (saa_call B MT HB LAWS MTL SIGP IMG TARG_S ly S W regs mem md ch pu id pp pc uri placement client R O
  lyc Sc Wc (ms_regs ms) memc mdv pos [sarg uri] O2 (sa_ev2 R) (sa_acc2 MT R uri) (sa_live2 uri)
  (frame_addr lyc 1 pos + 32) (Some (dec id)) L_M4 HCX0 HCORE1 HBUF HREP2 ltac:(cbn [length]; lia) HACCT HMLE A1'
  ltac:(unfold L_M4, AF_sup_add; lia) ltac:(reflexivity) A10 A11
  (or_intror (ex_intro _ (dec id) (conj eq_refl (conj HSTR (conj HLEN HFOBJ)))))
  HTAIL EV4 LV4 AC4).
(* back at M4 *)
intros ly2 S2 W2 regs2 mem2 md2 O4 HC2 HP2 EF2 HB2 HR2 HA2 HM2.
apply (HM4 fx ly S W regs mem md ch pu id pp pc uri placement client R O ly2 S2 W2 regs2 mem2 md2 pos HCX0 Hfrm).
assert (KP : forall z, In z [20; 21; 22; 24] -> getr regs2 (Z_to_bv 5 z) = getr regs1 (Z_to_bv 5 z)).
{ intros z Hz. rewrite (HP2 z ltac:(unfold acallee_saved; cbn [In] in Hz; lia)). exact (KR3 z Hz). }
unfold sa_M4m. cbv zeta.
split; [exact HC2|].
split; [saa_kr KP R20 20|]. split; [saa_kr KP R21 21|]. split; [saa_kr KP R24 24|].
split; [exact HB2|].
exists O4. split; [exact HR2|]. split; [exact HA2 | exact HM2].
Qed.
End e.
End f.
End d.
Print Assumptions sa_m3_ok.
