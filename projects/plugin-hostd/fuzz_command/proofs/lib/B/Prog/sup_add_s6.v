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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_add_s3a.v, with its module paths and module names changed; 135 of its 181 lines of code are new or changed and 956 lines of the source are left out. *)
(* sup_add's walk on the ASan+UBSan build of plugin-hostd/fuzz_command, stage M5 (0x8a5a4) -> M6 (0x8a5bc):
   arg_s(c, client or "-").

   The run 0x8a5a4 .. 0x8a5b8 (`beqz s4`, `mv s6,s4`, `addi s4,s10,64`, `mv a0,s8`, `mv a1,s6`, `jal arg_s`) writes no
   memory. The walk splits on client first: the seed's fact on atom 20 (s4 = pc) decides the `beqz`: pc is not 0
   when client = Some x (astr_argA's p <> 0), pc = 0 when client = None. With client = Some x the string is the
   entry's (sup_add_ag.v saa_str moves astr_argA from the entry to the call); with None it is the literal "-" that
   s6 holds since M5 (saa_dash). s4 is buf = F + 64 afterwards. The call is saa_call; the recorder then holds the
   four arguments sa_A. *)
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

(* the seed's fact on atom 20 (s4 = pc): at least 1 for a client; for none, the condition s4 = 0 that decides the
   `beqz` *)
Definition s6_G (client : option (list byte)) : facts :=
  match client with
  | Some _ => mkFacts [(20%nat, mkAF 1 18446744073709551615 0)] [] []
  | None => mkFacts [] [mkAC BC_EQ (SOff 20 0) (SLit 0)] []
  end.

Lemma sa_m5_ok : SA_M6_stmt B MT -> SA_M5_at B MT.
Proof using HB LAWS MTL SIGP IMG TARG_S.
intros HM6 ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos HCX Hfrm HM5.
pose proof HCX as HCX0.
unfold sa_cx in HCX. cbv zeta in HCX.
destruct HCX as (HPRE & _ & HROD & _ & _ & _ & _ & _ & _ & _ & H13 & Hpc & _ & _ & _ & HC & _ & HREP0 & _).
pose proof HPRE as (HAR0 & _).
unfold sa_M5m in HM5. cbv zeta in HM5.
destruct HM5 as (HCORE & R20 & R22 & R24 & HBUF & O5 & HREP5 & HACCT & HMLE).
pose proof HCORE as HCORE0.
unfold sa_core in HCORE. cbv zeta in HCORE.
destruct HCORE as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R26 & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrsc & _).
assert (Hin1pos : In (1, pos) (frames Sc)) by (rewrite Hfrsc; left; reflexivity).
pose proof HACCT as (_ & _ & HLIVE & _).
pose proof (saa_budgets MT MTL R uri id placement client) as Hbud. cbv zeta in Hbud.
destruct Hbud as (_ & _ & _ & EV6 & _ & _ & _ & LV6 & _ & _ & _ & AC6).
(* the seed at M5: the registers as atoms, no region, the fact on atom 20 *)
assert (U20 : bv_unsigned (ew (Eimg (Ereg regs1 [])) 20) = pc).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs1 [] 20 20%bv eq_refl), R20, H13.
  apply unsigned_lit_small. lia. }
assert (HG : facts_ok (Eimg (Ereg regs1 [])) (s6_G client)).
{ destruct client as [x|]; cbn [s6_G].
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U20, Z.pow_0_r, Z.mod_1_r. destruct HC as (Hp0 & _). lia.
  - hnf in HC. split; [exact I|]. split; [|exact I]. cbn [f_conds conds_ok]. split; [|exact I].
    unfold acond_ok. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, U_SOff, U_SLit, U20, HC. vm_compute. reflexivity. }
pose proof (saa_seed0 Wc regs1 memc L_M5 (s6_G client) HG) as HS.
set (E1 := Eimg (Ereg regs1 [])) in HS, U20.
assert (HEI1 : img_env VAL A_LIM E1) by apply Eimg_env.
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs1 r).
{ intros n r Hn'. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E1. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn'. }
pose proof (fun r => st_ok_pi_restrict_reg _ _ _ _ r HS) as HRA.
clearbody E1.
destruct client as [x|]; cbn [s6_G] in HS, HRA.
- (* a client: a1 = s6 = s4 = pc *)
  (* 0x8a5a4 .. 0x8a5b8: `beqz s4` (not taken), `mv s6,s4`, `addi s4,s10,64`, `mv a0,s8`, `mv a1,s6`, `jal arg_s` *)
  paj_run_shc (SRr_run_pi_AJ B LAWS) (SRr_run_pi_AJ_call B LAWS) HS HJ.
  { apply awr_ok_nil. }
  try (set (mdv := with_vm_backing _ _ _) in *; clearbody mdv).
  pose proof (frame_of_read_only _ [] _ _ eq_refl HF) as HmemE.
  pose proof (fun r => st_ok_restrict_reg SEGS _ E1 _ _ r HS) as HRB.
  pose proof (saa_regs_eq E1 _ _ regs1 (ms_regs ms) saa_kz HRA HRB ltac:(vm_compute; reflexivity)) as KR.
  pose proof (saa_regs_eq E1 _ _ regs1 (ms_regs ms) [24] HRA HRB ltac:(vm_compute; reflexivity)) as KR3.
  prreg HS (1%bv : bv 5) A1. prreg HS (10%bv : bv 5) A10. prreg HS (11%bv : bv 5) A11. prreg HS (20%bv : bv 5) A20.
  rewrite (EE1 24%nat 24%bv eq_refl), R24 in A10.
  rewrite (EE1 20%nat 20%bv eq_refl), R20, H13 in A11.
  rewrite (EE1 26%nat 26%bv eq_refl), R26 in A20. unfold w64 in A20. rewrite unsigned_lit_small in A20; [fold (w64 (frame_addr lyc 1 pos + 64)) in A20|].
  2:{ pose proof HJ as (HARx & _).
      destruct (frames_bounds SEGS B LAWS lyc Sc Wc _ mdv 1 pos HARx Hin1pos) as (HF0 & HFc & _).
      pose proof asan_consts as (C1 & _). change (fs_frame_bytes 1) with 128 in HFc. lia. }
  assert (A1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + L_M6)) by (rewrite A1; reflexivity).
  pmkst HS.
  rewrite HmemE in HJ |- *.
  pose proof (proj1 HJ) as HARc.
  pose proof (saa_core_kept B LAWS ly S W regs mem md O lyc Sc Wc regs1 (ms_regs ms) memc mdc memc mdv (sa_ev5 R) pos
    (fun _ => False) HCORE0 HJ (fun a H => False_ind _ H) (fun a _ _ => eq_refl) KR) as HCORE1.
  (* the string: the entry's client, moved to the call *)
  assert (HARO : arodata_okP SEGS RLO RHI B (rdW Wc memc))
    by exact (saa_aro B HB LAWS IMG SUP_ADD_STK (spZ regs) [(1, pos)] ly S W mem md lyc Sc Wc memc mdv (sa_ev5 R) R O
      HAR0 HJ HREP0 HROD).
  pose proof (saa_str B HB LAWS IMG SUP_ADD_STK (spZ regs) [(1, pos)] ly S W mem md lyc Sc Wc memc mdv (sa_ev5 R) R O
    pc x HAR0 HJ HREP0 HROD HARO HLIVE HC) as HSTR.
  assert (HTAIL : forall y, Some x = Some y -> atail_vis SEGS Wc memc (pc + Z.of_nat (length y))).
  { intros y Hy. injection Hy as <-.
    exact (cmd_str_tail SEGS B LAWS HB IMG lyc Sc Wc memc mdv pc x HARc HSTR). }
  apply (saa_call B MT HB LAWS MTL SIGP IMG TARG_S ly S W regs mem md ch pu id pp pc uri placement (Some x) R O
    lyc Sc Wc (ms_regs ms) memc mdv pos [sarg uri; dec id; darg placement (bstr "-"%string)] O5 (sa_ev5 R)
    (sa_acc5 MT R uri id placement) (sa_live5 uri id placement) pc (Some x) L_M6 HCX0 HCORE1 HBUF HREP5
    ltac:(cbn [length]; lia) HACCT HMLE A1' ltac:(unfold L_M6, AF_sup_add; lia) ltac:(reflexivity) A10 A11
    (or_introl HSTR) HTAIL EV6 LV6 AC6).
  (* back at M6 *)
  intros ly2 S2 W2 regs2 mem2 md2 O6 HC2 HP2 EF2 HB2 HR2 HA2 HM2.
  apply (HM6 fx ly S W regs mem md ch pu id pp pc uri placement (Some x) R O ly2 S2 W2 regs2 mem2 md2 pos HCX0 Hfrm).
  assert (KP : forall z, In z [24] -> getr regs2 (Z_to_bv 5 z) = getr regs1 (Z_to_bv 5 z)).
  { intros z Hz. rewrite (HP2 z ltac:(unfold acallee_saved; cbn [In] in Hz; lia)). exact (KR3 z Hz). }
  assert (KP2 : forall z, In z [20] -> getr regs2 (Z_to_bv 5 z) = getr (ms_regs ms) (Z_to_bv 5 z)).
  { intros z Hz. exact (HP2 z ltac:(unfold acallee_saved; cbn [In] in Hz; lia)). }
  assert (P20 : getr regs2 20 = w64 (frame_addr ly2 1 pos + 64)) by (rewrite EF2; saa_kr KP2 A20 20).
  unfold sa_M6m. cbv zeta.
  split; [exact HC2|].
  split; [exact P20|]. split; [saa_kr KP R24 24|].
  split; [exact HB2|].
  exists O6. split; [exact HR2|]. split; [exact HA2 | exact HM2].
- (* no client: a1 = s6 = "-" *)
  paj_run_shc (SRr_run_pi_AJ B LAWS) (SRr_run_pi_AJ_call B LAWS) HS HJ.
  { apply awr_ok_nil. }
  try (set (mdv := with_vm_backing _ _ _) in *; clearbody mdv).
  pose proof (frame_of_read_only _ [] _ _ eq_refl HF) as HmemE.
  pose proof (fun r => st_ok_restrict_reg SEGS _ E1 _ _ r HS) as HRB.
  pose proof (saa_regs_eq E1 _ _ regs1 (ms_regs ms) saa_kz HRA HRB ltac:(vm_compute; reflexivity)) as KR.
  pose proof (saa_regs_eq E1 _ _ regs1 (ms_regs ms) [24] HRA HRB ltac:(vm_compute; reflexivity)) as KR3.
  prreg HS (1%bv : bv 5) A1. prreg HS (10%bv : bv 5) A10. prreg HS (11%bv : bv 5) A11. prreg HS (20%bv : bv 5) A20.
  rewrite (EE1 24%nat 24%bv eq_refl), R24 in A10.
  rewrite (EE1 22%nat 22%bv eq_refl), R22 in A11.
  rewrite (EE1 26%nat 26%bv eq_refl), R26 in A20. unfold w64 in A20. rewrite unsigned_lit_small in A20; [fold (w64 (frame_addr lyc 1 pos + 64)) in A20|].
  2:{ pose proof HJ as (HARx & _).
      destruct (frames_bounds SEGS B LAWS lyc Sc Wc _ mdv 1 pos HARx Hin1pos) as (HF0 & HFc & _).
      pose proof asan_consts as (C1 & _). change (fs_frame_bytes 1) with 128 in HFc. lia. }
  assert (A1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + L_M6)) by (rewrite A1; reflexivity).
  pmkst HS.
  rewrite HmemE in HJ |- *.
  pose proof (proj1 HJ) as HARc.
  pose proof (saa_core_kept B LAWS ly S W regs mem md O lyc Sc Wc regs1 (ms_regs ms) memc mdc memc mdv (sa_ev5 R) pos
    (fun _ => False) HCORE0 HJ (fun a H => False_ind _ H) (fun a _ _ => eq_refl) KR) as HCORE1.
  (* the string: the literal "-" *)
  assert (HARO : arodata_okP SEGS RLO RHI B (rdW Wc memc))
    by exact (saa_aro B HB LAWS IMG SUP_ADD_STK (spZ regs) [(1, pos)] ly S W mem md lyc Sc Wc memc mdv (sa_ev5 R) R O
      HAR0 HJ HREP0 HROD).
  pose proof (saa_dash B HB LAWS IMG lyc Sc Wc memc (cmd_ro_ok_of_aro SEGS B LAWS HB IMG lyc Sc Wc memc mdv HARc HARO))
    as HSTR.
  assert (HTAIL : forall y, Some (bstr "-"%string) = Some y -> atail_vis SEGS Wc memc (SA_DASH + Z.of_nat (length y))).
  { intros y Hy. injection Hy as <-.
    exact (cmd_str_tail SEGS B LAWS HB IMG lyc Sc Wc memc mdv SA_DASH _ HARc HSTR). }
  apply (saa_call B MT HB LAWS MTL SIGP IMG TARG_S ly S W regs mem md ch pu id pp pc uri placement None R O
    lyc Sc Wc (ms_regs ms) memc mdv pos [sarg uri; dec id; darg placement (bstr "-"%string)] O5 (sa_ev5 R)
    (sa_acc5 MT R uri id placement) (sa_live5 uri id placement) SA_DASH (Some (bstr "-"%string)) L_M6 HCX0 HCORE1
    HBUF HREP5 ltac:(cbn [length]; lia) HACCT HMLE A1' ltac:(unfold L_M6, AF_sup_add; lia) ltac:(reflexivity) A10 A11
    (or_introl HSTR) HTAIL EV6 LV6 AC6).
  (* back at M6 *)
  intros ly2 S2 W2 regs2 mem2 md2 O6 HC2 HP2 EF2 HB2 HR2 HA2 HM2.
  apply (HM6 fx ly S W regs mem md ch pu id pp pc uri placement None R O ly2 S2 W2 regs2 mem2 md2 pos HCX0 Hfrm).
  assert (KP : forall z, In z [24] -> getr regs2 (Z_to_bv 5 z) = getr regs1 (Z_to_bv 5 z)).
  { intros z Hz. rewrite (HP2 z ltac:(unfold acallee_saved; cbn [In] in Hz; lia)). exact (KR3 z Hz). }
  assert (KP2 : forall z, In z [20] -> getr regs2 (Z_to_bv 5 z) = getr (ms_regs ms) (Z_to_bv 5 z)).
  { intros z Hz. exact (HP2 z ltac:(unfold acallee_saved; cbn [In] in Hz; lia)). }
  assert (P20 : getr regs2 20 = w64 (frame_addr ly2 1 pos + 64)) by (rewrite EF2; saa_kr KP2 A20 20).
  unfold sa_M6m. cbv zeta.
  split; [exact HC2|].
  split; [exact P20|]. split; [saa_kr KP R24 24|].
  split; [exact HB2|].
  exists O6. split; [exact HR2|]. split; [exact HA2 | exact HM2].
Qed.
End e.
End f.
End d.
Print Assumptions sa_m5_ok.
