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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/sup_add_s3a.v, with its module paths and module names changed; 113 of its 161 lines of code are new or changed and 954 lines of the source are left out. *)
(* sup_add's walk on the ASan+UBSan build of plugin-hostd/fuzz_command, stage M1 (0x8a538) -> M2 (0x8a554):
   arg_s(c, uri).

   The run 0x8a538 .. 0x8a550: `mv s8,a0` (s8 = c), `sb zero,8(s9)` .. `sb zero,11(s9)` (buf[32]'s four shadow bytes
   marked usable; a shadow-store run: the seed has the frame's shadow window [8, 12) above s9 writable, no chunk, and
   sa_buf0 at the call is read from the chunks the run leaves there), `mv a1,s6` (a1 = uri), `jal arg_s`. uri is a
   string in a live block apart from the recorder's (sa_uri), moved to the call by sup_add_ag.v's saa_str. The call is
   saa_call; the recorder then holds [sarg uri]. *)
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

(* a one-byte value 0 read through a reader *)
Lemma saa_byte_of_aval : forall (rd : reader) a, aval_mem rd a 1 0 -> rd a = Some 0.
Proof. intros rd a H. pose proof (H 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0. exact H0. Qed.

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

Lemma sa_m1_ok : SA_M2_stmt B MT -> SA_M1_at B MT.
Proof using HB LAWS MTL SIGP IMG TARG_S.
intros HM2 ly S W regs mem md ch pu id pp pc uri placement client R O lyc Sc Wc regs1 memc mdc pos HCX Hfrm HM1.
pose proof HCX as HCX0.
unfold sa_cx in HCX. cbv zeta in HCX.
destruct HCX as (HPRE & _ & HROD & _ & H10 & Hpu & _ & _ & _ & _ & _ & _ & HU & _ & _ & _ & _ & HREP0 & _).
pose proof HPRE as (HAR0 & _).
destruct (saa_uri B LAWS ly S W mem md O pu uri HAR0 HU) as (u & -> & HUA).
unfold sa_M1m in HM1. cbv zeta in HM1.
destruct HM1 as (HCORE & R10 & R20 & R21 & R22 & O1 & HREP1 & HACCT & HMLE).
pose proof HCORE as HCORE0.
unfold sa_core in HCORE. cbv zeta in HCORE.
destruct HCORE as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R25 & _).
pose proof HJ as (HARc0 & _ & _ & _ & _ & Hfrsc & _).
assert (Hin1pos : In (1, pos) (frames Sc)) by (rewrite Hfrsc; left; reflexivity).
pose proof HACCT as (_ & _ & HLIVE & _).
pose proof (saa_budgets MT MTL R (Some u) id placement client) as Hbud. cbv zeta in Hbud.
destruct Hbud as (EV2 & _ & _ & _ & LV2 & _ & _ & _ & AC2 & _).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 1 pos HARc0 Hin1pos) as (HF0 & HFc & _).
change (fs_frame_bytes 1) with 128 in HFc.
pose proof asan_consts as (C1 & _).
pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)) as HF8.
assert (HF8h : frame_addr lyc 1 pos / 8 < 2 ^ 60) by (apply Z.div_lt_upper_bound; lia).
(* the seed at M1: the registers as atoms, the frame's shadow window [8, 12), no fact *)
assert (U25 : bv_unsigned (ew (Eimg (Ereg regs1 [])) 25) = SHADOW_OFF + frame_addr lyc 1 pos / 8).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs1 [] 25 25%bv eq_refl), R25.
  apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
pose proof (saa_seed B LAWS lyc Sc Wc regs1 memc mdc pos L_M1 8 12 (mkFacts [] [] []) HARc0 Hin1pos R25
  ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(split; [exact I | split; exact I])) as HS.
set (E1 := Eimg (Ereg regs1 [])) in HS, U25.
assert (HEI1 : img_env VAL A_LIM E1) by apply Eimg_env.
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs1 r).
{ intros n r Hn'. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E1. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn'. }
pose proof (fun r => st_ok_pi_restrict_reg _ _ _ _ r HS) as HRA.
clearbody E1.
(* the shadow store's window lies in the frame's shadow *)
assert (HZ : forall a, SHADOW_OFF + frame_addr lyc 1 pos / 8 + 8 <= a < SHADOW_OFF + frame_addr lyc 1 pos / 8 + 12 ->
  shadow_addr (frame_addr lyc 1 pos) <= a < shadow_addr (frame_addr lyc 1 pos) + 16)
  by (intros a Ha; unfold shadow_addr; lia).
(* 0x8a538 .. 0x8a550: `mv s8,a0`, `sb zero,8(s9)` .. `sb zero,11(s9)`, `mv a1,s6`, `jal arg_s` *)
paj_run_shc (SRr_run_pi_AJ B LAWS) (SRr_run_pi_AJ_call B LAWS) HS HJ.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_gen; [reflexivity | exact U25 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. unfold awr_byte. right; right; right; left.
  exists 1, pos. split; [left; reflexivity | right]. unfold in_zr, shadow_addr. cbn [fst snd].
  change (fs_frame_bytes 1 / 8) with 16. lia. }
try (set (mdv := with_vm_backing _ _ _) in *; clearbody mdv).
lazymatch goal with Hfr : frame_of E1 _ (mrestrict _ memc) (mrestrict _ ?m1) |- _ =>
  pose proof (kept_of_frame (segs:=SEGS) E1 _ (w_H Wc) memc m1
    (fun a => SHADOW_OFF + frame_addr lyc 1 pos / 8 + 8 <= a < SHADOW_OFF + frame_addr lyc 1 pos / 8 + 12) Hfr
    ltac:(intros ?b ?wlo ?whi ?a' ?Hin ?Hrr; vm_compute in Hin;
          repeat (destruct Hin as [?Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U25 in Hrr; lia|]);
          destruct Hin)) as KM end.
(* buf[32]'s four shadow bytes are 0: the chunks the run left in the window *)
pose proof (st_ok_region_nth E1 _ _ 0%nat _ HS eq_refl) as HRg. cbn [ms_mem restrict mkst] in HRg.
assert (HBUF1 : sa_buf0 (rdW Wc (ms_mem ms)) (frame_addr lyc 1 pos)).
{ intros i Hi. apply saa_byte_of_aval. apply aval_mem_view.
  replace (SHADOW_OFF + frame_addr lyc 1 pos / 8 + 8 + i) with (SHADOW_OFF + frame_addr lyc 1 pos / 8 + (8 + i)) by lia.
  assert (Hi' : 8 + i = 8 \/ 8 + i = 9 \/ 8 + i = 10 \/ 8 + i = 11) by lia.
  destruct Hi' as [Ho | [Ho | [Ho | Ho]]]; rewrite Ho;
  lazymatch goal with |- val_mem _ _ (_ + ?od) _ _ =>
    exact (field_of_region E1 _ 25%nat _ _ _ _ _ _ od 1%N (SLit 0) 0 HRg U25
      ltac:(cbn [In]; repeat (first [left; reflexivity | right])) eq_refl ltac:(cbn; lia) ltac:(lia)) end. }
pose proof (fun r => st_ok_restrict_reg SEGS _ E1 _ _ r HS) as HRB.
pose proof (saa_regs_eq E1 _ _ regs1 (ms_regs ms) saa_kz HRA HRB ltac:(vm_compute; reflexivity)) as KR.
pose proof (saa_regs_eq E1 _ _ regs1 (ms_regs ms) [20; 21] HRA HRB ltac:(vm_compute; reflexivity)) as KR3.
prreg HS (1%bv : bv 5) A1. prreg HS (10%bv : bv 5) A10. prreg HS (11%bv : bv 5) A11. prreg HS (24%bv : bv 5) A24.
rewrite (EE1 10%nat 10%bv eq_refl), R10 in A10, A24.
rewrite (EE1 22%nat 22%bv eq_refl), R22, H10 in A11.
assert (A1' : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + L_M2)) by (rewrite A1; reflexivity).
pmkst HS.
pose proof (proj1 HJ) as HARc.
pose proof (saa_core_kept B LAWS ly S W regs mem md O lyc Sc Wc regs1 (ms_regs ms) memc mdc (ms_mem ms) mdv (sa_ev1 R)
  pos _ HCORE0 HJ HZ KM KR) as HCORE1.
(* the recorder at the call: g_rec, record.spill and its blocks lie off the window *)
assert (KREC : forall a, A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
  inFP (ablocks_fp O1) a -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply KM.
  - destruct Ha as [Ha | [Ha | (r & Hr & Hr1 & Hr2)]]; [unfold A_G_REC, REC_SIZE in Ha; lia | unfold A_REC_SPILL, SC_SIZE in Ha; lia|].
    unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hqm). cbn [fst snd] in Hr1, Hr2.
    destruct (saa_rep_blocks B _ _ _ _ _ HREP1 (q, m) Hqm) as (Hb & Hm).
    destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc q m HARc0 Hb) as (_ & H4 & Hcq & _). lia.
  - intros Hw. destruct Ha as [Ha | [Ha | (r & Hr & Hr1 & Hr2)]]; [unfold A_G_REC, REC_SIZE, SHADOW_OFF in *; lia | unfold A_REC_SPILL, SC_SIZE, SHADOW_OFF in *; lia|].
    unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([q m] & <- & Hqm). cbn [fst snd] in Hr1, Hr2.
    destruct (saa_rep_blocks B _ _ _ _ _ HREP1 (q, m) Hqm) as (Hb & Hm).
    destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc q m HARc0 Hb) as (_ & H4 & Hcq & Hpapp & _).
    refine (fshadow_not_app (frame_addr lyc 1 pos) 16 q (req_size m) a _ _ Hpapp _ _); unfold SHADOW_OFF in Hw; lia. }
assert (HREP1' : rec_repA B lyc Sc (rdW Wc (ms_mem ms)) (rec_record R REC_ADD []) O1).
{ apply (rec_repA_kept B lyc Sc (rdW Wc memc) lyc Sc _ _ O1 HREP1); [|exact KREC].
  intros pn Hpn. exact (proj1 (saa_rep_blocks B _ _ _ _ _ HREP1 pn Hpn)). }
(* the string: the entry's uri, moved to the call *)
assert (HARO : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms)))
  by exact (saa_aro B HB LAWS IMG SUP_ADD_STK (spZ regs) [(1, pos)] ly S W mem md lyc Sc Wc (ms_mem ms) mdv (sa_ev1 R)
    R O HAR0 HJ HREP0 HROD).
pose proof (saa_str B HB LAWS IMG SUP_ADD_STK (spZ regs) [(1, pos)] ly S W mem md lyc Sc Wc (ms_mem ms) mdv (sa_ev1 R)
  R O pu u HAR0 HJ HREP0 HROD HARO HLIVE HUA) as HSTR.
assert (HTAIL : forall y, Some u = Some y -> atail_vis SEGS Wc (ms_mem ms) (pu + Z.of_nat (length y))).
{ intros y Hy. injection Hy as <-.
  exact (cmd_str_tail SEGS B LAWS HB IMG lyc Sc Wc (ms_mem ms) mdv pu u HARc HSTR). }
apply (saa_call B MT HB LAWS MTL SIGP IMG TARG_S ly S W regs mem md ch pu id pp pc (Some u) placement client R O
  lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv pos [] O1 (sa_ev1 R) (sa_acc1 MT R) 0 pu (Some u) L_M2 HCX0 HCORE1 HBUF1
  HREP1' ltac:(cbn [length]; lia) HACCT HMLE A1' ltac:(unfold L_M2, AF_sup_add; lia) ltac:(reflexivity) A10 A11
  (or_introl HSTR) HTAIL EV2 LV2 AC2).
(* back at M2 *)
intros ly2 S2 W2 regs2 mem2 md2 O2 HC2 HP2 EF2 HB2 HR2 HA2 HM2'.
apply (HM2 fx ly S W regs mem md ch pu id pp pc (Some u) placement client R O ly2 S2 W2 regs2 mem2 md2 pos HCX0 Hfrm).
assert (KP : forall z, In z [20; 21] -> getr regs2 (Z_to_bv 5 z) = getr regs1 (Z_to_bv 5 z)).
{ intros z Hz. rewrite (HP2 z ltac:(unfold acallee_saved; cbn [In] in Hz; lia)). exact (KR3 z Hz). }
assert (KP2 : forall z, In z [24] -> getr regs2 (Z_to_bv 5 z) = getr (ms_regs ms) (Z_to_bv 5 z)).
{ intros z Hz. exact (HP2 z ltac:(unfold acallee_saved; cbn [In] in Hz; lia)). }
unfold sa_M2m. cbv zeta.
split; [exact HC2|].
split; [saa_kr KP R20 20|]. split; [saa_kr KP R21 21|]. split; [saa_kr KP2 A24 24|].
split; [exact HB2|].
exists O2. split; [exact HR2|]. split; [exact HA2 | exact HM2'].
Qed.
End e.
End f.
End d.
Print Assumptions sa_m1_ok.
