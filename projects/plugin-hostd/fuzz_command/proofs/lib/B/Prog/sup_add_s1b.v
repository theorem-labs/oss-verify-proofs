(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: descriptors_panel_get's walk from the join of record()'s arms (0x8d180) to the call of xstrdup (plugin-hostd/fuzz_command.asan), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v (a segment proved from the next one's statement: seed, run, branch, call) and lib/A/Prog/sup_reply_code.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/descriptors_panel_get_s4.v, with its module paths and module names changed; 154 of its 191 lines of code are new or changed and 270 lines of the source are left out. *)
(* sup_add's walk on the ASan+UBSan build of plugin-hostd/fuzz_command, stage 1, part b: the call of record(REC_ADD)
   at 0x8a534 and its return to M1 (0x8a538).

   From the machine state at record's entry (the run of sup_add_s1.v ends there: a0 = 0, ra = M1, the callee-saved
   registers of sa_core, the frame's saves and flag word, the recorder's bytes as at the entry), record's statement
   (record_c.v trecord_spec, at the ambient FP state: its post is apost_base, so the call returns at the same FP
   state) is composed by cl_callS_pg (PaCallPg.v: record writes g_rec's ncalls and the slot, program statics), with
   the frame chain of s0 = sp0 from sup_add_lem.v's sa_chain_at; the mid-state sa_M1m follows from record's post,
   and the next stage SA_M1_stmt is applied at the same FP state. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI09 YG0s YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v YI0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaLibG PaDenot PaLibF PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaSB PaCallRun PaCall PaNoChain PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
record_c arg_s_c mix_call_c hand_back_c answer_c xmalloc_c sup_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_add_s0 sup_add_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts CmdRecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import sup_add_s1a.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac s1_cs := unfold acallee_saved;
  match goal with |- context[bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.

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
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.

(* From record's entry (called at 0x8a534 with a0 = REC_ADD = 0, ra = M1) to the post, through M1. *)
Lemma s1_call : SA_M1_stmt B MT ->
forall ly S W regs mem md ch pu id pp pc uri placement client R O S2 (regsc : bvmap 5 word) memc mdc pos,
sa_cx B MT ly S W regs mem md ch pu id pp pc uri placement client R O ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
ajournal SEGS B SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md [(1, pos)] ly S2 W memc mdc 0 ->
ablocks B ly S2 = ablocks B ly S -> blocks_bytes S2 = blocks_bytes S -> (exists f, S2 = set_fs f S) ->
(forall a, s1_rec a -> rdW W memc a = rdW W mem a) ->
(forall p n i, In (p, n) O -> 0 <= i < req_size n -> rdW W memc (p + i) = rdW W mem (p + i)) ->
sa_frame (rdW W memc) (spZ regs) regs ->
rdword (rdW W memc) (frame_addr ly 1 pos + 120) = Some (flag_addr ly 1 pos) ->
getr regsc 1 = Z_to_bv 64 (BASE + L_M1) ->
getr regsc 2 = w64 (sa_s1 (spZ regs)) -> getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 (spZ regs) -> getr regsc 9 = w64 (sa_s1 (spZ regs)) -> getr regsc 10 = w64 0 ->
getr regsc 18 = w64 (frame_addr ly 1 pos) -> getr regsc 19 = getr regs 11 ->
getr regsc 20 = getr regs 13 -> getr regsc 21 = getr regs 12 -> getr regsc 22 = getr regs 10 ->
getr regsc 23 = w64 (frame_addr ly 1 pos + 32) -> getr regsc 25 = w64 (SHADOW_OFF + frame_addr ly 1 pos / 8) ->
getr regsc 26 = w64 (frame_addr ly 1 pos) -> getr regsc 27 = w64 (-8) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (SIG CS_record)) memc (seg_rom SEGS)) mdc)
  (sa_final B MT ly S W regs mem md R O uri id placement client).
Proof using HB LAWS MTL MTFL SIGP IMG TRECORD.
intros HM1 ly S W regs mem md ch pu id pp pc uri placement client R O S2 regsc memc mdc pos
  CX HFRM0 HJ Eab Hbb (fS2 & ES2) KR KB HFR HFL X1 X2 X3 X4 X8 X9 X10 X18 X19 X20 X21 X22 X23 X25 X26 X27.
pose proof CX as CX'. unfold sa_cx in CX'. cbv zeta in CX'.
destruct CX' as (HPRE & Hfr7 & HROD & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREP & HEV & _ & HMOK).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof pa_base_lo as HBLO.
assert (FFS : SUP_ADD_STK = 16736) by reflexivity. assert (FRS : RECORD_STK = 16560) by reflexivity.
pose proof (s1_O_blocks B ly S (rdW W mem) R O HREP) as HOb.
assert (HObc : forall pn, In pn O -> In pn (ablocks B ly S2)) by (intros pn Hpn; rewrite Eab; exact (HOb pn Hpn)).
pose proof HJ as (HARc & HLYc & _ & _ & _ & Hfrsc & Hnevc & _).
assert (HinF : In (1, pos) (frames S2)) by (rewrite Hfrsc; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S2 W memc mdc 1 pos HARc HinF) as (HF0 & HFc & _).
change (fs_frame_bytes 1) with 128 in HFc.
set (sp0 := spZ regs) in *.
assert (Hsp0r : 0 <= sp0 < 2 ^ 64) by (unfold sp0, spZ; apply s1_bvrange).
assert (Hs1 : sa_s1 sp0 = sp0 - 128 \/ sa_s1 sp0 = sp0 - 144).
{ unfold sa_s1. pose proof (Z.div_mod (sp0 - 128) 32 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (sp0 - 128) 32 ltac:(lia)) as M1.
  pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2. lia. }
assert (Ho16 : (sa_s1 sp0 - sp0) mod 16 = 0).
{ destruct Hs1 as [E|E]; rewrite E;
  [replace (sp0 - 128 - sp0) with (-128) by lia | replace (sp0 - 144 - sp0) with (-144) by lia]; reflexivity. }
assert (Hspc : spZ regsc = sp0 + (sa_s1 sp0 - sp0)).
{ unfold spZ at 1. rewrite X2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hs0 : s0Z regsc = sp0) by (unfold s0Z; rewrite X8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
(* record's premises at the call *)
destruct (sa_chain_at B LAWS ly S W regs mem md ch R O ly S2 W memc mdc 0 pos (sa_s1 sp0) HPRE HREP HJ HFR ltac:(lia))
  as (ch1 & HCH).
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW W memc))
  by exact (CmdRecRest.cmd_rodata_kept SEGS B LAWS HB IMG ly S W mem md ly S2 W memc mdc SUP_ADD_STK sp0 (sa_FP O)
      [(1, pos)] 0 HAR HJ (s1_saFP_cases B ly S (rdW W mem) ly S2 R O HREP) HROD).
assert (HREPc : rec_repA B ly S2 (rdW W memc) R O)
  by exact (s1_rep_kept B ly S (rdW W mem) ly S2 (rdW W memc) R O HREP HObc KR KB).
assert (HEVc : st_nev S2 + EV_RECORD R <= EV_MAX).
{ unfold EV_SUP_ADD in HEV.
  assert (0 <= EV_ARG_S + EV_ARG_S + EV_ARG_S + EV_ARG_S + Z.max EV_ANSWER EV_HAND_BACK) by (vm_compute; discriminate).
  lia. }
assert (HMLE0 : mo_le MT S S2 0) by (rewrite ES2; apply (mo_le_set_fs_r MT MTFL S S fS2 0); apply (mle_start MT S MTL)).
pose proof (mo_free_nonneg MT MTL) as HFnn.
assert (HXR : 0 <= XM_RECORD MT R) by (unfold XM_RECORD, rec_spill_frees; destruct (Nat.ltb _ _); nia).
assert (HXM : forall n, 0 <= XM_XMALLOC MT n) by (intros n; unfold XM_XMALLOC, LIVE_XMALLOC; apply (mo_malloc_nonneg MT MTL); lia).
assert (HMOc : mo_ok MT S2 (XM_RECORD MT R)).
{ lazymatch type of HMOK with mo_ok _ _ ?T =>
  assert (HXS : XM_RECORD MT R <= T) end.
  { unfold XM_SUP_ADD, XM_ARG_S, XM_ANSWER, XM_HAND_BACK.
    repeat match goal with |- context [XM_XMALLOC MT ?n] =>
      let H := fresh "HX" in pose proof (HXM n) as H; revert H; generalize (XM_XMALLOC MT n); intros end.
    lia. }
  exact (mok_station MT S S2 _ 0 (XM_RECORD MT R) MTL HMOK HMLE0 HXR ltac:(lia)). }
assert (HRA : YK0s.ret_ok (getr regsc 1)) by (rewrite X1; apply ret_ok_codeptr_v; [unfold L_M1, AF_sup_add; lia | reflexivity]).
assert (HRA4 : 4096 <= bv_unsigned (getr regsc 1))
  by (rewrite X1, unsigned_lit_small by (unfold L_M1, AF_sup_add; lia); unfold L_M1, AF_sup_add; lia).
(* record: footprint g_rec's ncalls, the slot and (spill arm) the recorder's blocks; cl_callS_pg *)
eapply SRr_bind.
{ eapply (cl_callS_pg B LAWS W regsc memc (Z_to_bv 64 (SIG CS_record)) SUP_ADD_STK sp0 (sa_FP O) ly S W mem md
    [(1, pos)] ly S2 mdc 0 RECORD_STK (rca_recFP R O) (EV_RECORD R) (sa_s1 sp0 - sp0) (getr regsc 1) ch1 _ HJ Hspc Ho16).
  - lia.
  - rewrite FRS. lia.
  - rewrite FFS, FRS. lia.
  - exact X3.
  - exact X4.
  - reflexivity.
  - exact HRA.
  - exact HRA4.
  - replace (sp0 + (sa_s1 sp0 - sp0)) with (sa_s1 sp0) by lia. rewrite Hs0. exact HCH.
  - intros HPREc. rewrite (rca_sig_record SIGP).
    pose proof (TRECORD fx ly S2 W regsc memc mdc ch1 0 R O HPREc HRODc X10 ltac:(unfold REC_FN_COUNT; lia)
      HREPc HEVc HMOc) as HCL.
    unfold cfg_at in HCL. unfold apost_base in HCL. exact HCL.
  - intros a Ha. left. destruct (s1_recfp R O a Ha) as (HfpO & [Hpg | Hbk]).
    + split; [exact HfpO|]. right. split; [exact (rca_HPROG B HB a Hpg) | exact (CmdRecBase.cif_prog_img _ _ IMG a Hpg)].
    + split; [exact HfpO|]. left. destruct (inFP_ablocks_fp_inv O a Hbk) as (p & n & Hpn & Hr).
      exists p, n. split; [exact (HObc _ Hpn) | exact Hr]. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 &
  (Fr & O1 & Hslot & HPerm & HlenF & HFO & HREP1 & HO1 & Hbb3 & Hmle3)).
(* ---- back at M1 (0x8a538) ---- *)
rewrite X1.
apply (HM1 fx ly S W regs mem md ch pu id pp pc uri placement client R O ly2 S3 W2 regs3 mem3 md3 pos CX HFRM0).
pose proof HJc3 as (_ & HLYc3 & _).
pose proof HLYc3 as (_ & _ & _ & _ & _ & EF3 & _).
assert (EFa3 : frame_addr ly2 1 pos = frame_addr ly 1 pos) by (unfold frame_addr; rewrite EF3; reflexivity).
assert (EFl3 : flag_addr ly2 1 pos = flag_addr ly 1 pos) by (unfold flag_addr; rewrite EF3; reflexivity).
destruct (s1_call_agree B RECORD_STK (sp0 + (sa_s1 sp0 - sp0)) (rca_recFP R O) ly S2 W memc mdc ly2 S3 W2 mem3 md3
  (EV_RECORD R) pos (frame_addr ly 1 pos) (sa_s1 sp0) (2 ^ 64) HJc3 HinF eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
  (fun a Ha => s1_recfp_off B LAWS IMG ly S2 W memc mdc R O pos a HARc HObc HinF Ha)) as (KS3 & KF3).
assert (CS3 : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs3 rr = getr regsc rr)
  by (intros rr Hr; pose proof (HP3 (bv_unsigned rr) Hr) as Hx; rewrite Z_to_bv_bv_unsigned in Hx; exact Hx).
unfold sa_M1m, sa_core. cbv zeta. fold sp0. rewrite EFa3, EFl3.
split.
{ split.
  { replace (sa_ev1 R) with (0 + EV_RECORD R) by (unfold sa_ev1; lia). exact HJ3. }
  split.
  { intros j r Hj k Hk.
    assert (Hj13 : (j < 13)%nat) by (apply (proj1 (nth_error_Some sa_saved j)); rewrite Hj; discriminate).
    rewrite KS3 by lia. exact (HFR j r Hj k Hk). }
  split.
  { change (fs_frame_bytes 1) with 128. replace (frame_addr ly 1 pos + 128 - 8) with (frame_addr ly 1 pos + 120) by lia.
    unfold rdword in HFL |- *. rewrite !KF3 by lia. exact HFL. }
  split; [rewrite (CS3 2%bv ltac:(s1_cs)); exact X2|].
  split; [rewrite (CS3 3%bv ltac:(s1_cs)); exact X3|].
  split; [rewrite (CS3 4%bv ltac:(s1_cs)); exact X4|].
  split; [rewrite (CS3 8%bv ltac:(s1_cs)); exact X8|].
  split; [rewrite (CS3 9%bv ltac:(s1_cs)); exact X9|].
  split; [rewrite (CS3 18%bv ltac:(s1_cs)); exact X18|].
  split; [rewrite (CS3 19%bv ltac:(s1_cs)); exact X19|].
  split; [rewrite (CS3 23%bv ltac:(s1_cs)); exact X23|].
  split; [rewrite (CS3 25%bv ltac:(s1_cs)); exact X25|].
  split; [rewrite (CS3 26%bv ltac:(s1_cs)); exact X26|].
  rewrite (CS3 27%bv ltac:(s1_cs)); exact X27. }
split; [exact Hslot|].
split; [rewrite (CS3 20%bv ltac:(s1_cs)); exact X20|].
split; [rewrite (CS3 21%bv ltac:(s1_cs)); exact X21|].
split; [rewrite (CS3 22%bv ltac:(s1_cs)); exact X22|].
exists O1. split; [exact HREP1|]. split.
- exact (s1_acct B ly S O ly S2 ly2 S3 Fr O1 (recb_ablocks_nodup_m B ly S2 W memc mdc HARc) Eab Hbb HOb HPerm HFO HO1 Hbb3).
- unfold sa_acc1. replace (XM_RECORD MT R) with (0 + XM_RECORD MT R) by lia.
  exact (mle_station MT S S2 S3 0 (XM_RECORD MT R) MTL HMLE0 Hmle3).
Qed.
End e.
End f.
End d.
