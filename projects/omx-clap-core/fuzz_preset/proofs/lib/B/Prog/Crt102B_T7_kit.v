(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 142 of its 184 lines of code are new or changed and 472 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move): cb7k_call at the wle' contract
   (the internal file WLE-CONTRACT.md), as Crt102Kit.crt102rw_call_ch: the journals at R := YA0nH.wle' SEGS
   YGcfRehidePost.RZ_cf (notations AJ / AJW), the callee's text in SRr' with apost_base_xFR at R (PRH_Base's fpostF;
   a plain text by Crt102Kit.crt102rw_lift_xF / crt102rw_lift_x), the walk in YA0nH.SRr' SEGS RZ_cf; the rule
   YCbqGwild.aj_call_xbFR at R under YSRrG.SRr'_bind / SRr'_mono. Names and binder lists unchanged. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan
   d663f82d7f488d30, unstripped twin c90d4fa54d43160b): the CALL KIT of FREE-PIECES-102 Part 7a row T7 (CRT-B-CEXIT,
   B' C + the exit, +0x6f8 .. +0x80c).
   The lemmas a segment of check_round_trip on B' uses to make a call to a callee whose text is
   given, and come back: the call rule cb7k_call, the return site cb7k_ret, and the two view-to-memory steps
   cb7k_mr_of_aview / cb7k_agree_of_aview.

   proves no function (kind: segment lemma support).

   INPUTS OF RECORD:
   - base commit 1ec37cdf5c5 (Crt102Glue.v; the contract texts at the kit tip 3ac20a5c9e30).
   - the A' originals: lib/A/Prog/Crt102Kit.v blob fe9d87b61d62 (crt102rw_mr_of_aview :690, crt102rw_agree_of_aview
     :700, crt102rw_ret :777, crt102rw_call :790), ported, not imported.
   - the image-B kit this file cites and does not restate: lib/B/Prog/Crt102KitB.v
     (moved unchanged from Crt102B_T4.v): cb4_sp (the entry's stack facts), cb4_chain (the frame-pointer
     chain at sp1), cb4_fb; cb4_rdword_of_val_mem / cb4_fpchain_keep / cb4_live_call are there too, so they are not
     written here.
   - engine: YCbqGcall.v aj_call_xF (the call rule this one specialises), YC1fP.v ret_ok_codeptr_v.
   - build route pins102: FACTS 8f3e7e1a07f1, PAU pau-preset-102 (the #102 pins' agent directory).

   WHAT THE B' PORT CHANGES BEYOND THE RENAME (prh_img_A -> prh_img_B, PI_prog_A -> PI_prog_B, A_prog_listing ->
   B_prog_listing, CRT_PC_A -> CRT_PC_B, crt_bregs -> crt_bregs_B, the prefix crt102rw_ -> cb4_ or cb7k_):
   1. THE RETURN OFFSETS. The A' text bounds a return offset by 2048 (A' body: 466 instructions, to +0x744). The B' body
      is 544 instructions, to +0x87c (the row's brief :77, not in this tree), and T7's own return sites are +0x800
      (fuzz_free) and +0x808 (pj_free), both >= 2048. So cb7k_ret / cb7k_call take 0 <= off < 4096.
   2. THE FUNCTION'S SLOT. crt102rw_ret rewrote CRT_PC_A to the numeral 4752; here CRT_PC_B (Crt102Img.v:699,
      4 * CRT_SLOT_B) is only BOUNDED (0 <= CRT_PC_B < 2 ^ 16, even), by vm_compute, and no numeral of it is typed.
   3. THE STACK. cb4_sp gives sp0 - 255 <= sp1 (A': sp0 - 240 <= sp1). cb7k_call KEEPS the A' budget premise
      STK1 + 240 <= STKC: the A' bound is derived again from cb4_sp's own facts, sp0 mod 16 = 0 and sp1 mod 32 = 0,
      which put sp0 - sp1 in {224, 240}. (256 would also go through; 240 is the true bound, so the premise is weaker.)
   4. THE CHAIN. cb4_chain (Crt102KitB.v) takes the journal and crt_saved and gives the chain AT sp1 directly, where
      crt102rw_chain took the live state and any sp2 in [sp0 - 256, sp0 - 16].
   5. THE GLUE. crt_side lost its position conjunct (Crt102Glue.v 7719492eb9d3:217-224), so the read-only view
      arodata_okP is its 6th conjunct, not its 7th.
   6. THE RETURN CONFIGURATION. The continuation of cb7k_call is stated at `crt_cfg fx' off regs2 mem2 md2` at CRT_PC_B
      (T4's cfgB) and ends in T4's QFb, so a caller chains it into a T4 / T7 boundary statement with no conversion;
      the A' spelling `mkCfg (mkst fx' regs2 (Z_to_bv 64 (BASE + (CRT_PC_A + off))) mem2 rom) md2` is its unfolding.

   THE CALLEE. As in the A' text, the callee's text is the caller's premise (Hcallee), in the float form apost_base_xF
   at any Q. The two callees of T7 plug in so:
   - fuzz_free (PRH_FnAlloc.v tfuzz_free_specX, fpostm): fpostm .. Q0 is apost_base_x .. (fQmn mem Q0) by unfolding,
     and YCbqG.v apost_base_x_F (under SRr_mono) moves it to apost_base_xF at the call's frm_zero premise; Q := fQmn ..
   - pj_free (PRH_FnPj.v tpj_free_specX, fpostWm at the caller window d): at d = 0 (&back lies in the class-3 fake
     frame, which prhReader_at accepts without a window) fpostW's journal is at (STK + 0) (spZ regs + 0) and its window
     clause is empty, so Z.add_0_r and apost_base_x_F give apost_base_xF; Q := fQmn .. of the text's Q.

   NUMERALS. LENGTH: 4096 (the bound on the function's own offsets, item 1; and the least text address, the A'
   text's), 240 (the frame and realignment bound of item 3), 16 / 32 (the entry and the realigned alignment).
   DERIVED: 2 ^ 16 / 2 ^ 30 / 2 ^ 31 / 2 ^ 40 / 2 ^ 64 (address bounds, checked by vm_compute or bv ranges).
   WORD: register numbers 1 2 3 4 8. No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YGcallMx YGcallMxmn YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Crt102Glue Crt102Img Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB Crt102KitB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
(* the re-hiding move's world relation and step relation (YA0nH), its step lemmas (YSRrG), the
   zone (YGcfRehidePost.RZ_cf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope bv_scope.
Local Open Scope Z_scope.

(* ======================================================================================================== *)
(* image B' at the B instance: the preamble of Crt102KitB.v (Section, instances, notations), so every name below
   means what it means there. *)
Section t7k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
Context {RL : PrhRoomLive} {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Notation STKC := (@STK_check_round_trip prh_img_B).

(* ---- bytes outside the image that the journal's view keeps are the same bytes, writability included
   (Crt102Kit.v :689-708, image-generic but for SEGS) ---- *)
Lemma cb7k_mr_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> aview SEGS H' m' a = aview SEGS H m a ->
  mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof.
intros H H' m m' a Ha Hn E. unfold aview, mbyte in E.
rewrite (seg_rom_none SEGS a Ha Hn) in E.
destruct (mrestrict H' m' (Z_to_bv 64 a)) as [b'|]; destruct (mrestrict H m (Z_to_bv 64 a)) as [b|];
  cbn [option_map] in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma cb7k_agree_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) (X : Z -> Prop),
  (forall x, X x -> 0 <= x < 2 ^ 64 /\ ~ in_img SEGS x /\ aview SEGS H' m' x = aview SEGS H m x) ->
  pj_agreeR SEGS (mrestrict H m) (mrestrict H' m') X.
Proof.
intros H H' m m' X HX y Hy. destruct (HX y Hy) as (Hr & Hn & E).
pose proof (cb7k_mr_of_aview H H' m m' y Hr Hn E) as Em.
split; [unfold mbyte; rewrite Em; reflexivity|].
intros Hw. unfold writable_at, wview in *. rewrite Em. exact Hw.
Qed.

(* ---- the return site of a call the body makes: a text address of check_round_trip, below 2 ^ 31 (Crt102Kit.v
   :776-783; the offset bound 4096 and the slot bounds are B''s, items 1 and 2 of the header) ---- *)
Lemma cb7k_ret : forall off, 0 <= off < 4096 -> off mod 2 = 0 ->
  4096 <= BASE + (CRT_PC_B + off) < 2 ^ 31 /\ (CRT_PC_B + off) mod 2 = 0 /\ 0 <= CRT_PC_B + off < 2 ^ 40.
Proof.
intros off H1 H2.
assert (HB : 4096 <= BASE < 2 ^ 30) by (split; vm_compute; first [discriminate | reflexivity]).
assert (HP : (0 <= CRT_PC_B < 2 ^ 16) /\ CRT_PC_B mod 2 = 0) by (split; [split|]; vm_compute; first [discriminate | reflexivity]).
destruct HP as (HP & HP2).
split; [lia|]. split; [|lia]. rewrite Z.add_mod by lia. rewrite HP2, H2. reflexivity.
Qed.

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* the re-hiding move: every journal below at R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf, the
   relation of the glue's crt_live_journal and of QF *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).
(* the journal at a wild-trace budget WS (kb round: crt_live's journal is at a budget WS with wbudget [] kb WS) *)
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARx RZW).

Section g.
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
  (doc : Z) (t : PjTree.jv) (D : list (Z * Z)) (x : list Z)
  (Lam : list (Z * Z)) (peak cnt ran most : Z)
  (CTX0 : list (list Z)) (a_mod_at a_stamp : Z).
#[local] Notation sp0 := (spZ regs).
#[local] Notation sp1 := (@CRT_sp1 regs).
#[local] Notation liveB := (@crt_live rc prh_img_B RL SK B_prog_listing PA B ARx
  ly S Hp W regs mem md doc t D Lam peak most).
#[local] Notation QFb := (@QF fx rc prh_img_B RL SK B_prog_listing PA B ARx rp_sm rp_x rp_os rp_i rp_H0
  ly S Hp W regs mem md doc t D Lam peak cnt ran most).
#[local] Notation cfgB := (@crt_cfg rc B_prog_listing PA CRT_PC_B).
(* the B' register snapshot without doc (T4 names only dregsB = this /\ x22 = doc; after L2 doc is gone, the
   seam's crt_at_L3_B / crt_at_C_B carry crt_bregs_B) *)
#[local] Notation bregsB := (@crt_bregs_B regs).

(* the Section hypotheses of Crt102B_T4.v :584-586, same text: the allocator relation's laws and
   tcheck_round_trip_specX's premises at the entry (Crt102Top.v discharges them from the text's) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.

(* ---- A CALL FROM check_round_trip AT THE REALIGNED sp (Crt102Kit.v :785-852, the model there being Crt102Arms.v's
   arms_rtt_call, generalised over the callee): the live state with the jal next, the kept registers, the return
   site, the callee's budget and footprint. The callee's text is supplied at the fpre the call establishes, in the
   float form (a callee whose text leaves the float state alone gives it by apost_base_x_F), together with the
   shape of the frame chain the call reads (cb4_chain: empty, or check_round_trip's own record on the entry chain
   ch), which a callee whose trace is a premise (fuzz_free's call_trace) needs; the continuation receives both
   journals, the kept registers, the float state the callee left and the callee's Q, at the return site's
   configuration cfgB fx' off.
   ARGUMENT ORDER after the Sections close (About in the dev log): {fx rc RL SK} B ARx rp_sm rp_x rp_os rp_i rp_H0
   ly S Hp W regs mem md ch doc t D x Lam peak cnt ran most LAWS HPRE, then the binders below. `x` is there because
   cb4_sp and cb4_chain take it (T4's own abstraction); any list serves. ---- *)
Lemma cb7k_call : forall (fxk : YK11.FPState) STK1 FP1 (off pcc : Z) Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc
    peakc cntc ownc ranc Q {kbg : nat},
  frm_zero (@YK11.fp_csr fxk) ->
  @st_ok SEGS fxk E ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = pcc ->
  bv_unsigned (ew E 2) = sp0 ->
  liveB kbg lyc Sc Hpc Wc (ms_mem ms) mdc kj pos Dx Lamc peakc cntc ownc ranc ->
  bregsB (ms_regs ms) (frame_addr lyc CRT_CID pos) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (CRT_PC_B + off)) -> 0 <= off < 4096 -> off mod 2 = 0 ->
  0 <= STK1 -> STK1 + 240 <= STKC ->
  fp_sub_x B STKC sp0 [] FP1 ly S [(CRT_CID, pos)] lyc Sc ->
  (forall ch1, (ch1 = [] \/ ch1 = (sp0, raZ regs, s0Z regs) :: ch) ->
     fpre (fx := fxk) B ARx STK1 lyc Sc Hpc Wc (ms_regs ms) (ms_mem ms) mdc ch1 ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc
       (mkCfg (@YK11.mkst fxk (ms_regs ms) (Z_to_bv 64 pcc) (ms_mem ms) (YK11.seg_rom SEGS)) mdc)
       (apost_base_xFR (fx := fxk) (SK := SK) SEGS B PST ARx RZW STK1 FP1 (ms_regs ms) lyc Sc Hpc Wc (ms_mem ms) mdc Q)) ->
  (forall (fx' : YK11.FPState) ly2 S2 Hp2 W2 regs2 mem2 md2 k1,
     frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fxk fx' ->
     (exists WS, AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] ly2 S2 Hp2 W2 mem2 md2 (kj + k1) WS /\
        YCbqGwild.wbudget [] kbg WS) ->
     AJ STK1 sp1 FP1 lyc Sc Hpc Wc (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
     aregs_preserved (ms_regs ms) regs2 -> Q ly2 S2 Hp2 W2 regs2 mem2 md2 ->
     YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W2 (cfgB fx' off regs2 mem2 md2) QFb) ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (mkCfg ms mdc) QFb.
Proof.
intros fxk STK1 FP1 off pcc Wc E ss ms mdc lyc Sc Hpc kj pos Dx Lamc peakc cntc ownc ranc Q kbg HFZ HS Hrv Hpcs HE2 HL
  HBR Hra Hoff Hoff2 HSTK0 HSTK1 HFP Hcallee HK.
destruct (crt_live_journal HL) as (WS0 & HJ & HB0). pose proof (crt_live_saved HL) as HSV.
pose proof (crt_side_arodata (crt_live_side HL)) as HRO.
pose proof (crt_bregs_B_sp HBR) as R2. pose proof (crt_bregs_B_gp HBR) as R3. pose proof (crt_bregs_B_tp HBR) as R4.
pose proof (crt_bregs_B_s0 HBR) as R8. pose proof (crt_bregs_B_s1 HBR) as R9. pose proof (crt_bregs_B_s2 HBR) as R18.
pose proof (crt_bregs_B_s4 HBR) as R20. pose proof (crt_bregs_B_s3 HBR) as R19. pose proof (crt_bregs_B_s7 HBR) as R23.
pose proof (crt_bregs_B_s9 HBR) as R25. pose proof (crt_bregs_B_s11 HBR) as R27.
pose proof HPRE as ((HAR & Hra0 & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HRO0 & Hhi & Hrac).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof YM05.alloc_ceiling_lt as Hc47.
pose proof (cb4_sp B ARx ly S Hp W regs mem md ch HPRE) as (Hs16 & Hsc & Hs47 & Hs1 & Hs32 & Hs0).
(* the A' bound sp0 - 240 <= sp1, from cb4_sp's alignments (header item 3) *)
assert (Hs240 : sp0 - 240 <= sp1).
{ pose proof Hs16 as H16. pose proof Hs32 as H32.
  apply Z.mod_divide in H16; [|lia]. apply Z.mod_divide in H32; [|lia].
  destruct H16 as [q Hq]. destruct H32 as [q' Hq']. lia. }
pose proof HJ as (HARc & HLYc & _).
pose proof HLYc as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
destruct (cb7k_ret off Hoff Hoff2) as (Hr1 & Hr2 & Hr3).
destruct (cb4_chain B ARx ly S Hp W regs mem md ch HPRE [(CRT_CID, pos)] lyc Sc Hpc Wc (ms_mem ms) mdc kj HJ HSV)
  as (ch1 & Hch1 & Ech1).
set (o := sp1 - sp0).
assert (Hspz : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hspc : getr (ms_regs ms) 2 = sv_denot E (SOff 2 o)).
{ apply bv_eq. rewrite denot_SOff, HE2, R2. unfold w64. rewrite unsigned_lit_small by lia.
  rewrite YP0m.zcanon_small by (unfold o; lia). unfold o. lia. }
assert (Hs0z : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr. }
assert (Hraz : raZ (ms_regs ms) = BASE + (CRT_PC_B + off)) by (unfold raZ; rewrite Hra; apply unsigned_lit_small; lia).
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ (* the caller's journal is at its budget WS0 (crt_live's kb journal): the budgeted call rule at RZW at the callee's
     empty budget, P := (fun WS1 => WS1 = []), the callee's text by YCbqGwild.apost_base_xbF_of_xR (the A' twin:
     Crt102Kit.crt102rw_call_ch at the kb round) *)
  refine (@YCbqGwild.aj_call_xbFR fxk rc SK SEGS B PST ARx cf_head LAWS (@pa_segs_low rc B_prog_listing PA)
    RZW (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) Wc E ss ms
    STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc mdc kj WS0 STK1 FP1 o (ew E 2) (getr (ms_regs ms) 1) ch1
    (fun WS1 => WS1 = []) Q HS Hrv HJ Hspc eq_refl HE2 _ _ HSTK0 _ _ _ eq_refl _ _ _ _ HFP).
  - unfold o. apply Z.mod_divide in Hs16; [|lia]. destruct Hs16 as [q Hq]. apply Z.mod_divide in Hs32; [|lia].
    destruct Hs32 as [q' Hq']. apply Z.mod_divide; [lia|]. exists (2 * q' - q). lia.
  - unfold o. lia.
  - unfold o. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - rewrite Hra. apply (ret_ok_codeptr_v (PI := PA)); [exact Hr3 | exact Hr2].
  - rewrite Hra, unsigned_lit_small by lia. lia.
  - replace (sp0 + o) with sp1 by (unfold o; lia). rewrite Hs0z. exact Hch1.
  - intros HPRE1. rewrite Hpcs. eapply (YSRrG.SRr'_mono SEGS YGcfRehidePost.RZ_cf).
    + apply (Hcallee ch1 Ech1). split; [exact HPRE1|]. split; [exact HRO|].
      split; [rewrite Hspz, Eshi; lia|]. split; [rewrite Hraz; lia | exact HFZ].
    + intros W' c' _ Hpo. apply YCbqGwild.apost_base_xbF_of_xR; [reflexivity | exact Hpo]. }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & -> & HFZ2 & HFK2 & HPW & HJ2 & HJ1 &
  HP & HQ).
subst WS1. rewrite app_nil_r in HJ2.
replace (sp0 + o) with sp1 in HJ1 by (unfold o; lia).
rewrite Hra. exact (HK fx' ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HFZ2 HFK2 (ex_intro _ WS0 (conj HJ2 HB0)) HJ1 HP HQ).
Qed.

End g.
End f.
End t7k.
