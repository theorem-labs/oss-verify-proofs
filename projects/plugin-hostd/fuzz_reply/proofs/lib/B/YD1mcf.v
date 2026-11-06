(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YD1m.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: made from lib/B/YD1m.v (tfib_lib_site_x) for the cf driver of image B, as
   lib/A/AD1mcf.v (a working branch 46f1762ad5a) was made from lib/A/AD1m.v; A's text with image B's modules
   and names (lib/B's W8 files, YCfn / YCfn_cf's _b names, YE01 / YE2k from lib/B, YCeg, YD2f, YD1ucf, YD1w_cf,
   ReplyGuardB).  The call site lib_site_cf is derived from the cf program interface fr_lib_contract_drv
   (B/YD1w_cf.v).  Changes against the donor: every allocator predicate is over ARcf at Hp = []; the event room is
   gone, LIBROOM is preset's LIB_ROOM abudget_cf CF_LIB discharged from Wf_cf and qloose (lib_room_fr_of_wf); the
   live-state bounds, the surviving blocks and the footprint are YCfn_cf's (fr_live_pre_b, fr_live_post_b, fr_surv_b,
   sink_token :: fr_FP_b); fr_LI, rom_view, NP and the readable stack above sp pass through.  KF-COUNT #7: the meter's
   room MT_PRE asks the run count to leave this call's step, NS S + XNMAX <= NRUN (at MT_sec, NS is a Theorem Labs lane's nsec_cf
   and NRUN := cf_kmax), which the caller passes in; the post's `mo_le MT S S' (XN_LIB n)` gives the caller back the
   count's step NS S' <= NS S + XNMAX (NS_MO, XN_BND).  The room is asked for THIS call only (not `NS S <= NRUN`): at
   MT_sec, mo_ok MT S (XM_LIB n) is nsec S + XM_LIB n <= KMAX, so `NS S <= NRUN` would force NRUN + XM_LIB n <= KMAX
   on top of NS_START's NRUN >= 12 + 4 * XNMAX, i.e. 5 * SEC_CALL + 12 <= cf_kmax, false at reply's 2 ^ 23 (a Theorem Labs lane's
   measurement; a Theorem Labs lane's ruling 2026-10-30 15:16Z; A's 1d79995f144). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0ncf YGcfNames YG01cf YG08cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCfn YCeg YD2f YD1ucf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_G YCfn_cf YD1w_cf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* The interface's room, at preset's ceiling and per-call allowance (PresetCfnA.v section 3: CF_LIB = 2 ^ 33). *)
Definition CF_LIB_FR : Z := 2 ^ 33.
Definition LIBROOM_fr {cp : CfParams} (S : astate) : Prop := LIB_ROOM abudget_cf CF_LIB_FR S.

(* preset's lib_room_of_wf (PresetCfnA.v): the room holds before every call from the state invariant and, since field
   round 3, the call's hull admission cf_hull_ok (Reusable/YG08cf.v:312 abudget_room_cf). *)
Lemma lib_room_fr_of_wf : forall (cp : CfParams) U pp cc bb s, @WfP_cf cp U pp cc bb s -> qloose s ->
  @cf_hull_ok cp s -> @LIBROOM_fr cp s.
Proof.
  intros cp U pp cc bb s W QL HT. unfold LIBROOM_fr, LIB_ROOM.
  apply (abudget_room_cf U pp cc bb s CF_LIB_FR W QL HT). unfold CF_LIB_FR. lia.
Qed.

(* the live bytes at each of the driver's calls: the input buffer (<= 2 ^ 26), the payload block (below the buffer's
   size) and up to three growths of the harness's survivors (ATopKeeper's A/AD1r_heap_cf.H_bytes on image A: g_src's table and
   g_out's buffer each call) *)
Definition DRV_LIVE : Z := 2 ^ 27 + 3 * (ATABLE + OUT_MAX).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {ci : CfImg} {cp : CfParams}.
Section c.
Variable B : asyms.
Variable NP : astate -> Prop.
(* the run count (at MT_sec: a Theorem Labs lane's nsec_cf), its bound for the run, and the most one call adds to it *)
Variable NS : astate -> Z.
Variable NRUN : Z.
Variable XNMAX : Z.
(* route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the world relation of the call's step. The library run can free, so cut_x's
   contract at R (fr_lib_contract_cf_xR) gives the continuation only R W W' and its journal is ajournal_xR at R; the
   cf instance takes R := wle' tfibsegs RZ_cf (B/YD1pcf.v). The three laws in the route-R crew's order and names. *)
Variable R : world tfibsegs -> world tfibsegs -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle tfibsegs W W' -> R W W'.
Local Notation segs := tfibsegs.
Local Notation ARx := (ARcf (cp := cp) tfibsegs B).
Local Notation GF := (G_fr_c B).

(* The donor's lib_pre (B/YD1w.v) over ARcf at Hp = []. *)
Definition lib_pre_cf (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) : Prop :=
  ARx ly S [] W mem md /\ YK0s.ret_ok (getr regs 1%bv) /\ raZ regs = RA_LLVMF /\
  getr regs 3%bv = w64 (as_gp B) /\ getr regs 4%bv = w64 (as_tp B) /\
  spZ regs mod 16 = 0 /\ sp_window_lo - 208 <= spZ regs <= sp_window_hi /\ spZ regs + 32 <= ly_top ly <= spZ regs + 4128 /\
  ly_stk_lo ly = ASAN_CEIL /\ ly_stk_hi ly = kHighMemEnd /\
  (forall a, spZ regs - LLVMF_STK <= a < spZ regs -> apresent (w_H W) mem a) /\
  s0Z regs < alloc_ceiling /\
  qtight S.

(* The donor's lib_site_x (B/YD1w.v) at fuzz_reply's cf interface: the call of LLVMFuzzerTestOneInput as the
   driver loop consumes it, at call ci0. *)
Definition lib_site_cf : Prop :=
  forall ly S (W : world segs) (regs : bvmap 5 word) mem md p n (pl : list byte) (ci0 : Z) (K : lleaf -> TSet),
  lib_pre_cf ly S W regs mem md ->
  getr regs 10%bv = w64 p -> getr regs 11%bv = w64 n ->
  ((n = 0 /\ p = A_EMPTY_tfa) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) ->
  n = Z.of_nat (length pl) -> garr8 segs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) pl) ->
  frames S = [] -> fr_live_pre_b S -> NP S -> NS S + XNMAX <= NRUN -> blocks_bytes S <= DRV_LIVE ->
  0 <= ci0 < 4 -> fr_LI B ci0 ly S W mem -> rom_view segs W mem ->
  (* W8's readable-stack conjunct (fr_lib_pre_drv's STKR) *)
  (forall a, spZ regs <= a < ly_top ly -> aview segs (w_H W) mem a <> None) ->
  (* the HFP clause (fr_lib_pre_drv's) *)
  List.NoDup ((if n =? 0 then [] else [(p, n)]) ++ fr_hblks_b W mem) /\ incl (fr_hblks_b W mem) (ablocks B ly S) ->
  (* the XCNT clause (fr_lib_pre_drv's) *)
  fr_xcnt_ok_b B ly S W mem (if n =? 0 then [] else [(p, n)]) ->
  (* the CAPOUT clause (fr_lib_pre_drv's) *)
  fr_capout_ok_b W mem ->
  arodata_ok B (aview segs (w_H W) mem) ->
  FINV ly (w_H W) mem ->
  (* field round 3 (Part A): the call memory's read-only RELRO bytes (fr_lib_pre_drv's last) *)
  YG0dcf.arodata_ok_cf segs B mem ->
  fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None -> Namei.fd_names_path (m_fds md) YI16.sink_path = false ->
  Fs.fs_sorted (m_fs md) = true ->
  AI segs (w_H W) (w_A W) md ->
  (forall (l : lleaf) (W' : world segs) (c' : config),
     R W W' -> AI segs (w_H W') (w_A W') (cfg_model c') ->
     (exists ly' S' regs' mem' md' k,
        c' = cfg_at segs RA_LLVMF regs' mem' md' /\
        ajournal_xR (SK := YE2k.tfib_sink_head) segs B GF ARx R LLVMF_STK (spZ regs) (sink_token :: fr_FP_b regs ly S W mem)
          ly S [] W mem md [] ly' S' [] W' mem' md' k /\
        fr_live_post_b S S' k /\ NP S' /\
        aregs_preserved regs regs' /\ getr regs' 10%bv = w64 0 /\
        fr_surv_b B ly S W mem ly' S' W' mem' /\
        fr_LI B (ci0 + 1) ly' S' W' mem' /\ rom_view segs W' mem' /\
        (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
        m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
        Namei.fd_names_path (m_fds md') YI16.sink_path = false /\
        FINV ly' (w_H W') mem' /\
        (forall i, 0 <= i < n -> aview segs (w_H W') mem' (p + i) = aview segs (w_H W) mem (p + i)) /\
        (List.NoDup (fr_hblks_b W' mem') /\ incl (fr_hblks_b W' mem') (ablocks B ly' S')) /\
        fr_xcnt_ok_b B ly' S' W' mem' (if n =? 0 then [] else [(p, n)]) /\
        fr_capout_ok_b W' mem' /\
        (* the run count's step (the post's mo_le, by NS_MO and XN_BND) *)
        NS S' <= NS S + XNMAX /\
        (* field round 3 (Part A): the RELRO bytes at the return (fr_lib_post_drvR's last) *)
        YG0dcf.arodata_ok_cf segs B mem') ->
     srealizes segs c' (K l)) ->
  srealizes segs (cfg_at segs A_LLVMF regs mem md) (LIBK pl (m_fs md) K).

Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
(* the meter's room for the call (the interface's pre `mo_ok MT S (XM_LIB n)`), from what the driver knows at every
   call: the live bytes leave the call's room (fr_live_pre), the non-primary room NP, the run count under its bound
   NRUN, the allocator's state invariant and qtight, for an input of less than 2 ^ 26 bytes.  The instance's meter is
   KF-COUNT's MT_sec (a Theorem Labs lane's lib/B/ReplyKfMeterB.v) with NS := a Theorem Labs lane's nsec_cf; its witness is
   lib/B/YD1w_cf_wit.v mt_pre_wit_B_sec (a Theorem Labs lane), under `NRUN + XM_LIB n <= KMAX` for every input length.  At
   ameter_triv it is `fun _ _ _ _ _ _ _ _ => I`. *)
Hypothesis MT_PRE : forall S n, Wf_cf (as_universe B) S -> qtight S -> blocks_bytes S <= DRV_LIVE -> NP S -> NS S + XNMAX <= NRUN ->
  0 <= n < 2 ^ 26 -> mo_ok MT S (XM_LIB n).
(* the meter's step bounds the run count's step, and one call's step is at most XNMAX *)
Hypothesis NS_MO : forall S S' n, mo_le MT S S' (XN_LIB n) -> NS S' <= NS S + XN_LIB n.
Hypothesis XN_BND : forall n, 0 <= n < 2 ^ 26 -> 0 <= XN_LIB n <= XNMAX.
(* field round 3: the hull admission cf_hull_ok (Reusable/YG0dcf.v acall_pre_cf) from the run count's bound; at reply
   cf_hull_ok S is nsec_cf S <= cf_kmax (YGcfAbudget.v section 6), so at NS := nsec_cf, NRUN := cf_kmax it holds by
   conversion *)
Hypothesis HULL_NS : forall S, NS S <= NRUN -> cf_hull_ok S.
Hypothesis RO_IN : forall a, RLO <= a < RHI -> in_ro_tfa a.
Hypothesis LIBC : fr_lib_contract_drvR B MT XM_LIB XN_LIB RLO RHI LIBROOM_fr NP R.

Lemma layout_of_ARcf : forall ly S Hp W mem md, ARx ly S Hp W mem md -> layout_ok ly.
Proof. intros ly S Hp W mem md H. exact (amc_layout _ _ _ _ _ (proj1 H)). Qed.

Theorem tfib_lib_site_cf : lib_site_cf.
Proof.
  intros ly S W regs mem md p n pl ci0 K HPRE R10 R11 Hpn Hlen Hpl Hfr Hlive HNP HNS Hbb Hci HLI Hrom Hstk HHFP HXC
    HCAP Hro HFI HAD Hfree Hnames Hsorted HAI CONT.
  pose proof HPRE as (HAR & Hret & Hra & Hgp & Htp & Hal & [Wlo Whi] & [Tlo Thi] & Elo & Ehi & Hpres & Hs0 & Hqt).
  pose proof (layout_of_ARcf _ _ _ _ _ _ HAR) as LO. pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & _).
  pose proof (lo_stk_ceil _ LO) as SC. unfold ASAN_CEIL in SC. unfold ly_bot in *. unfold sp_window_lo, sp_window_hi in *.
  destruct HFI as ((M & HAM) & Henv & Hhead).
  apply (LIBC ly S [] W regs mem md p n pl M K ci0 HAI).
  - split.
    { split; [exact HAR|]. split; [exact Hret|]. split; [rewrite Hra; cbv; discriminate|]. split; [exact Hgp|].
      split; [exact Htp|]. split.
      - unfold astk_ok. rewrite Ehi. unfold ly_bot, kHighMemEnd, YCfn.LLVMF_STK, ASTACK, kStackSpan in *. repeat split; lia.
      - split; [exact Hpres|]. split; [| exact Hqt]. apply achain_low. exact Hs0. }
    split; [exact Hra|]. split; [exact R10|]. split; [exact R11|]. split; [exact Hpn|].
    split; [exact Hlen|]. split; [exact Hpl|]. split; [exact Hfr|]. split; [reflexivity|]. split; [exact Hlive|].
    split; [exact (lib_room_fr_of_wf cp _ _ _ _ S (amc_wf _ _ _ _ _ (proj1 HAR)) (qtight_qloose S Hqt)
      (HULL_NS S ltac:(pose proof (XN_BND 0 ltac:(lia)); lia)))|].
    split; [exact HNP|]. split; [exact Hci|]. split; [exact HLI|]. split; [exact Hrom|].
    split.
    { intros a Ha Hno Hne. apply Hro; [| exact Hno | exact Hne]. destruct Ha as [Ha | Ha]; [left; exact Ha | exact (RO_IN a Ha)]. }
    split; [exact (conj Henv (conj Hhead Hnames))|].
    split; [exact Hfree|]. split; [exact Hsorted|]. split; [exact HAM|].
    split; [| exact (conj Hstk (conj HHFP (conj HXC (conj HCAP HAD))))].
    apply (MT_PRE S n (amc_wf _ _ _ _ _ (proj1 HAR)) Hqt Hbb HNP HNS). destruct Hpn as [[-> _] | [Hn _]]; lia.
  - intros l W' c' Hwle HAI' (ly' & S' & regs' & mem' & md' & k & Hc' & HJ & Hlv & HNP' & HP & Ha0 & HSV & HLI' & Hrom'
      & Hfdl & Hmfs & Hret' & Hout & Hsorted' & (Henv' & Hhead' & Hnames') & HAM' & HMO' & Hplk & HHFP' & HXC' & HCAP' & HAD').
    assert (HNS' : NS S' <= NS S + XNMAX).
    { assert (Hn : 0 <= n < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hn _]]; lia).
      pose proof (NS_MO S S' n HMO'). pose proof (XN_BND n Hn). lia. }
    apply (CONT l W' c' Hwle HAI'). exists ly', S', regs', mem', md', k.
    split; [exact Hc'|]. split; [exact HJ|]. split; [exact Hlv|]. split; [exact HNP'|]. split; [exact HP|].
    split; [exact Ha0|]. split; [exact HSV|]. split; [exact HLI'|]. split; [exact Hrom'|].
    split; [exact Hfdl|]. split; [exact Hmfs|]. split; [exact Hret'|]. split; [exact Hout|]. split; [exact Hsorted'|].
    split; [exact Hnames'|].
    split; [| exact (conj Hplk (conj HHFP' (conj HXC' (conj HCAP' (conj HNS' HAD')))))].
    split; [exists M; exact HAM' | exact (conj Henv' Hhead')].
Qed.
End c.
End b.
