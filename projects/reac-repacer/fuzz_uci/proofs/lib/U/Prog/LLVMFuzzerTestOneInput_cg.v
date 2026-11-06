(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_uci: the cut-free (SRcf) walk of fuzz_uci's
   LLVMFuzzerTestOneInput on the UBSan image, against lib/U/Prog/LLVMFuzzerTestOneInput_cfb.v's
   LLVMFuzzerTestOneInput_sr_contract_cf: LLVMFuzzerTestOneInput_holds_of_cf, as libreac/fuzz_decode's released
   lib/U/Prog/LLVMFuzzerTestOneInput_cg.v (with its fd_*_cg files) is to that release's U walk. Sections G and M are
   lib/U/Prog/LLVMFuzzerTestOneInput.v's with SR replaced by SRcf (SRcf_bind / SRcf_ret, llvm_run_norm_cf), the two
   SR callees taken at their cf contracts (check_no_overread_ccf.v, check_value_ccf.v) with the agree room
   (llvm_room_cf, room_cno_cf / room_cv_cf), and the early exit by llvm_early_cf; the instruction segments (e0_evt,
   sa_evt, sb_evt, sc_evt, sx_evt) and the frame cells are that file's, used as they are (module LW). Section M takes
   only the hypotheses its proofs use (that file's also lists MALLOC, FREE, BND and CT, which its proofs never use). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Spec Require Import UciModel.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog Require Import rp_uci_int_c rp_hot_clamp_c
  check_no_overread_c check_value_c check_clamp_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr
  LLVMFuzzerTestOneInput_early.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog Require Import LLVMFuzzerTestOneInput_cfb
  check_no_overread_ccf check_value_ccf LLVMFuzzerTestOneInput_early_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog Require LLVMFuzzerTestOneInput.
Import ListNotations.
Open Scope Z_scope.

Module LW := OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.U.Prog.LLVMFuzzerTestOneInput.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis HGG : ms_got_guard B = LLVM_GUARD_GOT.

Lemma g_pre : forall stk S L0 A0 mem0 md0 L A mem md regs K,
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - K -> spZ regs <= S -> 0 <= K ->
  YM05.alloc_ceiling + stk <= S -> spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  call_pre_k B (aa_MR API) K L A regs mem md.
Proof.
  intros stk S L0 A0 mem0 md0 L A mem md regs K
    (HM & HW & HB & HID & _ & _ & _ & _ & _ & Hstw & Herr & _) Hra Hal H1 H2 HK Hc H63 Htp.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact Hra|].
  split; [exact Hal|]. split; [lia|]. split; [exact H63|].
  split; [intros a Ha; apply Hstw; lia|]. split; [exact Htp|]. split; [exact Herr|].
  intros E. rewrite HID in E. discriminate.
Qed.

Lemma g_above : forall stk S L A regs mem md K E L' A' regs' mem' md',
  aa_MR API L A mem md ->
  call_post_k B (aa_MR API) K L A regs mem md E L' A' regs' mem' md' ->
  YM05.alloc_ceiling + stk <= S -> S - stk <= spZ regs - K -> S <= 2 ^ 64 -> 0 <= K ->
  (forall a, E a -> a < YM05.alloc_ceiling) ->
  forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
    (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a).
Proof.
  intros stk S L A regs mem md K E L' A' regs' mem' md' HM
    (HM2 & _ & _ & _ & _ & _ & _ & Hfr & _) H1 H2 H3 HK0 HE a Ha.
  pose proof YM05.alloc_ceiling_value as Hac.
  apply Hfr.
  - left. lia.
  - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM Ho). lia.
  - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM2 Ho). lia.
  - unfold scratch_k. intros [Hs|Hs]; [lia | pose proof (lf_errno_low B ERRNO_LOW a Hs); lia].
  - intros He. pose proof (HE a He). lia.
Qed.

Lemma g_run_cf : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs pc mem md L A
    (Q : machine_state -> Prop) (P : config -> Prop),
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) (@fp_regs fx') pc (@fp_csr fx') None
                      (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R F pc' fc m' W, ms = MState.MS R F pc' fc None m' (seg_rom rsegs) /\
     munch W (normalize rsegs mem) m' /\ wmono rsegs (normalize rsegs mem) m' /\
     (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x ->
        (S - stk <= x < S) \/ exists y k, lf_mine L0 A0 L A y k /\ y <= x < y + k)) ->
  (forall R F pc' fc m0', Q (MState.MS R F pc' fc None m0' (seg_rom rsegs)) ->
     forall regs' m', Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' ->
     lf_fr B API stk S L0 A0 mem0 md0 L A m' md ->
     SRcf B (mkCfg (@YK11.mkst (mkFP F fc) regs' pc' m' (YK11.seg_rom rsegs)) md) P) ->
  SRcf B (mkCfg (@YK11.mkst fx' regs pc mem (YK11.seg_rom rsegs)) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs pc mem md L A Q P FR Hc HS HE Hform HK.
  pose proof FR as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  apply (llvm_run_norm_cf B SEGS fx' regs pc mem md Q P Hh Hl Hro HE).
  - intros ms HQ. destruct (Hform ms HQ) as (R & F & pc' & fc & m' & W & -> & _). do 5 eexists. reflexivity.
  - intros R F pc' fc m0' HQ regs' m' Hx Hrel Hsame.
    destruct (Hform _ HQ) as (R2 & F2 & pc2 & fc2 & m2 & W & HE2 & MU & WM & HW).
    injection HE2 as ER EF EP EC EM. subst R2 F2 pc2 fc2 m2.
    assert (MU' : munch W mem m')
      by exact (munch_rel rsegs _ mem (normalize rsegs mem) m' m0' (mem_rel_normalize rsegs mem Hro) Hrel Hsame MU).
    assert (WM' : wmono rsegs mem m')
      by exact (wmono_rel rsegs mem (normalize rsegs mem) m' m0' (mem_rel_normalize rsegs mem Hro) Hrel Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs mem m' Hro Hsame).
    apply (HK R F pc' fc m0' HQ regs' m' Hx Hrel).
    eapply (lf_fr_evt B API SEGS AX HGG); [exact FR | exact Hc | exact HS | exact MU' | exact WM' | exact Hro' | exact HW].
Qed.

(* the two allocating callees of the loop body, at their cf contracts: a call's frame is the caller's frame below
   spZ regs *)
Lemma g_cno_cf : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A r nn cur bs bres
    (P : config -> Prop),
  (forall fx'' : YK11.FPState, @check_no_overread_contract_cf fx'' rc B API) ->
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - CNO_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  YK11.getr regs 10 = Z_to_bv 64 r -> YK11.getr regs 11 = Z_to_bv 64 nn -> YK11.getr regs 12 = Z_to_bv 64 cur ->
  INT_MIN <= cur <= INT_MAX -> 0 <= nn <= REPLY_MAX -> Z.of_nat (length bs) = nn -> blk_data B mem r bs ->
  (0 < nn -> in_block L A r nn) -> frm_zero (@fp_csr fx') -> res_ok_slots A bres -> cno_room_cf bres nn ->
  (forall (fx'' : YK11.FPState) L' A' regs' mem' md',
     frm_zero (@fp_csr fx'') ->
     lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     blocks L' A' = blocks L A -> res_ok_slots A' bres ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     SRcf B (mkCfg (@YK11.mkst fx'' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 CHECK_NO_OVERREAD) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A r nn cur bs bres P CNO FR Hc HS Hra Hal H1 H2 H63 Htp
    G10 G11 G12 Hcur Hnn Hlen BD IB Hfrm Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  eapply (SRcf_bind B).
  { apply (CNO fx' L A regs mem md r nn cur bs bres SEGS).
    - exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs CNO_STACK FR Hra Hal H1 H2
        ltac:(unfold CNO_STACK, CNO_FRAME, ALLOC_STACK; lia) Hc H63 Htp).
    - exact G10.
    - exact G11.
    - exact G12.
    - exact Hcur.
    - exact Hnn.
    - exact Hlen.
    - exact BD.
    - exact IB.
    - rewrite SEGS. exact MI.
    - exact Hfrm.
    - exact Hres.
    - exact Hroom. }
  intros c2 (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & Hfrm2 & Hpost & Eb & Hkept & Hgk & Hro2 & Hres2 & Hidt).
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | unfold CNO_STACK, CNO_FRAME, ALLOC_STACK in *; lia | lia | | | | | | exact Hidt | | ].
    - intros a Ha. exfalso. exact Ha.
    - intros a Ha. right. intros Hf. exact Hf.
    - intros a Hf Ha. exfalso. exact Hf.
    - intros a0 k0 Hin. rewrite Eb. exact (Hblk a0 k0 Hin).
    - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i (Hblk a0 k0 Hin) (fun H => H) Hi).
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp Eb Hres2).
  apply (g_above stk S L A regs mem md CNO_STACK (fun _ => False) L2 A2 regs2 mem2 md2 HM Hpost Hc H1 HS
    ltac:(unfold CNO_STACK, CNO_FRAME, ALLOC_STACK; lia)).
  intros a Ha. destruct Ha.
Qed.

Lemma g_cv_cf : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A r nn cur bs bres
    (P : config -> Prop),
  (forall fx'' : YK11.FPState, @check_value_contract_cf fx'' rc B API) ->
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - CV_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  YK11.getr regs 10 = Z_to_bv 64 r -> YK11.getr regs 11 = Z_to_bv 64 nn -> YK11.getr regs 12 = Z_to_bv 64 cur ->
  INT_MIN <= cur <= INT_MAX -> 0 <= nn <= REPLY_MAX -> Z.of_nat (length bs) = nn -> blk_data B mem r bs ->
  (0 < nn -> in_block L A r nn) -> frm_zero (@fp_csr fx') -> res_ok_slots A bres -> cv_room_cf bres nn ->
  (forall (fx'' : YK11.FPState) L' A' regs' mem' md',
     frm_zero (@fp_csr fx'') ->
     lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     YK11.getr regs' 10 = Z_to_bv 64 (rp_uci_int_m (zbytes bs) cur) ->
     blocks L' A' = blocks L A -> res_ok_slots A' bres ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     SRcf B (mkCfg (@YK11.mkst fx'' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 CHECK_VALUE) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A r nn cur bs bres P CV FR Hc HS Hra Hal H1 H2 H63 Htp
    G10 G11 G12 Hcur Hnn Hlen BD IB Hfrm Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  eapply (SRcf_bind B).
  { apply (CV fx' L A regs mem md r nn cur bs bres SEGS).
    - exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs CV_STACK FR Hra Hal H1 H2
        ltac:(unfold CV_STACK, CV_FRAME, ALLOC_STACK; lia) Hc H63 Htp).
    - exact G10.
    - exact G11.
    - exact G12.
    - exact Hcur.
    - exact Hnn.
    - exact Hlen.
    - exact BD.
    - exact IB.
    - rewrite SEGS. exact MI.
    - exact Hfrm.
    - exact Hres.
    - exact Hroom. }
  intros c2 (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & Hfrm2 & Hpost & G210 & Eb & Hkept & Hgk & Hro2 & Hres2 & Hidt).
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | unfold CV_STACK, CV_FRAME, ALLOC_STACK in *; lia | lia | | | | | | exact Hidt | | ].
    - intros a Ha. exfalso. exact Ha.
    - intros a Ha. right. intros Hf. exact Hf.
    - intros a Hf Ha. exfalso. exact Hf.
    - intros a0 k0 Hin. rewrite Eb. exact (Hblk a0 k0 Hin).
    - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i (Hblk a0 k0 Hin) (fun H => H) Hi).
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp G210 Eb Hres2).
  apply (g_above stk S L A regs mem md CV_STACK (fun _ => False) L2 A2 regs2 mem2 md2 HM Hpost Hc H1 HS
    ltac:(unfold CV_STACK, CV_FRAME, ALLOC_STACK; lia)).
  intros a Ha. destruct Ha.
Qed.

End G.

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis SINK : lf_sink_env B.
Hypothesis CNO : forall fx' : YK11.FPState, @check_no_overread_contract_cf fx' rc B API.
Hypothesis CV : forall fx' : YK11.FPState, @check_value_contract_cf fx' rc B API.
Hypothesis CC : check_clamp_contract.

Section Run.
Variables (stk empty : Z) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte)
  (md0 : Model) (ra p n : Z) (pl : list byte) (b : sbound) (j : nat).
Hypothesis BI : llvm_binds B API.
Hypothesis Hk : LLVM_K <= stk.
Hypothesis Hra : YK0s.ret_ok (Z_to_bv 64 ra).
Hypothesis Hpre : lib_pre B API stk empty L0 A0 regs0 mem0 md0 ra p n.
Hypothesis Hlen : n = Z.of_nat (length pl).
Hypothesis Hpd : blk_data B mem0 p pl.
Hypothesis Hsn : sink_none B mem0 md0.
Hypothesis Hsp : spZ regs0 <= 2 ^ 47.
Hypothesis Hroom : llvm_room_cf b.
Hypothesis Hro : ro_agree rsegs mem0.
Hypothesis Hn26 : n < 2 ^ 26.

Local Abbreviation Sx := (spZ regs0).
Local Abbreviation Sp := (spZ regs0 - 128).
Local Abbreviation P' := (bv_unsigned (reg_get regs0 10)).
Local Abbreviation sv0 := (LW.lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
  (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21) (reg_get regs0 22) (reg_get regs0 23) (reg_get regs0 24)
  (reg_get regs0 25)).
Local Abbreviation Post := (llvm_sr_post B API stk L0 A0 regs0 mem0 md0 ra p n b j).

Lemma f_bounds : 8368 <= stk /\ YM05.alloc_ceiling + stk <= Sx /\ Sx mod 16 = 0 /\ Sx <= 2 ^ 47 /\
  LF_RES_TOP < YM05.alloc_ceiling /\ 0 <= n.
Proof.
  pose proof Hpre as (_ & _ & _ & _ & _ & Hal & Hceil & _).
  pose proof Hk as Hk'. unfold LLVM_K, LLVM_FRAME, CNO_STACK, CNO_FRAME, ALLOC_STACK in Hk'.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  split; [lia|]. split; [exact Hceil|]. split; [exact Hal|]. split; [exact Hsp|]. split; [exact Hrt | lia].
Qed.

Lemma f_pay : 0 < n -> In (P', n) (blocks L0 A0) /\ 4096 <= P' /\ P' + n <= YM05.alloc_ceiling /\ P' = p.
Proof.
  intros Hn0.
  pose proof Hpre as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _ & Hpl & _).
  pose proof YM05.alloc_ceiling_value as Hac.
  destruct Hpl as [[-> _] | [_ (q & Hq & Hqp)]]; [lia|].
  pose proof (mr_blocks_range B _ (aa_laws API) L0 A0 mem0 md0 q n HM Hq) as (R1 & R2). rewrite Hqp in R1, R2.
  assert (E : P' = p).
  { assert (E10 : reg_get regs0 10 = Z_to_bv 64 p) by exact Hp. rewrite E10. apply MState.unsigned_lit. lia. }
  rewrite E. split; [apply blocks_In; exists q; split; [exact Hqp | exact Hq]|]. lia.
Qed.

Lemma f_p'range : 0 <= P' < 2 ^ 64.
Proof.
  pose proof (bv_unsigned_in_range _ (reg_get regs0 10)) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in R. exact R.
Qed.

(* the payload is a live block of every later state, with its bytes *)
Lemma f_blk : forall L A mem md, lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md -> 0 < n ->
  In (P', n) (blocks L A) /\ blk_data B mem P' pl.
Proof.
  intros L A mem md (HM & _ & _ & _ & _ & _ & _ & Hblk & Hbyt & _) Hn0.
  destruct (f_pay Hn0) as (Hin & H1 & H2 & E).
  split; [exact (Hblk _ _ Hin)|].
  intros i Hi. rewrite (Hbyt _ _ i Hin ltac:(lia)). rewrite E. exact (Hpd i Hi).
Qed.

Lemma f_norm : forall L A mem md cs, lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md ->
  (cells_size cs <= 128)%nat ->
  rw_cells rsegs mem Sp cs -> rw_cells rsegs (normalize rsegs mem) Sp cs.
Proof.
  intros L A mem md cs FR Hsz HC. pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI).
  pose proof BI as (SEGS & _).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5 & B6).
  apply (lf_rw_cells_norm B mem Sp cs SEGS MI); [|exact HC].
  intros i Hi Himg. pose proof (lf_in_img_top B _ SEGS Himg). pose proof (rw_cells_bound _ _ _ _ HC). lia.
Qed.

Lemma f_stk : forall L A mem md, lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md ->
  Frame.stk rsegs (normalize rsegs mem) (Sx - stk) Sp.
Proof.
  intros L A mem md FR. pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hstw & _ & _ & MI).
  pose proof BI as (SEGS & _).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5 & B6). pose proof YM05.alloc_ceiling_value as Hac.
  apply lf_stk; [lia | lia |]. intros a Ha. unfold writable_at.
  assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
  rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem MI)
             (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
  rewrite <- SEGS. exact (Hstw a ltac:(lia)).
Qed.

Lemma sr_exit_cf : forall (fx' : YK11.FPState) L A regs mem md mm vs jc jp,
  frm_zero (@fp_csr fx') -> lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md -> res_ok_slots A b ->
  reg_get regs 2 = Z_to_bv 64 Sp -> reg_get regs 3 = reg_get regs0 3 -> reg_get regs 4 = reg_get regs0 4 ->
  reg_get regs 8 = Z_to_bv 64 mm -> reg_get regs 26 = reg_get regs0 26 -> reg_get regs 27 = reg_get regs0 27 ->
  (mm = 1984 \/ mm = 16320) -> length vs = 5%nat -> Forall (fun v => INT_MIN <= v <= INT_MAX) vs ->
  rw_cells rsegs mem Sp (CB 4 jc :: CB 16 jp :: map (fun v => C4 (Z_to_bv 64 v)) vs ++ sv0) ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12cc0) mem (YK11.seg_rom (ms_segs B))) md) Post.
Proof.
  intros fx' L A regs mem md mm vs jc jp Hfrm FR Hres R2 R3 R4 R8 R26 R27 Hmm Hl Hvs HC.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5 & B6). pose proof YM05.alloc_ceiling_value as Hac.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & _).
  destruct vs as [|v0 [|v1 [|v2 [|v3 [|v4 [|v5 vs']]]]]]; cbn [length] in Hl; try discriminate.
  apply Forall_cons_iff in Hvs as [Hv0 Hvs]. apply Forall_cons_iff in Hvs as [Hv1 Hvs].
  apply Forall_cons_iff in Hvs as [Hv2 Hvs]. apply Forall_cons_iff in Hvs as [Hv3 Hvs].
  apply Forall_cons_iff in Hvs as [Hv4 _].
  cbn [map app] in HC.
  pose proof (fun H => f_norm L A mem md _ FR H HC) as HCn.
  specialize (HCn ltac:(cbn [cells_size csize LW.lsv Nat.add]; lia)).
  pose proof (f_stk L A mem md FR) as STn.
  rewrite SEGS.
  eapply (g_run_cf B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx' regs (Z_to_bv 64 0x12cc0) mem md L A).
  - exact FR.
  - lia.
  - lia.
  - unfold Regs6ss.mkR_of. rewrite R2, R3, R4, R8, R26, R27.
    eapply (LW.sx_evt CC); [| | | | exact Hmm | exact Hv0 | exact Hv1 | exact Hv2 | exact Hv3 | exact Hv4
      | exact (mem_inv_normalize rsegs mem) | exact STn | exact HCn]; lia.
  - intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM).
    do 5 eexists. exists [(Sx - stk, Sp + 128)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply LW.en_out1 in NO. lia.
  - intros R F pc' fc m0' HQ regs' m' Hx Hrel FR'.
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m'' &
      HE & _ & _).
    injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
    apply (SRcf_ret B).
    assert (G10 : YK11.getr regs' 10 = Z_to_bv 64 0) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
    assert (RP : regs_preserved regs0 regs').
    { intros r Hr. rewrite (lf_getr_eqv _ _ _ Hx).
      destruct (LW.lf_callee_cases r Hr) as [-> | Hr'].
      - cbn. replace (spZ regs0 - 128 + 128) with (spZ regs0) by lia. unfold spZ.
        apply Z_to_bv_bv_unsigned.
      - repeat (destruct Hr' as [-> | Hr']; [reflexivity|]). subst. reflexivity. }
    destruct (lf_post B API SINK stk empty L0 A0 regs0 mem0 md0 ra p n L A regs' m' md Hpre Hsn FR' G10 RP)
      as (Hpost & Hsn' & Hpay & MI2).
    exists (mkFP (@fp_regs fx') (@fp_csr fx')), L, A, regs', m', md.
    assert (E1 : YK11.getr regs0 1 = reg_get regs0 1) by reflexivity.
    split; [rewrite SEGS, <- E1, Hra1, (lf_ret_pc _ Hra); reflexivity|].
    split; [exact Hfrm|]. split; [exact Hpost|]. split; [exact Hsn'|].
    split; [exact Hres|]. split; [exact Hpay|]. split; [exact MI2 | exact I].
Qed.

Lemma map_c4_size : forall vs, cells_size (map (fun v => C4 (Z_to_bv 64 v)) vs) = (4 * length vs)%nat.
Proof. induction vs as [|v vs IH]; cbn [map cells_size csize length]; [reflexivity | rewrite IH; lia]. Qed.

Lemma hcells_size : forall jc jp vs jv, (length vs <= 5)%nat -> cells_size (LW.hcells jc jp vs jv sv0) = 128%nat.
Proof.
  intros jc jp vs jv Hl. unfold LW.hcells. cbn [cells_size csize]. rewrite cells_size_app, map_c4_size.
  cbn [cells_size csize LW.lsv]. lia.
Qed.

(* the loop head 0x12bf4 at the SRcf level *)
Definition LH (i : nat) (fx' : YK11.FPState) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) : Prop :=
  exists mm at0 vs jc jp jv,
    frm_zero (@fp_csr fx') /\ lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md /\ res_ok_slots A b /\
    YK11.getr regs 2 = Z_to_bv 64 Sp /\ YK11.getr regs 3 = YK11.getr regs0 3 /\
    YK11.getr regs 4 = YK11.getr regs0 4 /\ YK11.getr regs 8 = Z_to_bv 64 mm /\ YK11.getr regs 9 = Z_to_bv 64 n /\
    YK11.getr regs 18 = Z_to_bv 64 P' /\ YK11.getr regs 21 = Z_to_bv 64 (Z.of_nat i) /\
    YK11.getr regs 22 = Z_to_bv 64 at0 /\ YK11.getr regs 23 = Z_to_bv 64 (LW.nzb P') /\
    YK11.getr regs 24 = Z_to_bv 64 (Sp + 20) /\ YK11.getr regs 25 = Z_to_bv 64 5 /\
    YK11.getr regs 26 = YK11.getr regs0 26 /\ YK11.getr regs 27 = YK11.getr regs0 27 /\
    (mm = 1984 \/ mm = 16320) /\ 0 <= at0 <= n /\ length vs = i /\ (i < 5)%nat /\
    Forall (fun v => INT_MIN <= v <= INT_MAX) vs /\
    rw_cells rsegs mem Sp (LW.hcells jc jp vs jv sv0).

Lemma pres_get : forall r1 r2 (k : Z) v, regs_preserved r1 r2 -> callee_saved k ->
  YK11.getr r1 (Z_to_bv 5 k) = v -> YK11.getr r2 (Z_to_bv 5 k) = v.
Proof. intros r1 r2 k v Hp1 Hk1 E. rewrite (Hp1 k Hk1). exact E. Qed.

Ltac cs := unfold callee_saved; lia.

(* reg_get facts of a machine state carried to the config registers it is equivalent to *)
Ltac xr Hx Rk E := lazymatch type of Rk with reg_get _ ?k = ?v => lazymatch type of Hx with Regs6ss.xregs_eqv _ ?r' =>
  assert (E : reg_get r' k = v) by (rewrite <- (Hx k eq_refl); exact Rk) end end.
(* a callee-saved register across a call *)
Tactic Notation "pz" constr(Hrp) constr(E) constr(kz) ident(E') :=
  lazymatch type of E with _ ?r1 _ = ?v => lazymatch type of Hrp with regs_preserved r1 ?r2 =>
  assert (E' : YK11.getr r2 (Z_to_bv 5 kz) = v) by (rewrite (Hrp kz ltac:(cs)); exact E) end end.

(* the reply slice data[at, at + n) as the two calls see it *)
Lemma f_slice : forall L A mem md at1 nsl, lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md ->
  0 <= at1 -> 0 <= nsl -> at1 + nsl <= n ->
  blk_data B mem (at1 + P') (firstn (Z.to_nat nsl) (skipn (Z.to_nat at1) pl)) /\
  (0 < nsl -> in_block L A (at1 + P') nsl) /\
  Z.of_nat (length (firstn (Z.to_nat nsl) (skipn (Z.to_nat at1) pl))) = nsl.
Proof.
  intros L A mem md at1 nsl FR H1 H2 H3.
  split; [|split].
  - destruct (Z.eq_dec nsl 0) as [Z0|Z0].
    + rewrite Z0. cbn [Z.to_nat firstn]. apply blk_data_nil.
    + destruct (f_blk L A mem md FR ltac:(lia)) as (_ & BD). rewrite Z.add_comm.
      apply LW.blk_slice; [exact BD | lia | lia | lia].
  - intros Hs0. destruct (f_blk L A mem md FR ltac:(lia)) as (Hin & _). exists P', n. split; [exact Hin | lia].
  - rewrite firstn_length_le; [lia|]. rewrite length_skipn. lia.
Qed.

Lemma room_cno_cf : forall nsl, 0 <= nsl <= 255 -> cno_room_cf b nsl.
Proof. intros nsl Hs. destruct Hroom as (R1 & R2 & R3). unfold cno_room_cf. lia. Qed.

Lemma room_cv_cf : forall nsl, 0 <= nsl <= 255 -> cv_room_cf b nsl.
Proof. intros nsl Hs. destruct Hroom as (R1 & R2 & R3). unfold cv_room_cf. lia. Qed.

Lemma sr_step_cf : forall i fx' L A regs mem md, LH i fx' L A regs mem md ->
  (forall fx'' L' A' regs' mem' md', LH (S i) fx'' L' A' regs' mem' md' ->
     SRcf B (mkCfg (@YK11.mkst fx'' regs' (Z_to_bv 64 0x12bf4) mem' (YK11.seg_rom (ms_segs B))) md') Post) ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12bf4) mem (YK11.seg_rom (ms_segs B))) md) Post.
Proof.
  intros i fx' L A regs mem md (mm & at0 & vs & jc & jp & jv & Hfrm & FR & Hres & G2 & G3 & G4 & G8 & G9 & G18 &
    G21 & G22 & G23 & G24 & G25 & G26 & G27 & Hmm & Hat & Hl & Hi & Hvs & HC) IH.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5 & B6). pose proof YM05.alloc_ceiling_value as Hac.
  pose proof f_p'range as HP'.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & _).
  pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI).
  assert (HPB : 0 < n -> bytes_at rsegs (normalize rsegs mem) P' pl).
  { intros Hn0. destruct (f_blk L A mem md FR Hn0) as (_ & BD). destruct (f_pay Hn0) as (_ & P1 & P2 & _).
    apply bytes_at_normalize; [exact MI|]. apply (LW.blk_bytes_at B); [exact SEGS | lia | lia | exact BD]. }
  assert (HP0 : 0 < n -> 4096 <= P' /\ P' + n <= Sp).
  { intros Hn0. destruct (f_pay Hn0) as (_ & P1 & P2 & _). lia. }
  pose proof (fun H => f_norm L A mem md _ FR H HC) as HCn.
  specialize (HCn ltac:(rewrite hcells_size by lia; lia)).
  assert (E2 : reg_get regs 2 = Z_to_bv 64 Sp) by exact G2.
  assert (E9 : reg_get regs 9 = Z_to_bv 64 n) by exact G9.
  assert (E18 : reg_get regs 18 = Z_to_bv 64 P') by exact G18.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 at0) by exact G22.
  assert (E23 : reg_get regs 23 = Z_to_bv 64 (LW.nzb P')) by exact G23.
  rewrite SEGS.
  eapply (g_run_cf B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx' regs (Z_to_bv 64 0x12bf4) mem md L A).
  { exact FR. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. rewrite E2, E9, E18, E22, E23.
    unfold LW.hcells in HCn.
    eapply LW.sa_evt with (pl := pl); [lia | lia | exact Hlen | lia | exact HP' | exact HPB | exact HP0 | lia
      | exact HCn | exact (munch_refl _ _) | exact (wmono_refl _ _)]. }
  { intros ms (R & m' & jc' & at1 & nsl & cur & -> & R1 & R2 & R3 & R4 & R8 & R9 & R10 & R11 & R12 & R18 & R19 & R20 &
      R21 & R22 & R23 & R24 & R25 & R26 & R27 & Hcur & Hat1 & Hnsl & Hsum & MU & WM & FRc).
    do 5 eexists. exists [(Sp, Sp + 128)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply LW.en_out1 in NO. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx1 Hrel1 FR1.
  destruct HQ as (R' & m'' & jc' & at1 & nsl & cur & HE & R1 & R2 & R3 & R4 & R8 & R9 & R10 & R11 & R12 & R18 & R19 &
    R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & Hcur & Hat1 & Hnsl & Hsum & MU & WM & FRc).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  xr Hx1 R1 F1. xr Hx1 R2 F2. xr Hx1 R3 F3. xr Hx1 R4 F4. xr Hx1 R8 F8. xr Hx1 R9 F9. xr Hx1 R10 F10.
  xr Hx1 R11 F11. xr Hx1 R12 F12. xr Hx1 R18 F18. xr Hx1 R19 F19. xr Hx1 R20 F20. xr Hx1 R21 F21. xr Hx1 R22 F22.
  xr Hx1 R23 F23. xr Hx1 R24 F24. xr Hx1 R25 F25. xr Hx1 R26 F26. xr Hx1 R27 F27.
  clear R1 R2 R3 R4 R8 R9 R10 R11 R12 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27.
  pose proof (lf_rw_cells_rel m1 m0' _ _ Hrel1 FRc) as FC1. clear FRc.
  fold (LW.hcells jc' jp vs jv sv0) in FC1.
  assert (G2' : YK11.getr regs1 2 = Z_to_bv 64 Sp) by exact F2.
  assert (Hsp1 : spZ regs1 = Sp) by (unfold spZ at 1; rewrite G2'; apply MState.unsigned_lit; lia).
  destruct (f_slice L A m1 md at1 nsl FR1 ltac:(lia) ltac:(lia) ltac:(lia)) as (BD1 & IB1 & Hbs).
  set (bs := firstn (Z.to_nat nsl) (skipn (Z.to_nat at1) pl)) in *.
  assert (H1 : YK11.getr regs1 1 = Z_to_bv 64 0x12c98) by exact F1.
  rewrite <- SEGS. change (Z_to_bv 64 77140) with (Z_to_bv 64 CHECK_NO_OVERREAD).
  eapply (g_cno_cf B API SEGS AX ERRNO_LOW stk Sx L0 A0 mem0 md0 _ regs1 m1 md L A (at1 + P') nsl cur bs b).
  { exact CNO. } { exact FR1. } { lia. } { lia. }
  { rewrite H1. apply ret_ok_even. reflexivity. }
  { rewrite Hsp1. replace (Sx - 128) with (Sx + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact B3. }
  { rewrite Hsp1. unfold CNO_STACK, CNO_FRAME, ALLOC_STACK. lia. }
  { lia. } { lia. }
  { change (YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)). rewrite <- Htp0. exact (eq_trans F4 G4). }
  { exact F10. } { exact F11. } { exact F12. } { exact Hcur. }
  { unfold REPLY_MAX. lia. } { exact Hbs. } { exact BD1. } { exact IB1. } { exact Hfrm. } { exact Hres. }
  { apply room_cno_cf. lia. }
  intros fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp2 Eb2 Hres2 Hab2.
  rewrite H1.
  rewrite SEGS in Hab2.
  assert (FC2 : rw_cells rsegs mem2 Sp (LW.hcells jc' jp vs jv sv0)).
  { apply (LW.lf_rw_cells_frame m1); [exact FC1|]. intros a Ha. rewrite hcells_size in Ha by lia.
    apply Hab2. lia. }
  pz Hrp2 F2 2 P2. pz Hrp2 F3 3 P3. pz Hrp2 F4 4 P4. pz Hrp2 F8 8 P8. pz Hrp2 F9 9 P9. pz Hrp2 F18 18 P18.
  pz Hrp2 F19 19 P19. pz Hrp2 F20 20 P20. pz Hrp2 F21 21 P21. pz Hrp2 F22 22 P22. pz Hrp2 F23 23 P23.
  pz Hrp2 F24 24 P24. pz Hrp2 F25 25 P25. pz Hrp2 F26 26 P26. pz Hrp2 F27 27 P27.
  (* 0x12c98-0x12ca4 *)
  pose proof (fun H => f_norm L2 A2 mem2 md2 _ FR2 H FC2) as FC2n.
  specialize (FC2n ltac:(rewrite hcells_size by lia; lia)).
  assert (E2' : reg_get regs2 2 = Z_to_bv 64 Sp) by exact P2.
  rewrite SEGS.
  eapply (g_run_cf B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx2 regs2 (Z_to_bv 64 0x12c98) mem2 md2 L2 A2).
  { exact FR2. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. rewrite E2'. eapply LW.sb_evt. exact FC2n. }
  { intros ms (cur' & Hcur' & ->). do 5 eexists. exists (@nil (Z * Z)).
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    intros x Hx NO. exfalso. apply NO. exact I. }
  intros Rb Fb pcb fcb m0'' HQ regs3 m3 Hx3 Hrel3 FR3.
  destruct HQ as (cur' & Hcur' & HE). injection HE as ER EF EP EC EM. subst Rb Fb pcb fcb m0''.
  assert (Q1 : YK11.getr regs3 1 = Z_to_bv 64 0x12ca8) by (rewrite (lf_getr_eqv _ _ _ Hx3); reflexivity).
  assert (Q10 : YK11.getr regs3 10 = Z_to_bv 64 (at1 + P'))
    by (rewrite (lf_getr_eqv _ _ _ Hx3); exact P20).
  assert (Q11 : YK11.getr regs3 11 = Z_to_bv 64 nsl) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact P19).
  assert (Q12 : YK11.getr regs3 12 = Z_to_bv 64 cur') by (rewrite (lf_getr_eqv _ _ _ Hx3); reflexivity).
  assert (Q2 : YK11.getr regs3 2 = Z_to_bv 64 Sp) by (rewrite (lf_getr_eqv _ _ _ Hx3); reflexivity).
  assert (Q3 : YK11.getr regs3 3 = YK11.getr regs0 3)
    by (rewrite (lf_getr_eqv _ _ _ Hx3); exact (eq_trans P3 G3)).
  assert (Q4 : YK11.getr regs3 4 = YK11.getr regs0 4)
    by (rewrite (lf_getr_eqv _ _ _ Hx3); exact (eq_trans P4 G4)).
  assert (Q8 : YK11.getr regs3 8 = Z_to_bv 64 mm)
    by (rewrite (lf_getr_eqv _ _ _ Hx3); exact (eq_trans P8 G8)).
  assert (Q9 : YK11.getr regs3 9 = Z_to_bv 64 n) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact P9).
  assert (Q18 : YK11.getr regs3 18 = Z_to_bv 64 P') by (rewrite (lf_getr_eqv _ _ _ Hx3); exact P18).
  assert (Q19 : YK11.getr regs3 19 = Z_to_bv 64 nsl) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact P19).
  assert (Q21 : YK11.getr regs3 21 = Z_to_bv 64 (Z.of_nat i))
    by (rewrite (lf_getr_eqv _ _ _ Hx3); exact (eq_trans P21 G21)).
  assert (Q22 : YK11.getr regs3 22 = Z_to_bv 64 at1) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact P22).
  assert (Q23 : YK11.getr regs3 23 = Z_to_bv 64 (LW.nzb P')) by (rewrite (lf_getr_eqv _ _ _ Hx3); exact P23).
  assert (Q24 : YK11.getr regs3 24 = Z_to_bv 64 (Sp + 20))
    by (rewrite (lf_getr_eqv _ _ _ Hx3); exact (eq_trans P24 G24)).
  assert (Q25 : YK11.getr regs3 25 = Z_to_bv 64 5)
    by (rewrite (lf_getr_eqv _ _ _ Hx3); exact (eq_trans P25 G25)).
  assert (Q26 : YK11.getr regs3 26 = YK11.getr regs0 26)
    by (rewrite (lf_getr_eqv _ _ _ Hx3); exact (eq_trans P26 G26)).
  assert (Q27 : YK11.getr regs3 27 = YK11.getr regs0 27)
    by (rewrite (lf_getr_eqv _ _ _ Hx3); exact (eq_trans P27 G27)).
  pose proof (lf_rw_cells_rel m3 _ _ _ Hrel3 FC2n) as FC3.
  assert (Hsp3 : spZ regs3 = Sp) by (unfold spZ at 1; rewrite Q2; apply MState.unsigned_lit; lia).
  destruct (f_slice L2 A2 m3 md2 at1 nsl FR3 ltac:(lia) ltac:(lia) ltac:(lia)) as (BD3 & IB3 & _).
  fold bs in BD3, IB3.
  rewrite <- SEGS. change (Z_to_bv 64 77384) with (Z_to_bv 64 CHECK_VALUE).
  eapply (g_cv_cf B API SEGS AX ERRNO_LOW stk Sx L0 A0 mem0 md0 _ regs3 m3 md2 L2 A2 (at1 + P') nsl cur' bs b).
  { exact CV. } { exact FR3. } { lia. } { lia. }
  { rewrite Q1. apply ret_ok_even. reflexivity. }
  { rewrite Hsp3. replace (Sx - 128) with (Sx + (-8) * 16) by lia. rewrite Z.mod_add by lia. exact B3. }
  { rewrite Hsp3. unfold CV_STACK, CV_FRAME, ALLOC_STACK. lia. }
  { lia. } { lia. }
  { rewrite Q4. exact Htp0. }
  { exact Q10. } { exact Q11. } { exact Q12. } { exact Hcur'. }
  { unfold REPLY_MAX. lia. } { exact Hbs. } { exact BD3. } { exact IB3. } { exact Hfrm2. } { exact Hres2. }
  { apply room_cv_cf. lia. }
  intros fx4 L4 A4 regs4 mem4 md4 Hfrm4 FR4 Hrp4 G410 Eb4 Hres4 Hab4.
  rewrite Q1.
  rewrite SEGS in Hab4.
  assert (FC4 : rw_cells rsegs mem4 Sp (LW.hcells jc' jp vs jv sv0)).
  { apply (LW.lf_rw_cells_frame m3); [exact FC3|]. intros a Ha. rewrite hcells_size in Ha by lia.
    apply Hab4. lia. }
  pz Hrp4 Q2 2 S2. pz Hrp4 Q3 3 S3. pz Hrp4 Q4 4 S4. pz Hrp4 Q8 8 S8. pz Hrp4 Q9 9 S9. pz Hrp4 Q18 18 S18.
  pz Hrp4 Q19 19 S19. pz Hrp4 Q21 21 S21. pz Hrp4 Q22 22 S22. pz Hrp4 Q23 23 S23. pz Hrp4 Q24 24 S24.
  pz Hrp4 Q25 25 S25. pz Hrp4 Q26 26 S26. pz Hrp4 Q27 27 S27.
  assert (T2 : reg_get regs4 2 = Z_to_bv 64 Sp) by exact S2.
  assert (T3 : reg_get regs4 3 = YK11.getr regs0 3) by exact S3.
  assert (T4 : reg_get regs4 4 = YK11.getr regs0 4) by exact S4.
  assert (T8 : reg_get regs4 8 = Z_to_bv 64 mm) by exact S8.
  assert (T9 : reg_get regs4 9 = Z_to_bv 64 n) by exact S9.
  assert (T10 : reg_get regs4 10 = Z_to_bv 64 (rp_uci_int_m (zbytes bs) cur')) by exact G410.
  assert (T18 : reg_get regs4 18 = Z_to_bv 64 P') by exact S18.
  assert (T19 : reg_get regs4 19 = Z_to_bv 64 nsl) by exact S19.
  assert (T21 : reg_get regs4 21 = Z_to_bv 64 (Z.of_nat i)) by exact S21.
  assert (T22 : reg_get regs4 22 = Z_to_bv 64 at1) by exact S22.
  assert (T23 : reg_get regs4 23 = Z_to_bv 64 (LW.nzb P')) by exact S23.
  assert (T24 : reg_get regs4 24 = Z_to_bv 64 (Sp + 20)) by exact S24.
  assert (T25 : reg_get regs4 25 = Z_to_bv 64 5) by exact S25.
  assert (T26 : reg_get regs4 26 = YK11.getr regs0 26) by exact S26.
  assert (T27 : reg_get regs4 27 = YK11.getr regs0 27) by exact S27.
  pose proof (rp_uci_int_range (zbytes bs) cur' Hcur') as Hv.
  pose proof (fun H => f_norm L4 A4 mem4 md4 _ FR4 H FC4) as FC4n.
  specialize (FC4n ltac:(rewrite hcells_size by lia; lia)).
  subst i.
  (* 0x12ca8-0x12cbc *)
  rewrite SEGS.
  eapply (g_run_cf B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx4 regs4 (Z_to_bv 64 0x12ca8) mem4 md4 L4 A4).
  { exact FR4. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. rewrite T2, T3, T4, T8, T9, T10, T18, T19, T21, T22, T23, T24, T25, T26, T27.
    eapply LW.sc_evt; [lia | lia | exact Hmm | lia | lia | lia | exact Hv | exact Hvs | exact Hi | exact FC4n]. }
  { intros ms [(Rq & m' & mm' & at0' & vs' & jc'' & jp' & jv' & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & _ & _ & _ & _ & _ & MUq & WMq & _)
      | (Rq & m' & mm' & vs' & jc'' & jp' & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & MUq & WMq & _)].
    - do 5 eexists. exists [(Sp, Sp + 128)].
      split; [reflexivity|]. split; [exact MUq|]. split; [exact WMq|].
      intros x Hx NO. left. apply LW.en_out1 in NO. lia.
    - do 5 eexists. exists [(Sp, Sp + 128)].
      split; [reflexivity|]. split; [exact MUq|]. split; [exact WMq|].
      intros x Hx NO. left. apply LW.en_out1 in NO. lia. }
  intros Rc Fc pcc fcc m0c HQ regs5 m5 Hx5 Hrel5 FR5.
  destruct HQ as [(Rq & m'' & mm' & at0' & vs' & jc'' & jp' & jv' & HE & V2 & V3 & V4 & V8 & V9 & V18 & V21 & V22 &
      V23 & V24 & V25 & V26 & V27 & Hmm' & Hat' & Hlv & Hi' & Hvs' & _ & _ & FRc)
    | (Rq & m'' & mm' & vs' & jc'' & jp' & HE & V2 & V3 & V4 & V8 & V26 & V27 & Hmm' & Hlv & Hvs' & _ & _ & FRc)].
  - injection HE as ER EF EP EC EM. subst Rq Fc pcc fcc m''.
    pose proof (lf_rw_cells_rel m5 _ _ _ Hrel5 FRc) as FC5.
    rewrite <- SEGS. apply (IH (mkFP (@fp_regs fx4) (@fp_csr fx4)) L4 A4 regs5 m5 md4).
    exists mm', at0', vs', jc'', jp', jv'.
    split; [exact Hfrm4|]. split; [exact FR5|]. split; [exact Hres4|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V2|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V3|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V4|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V8|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V9|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V18|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V21|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V22|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V23|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V24|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V25|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V26|].
    split; [rewrite (lf_getr_eqv _ _ _ Hx5); exact V27|].
    split; [exact Hmm'|]. split; [exact Hat'|]. split; [exact Hlv|]. split; [exact Hi'|].
    split; [exact Hvs' | exact FC5].
  - injection HE as ER EF EP EC EM. subst Rq Fc pcc fcc m''.
    pose proof (lf_rw_cells_rel m5 _ _ _ Hrel5 FRc) as FC5.
    rewrite <- SEGS.
    xr Hx5 V2 W2. xr Hx5 V3 W3. xr Hx5 V4 W4. xr Hx5 V8 W8. xr Hx5 V26 W26. xr Hx5 V27 W27.
    apply (sr_exit_cf (mkFP (@fp_regs fx4) (@fp_csr fx4)) L4 A4 regs5 m5 md4 mm' vs' jc'' jp'); try assumption.
Qed.


Lemma sr_loop_cf : forall k i fx' L A regs mem md, k = (5 - i)%nat -> LH i fx' L A regs mem md ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12bf4) mem (YK11.seg_rom (ms_segs B))) md) Post.
Proof.
  induction k as [|k IHk]; intros i fx' L A regs mem md Hk5 HL.
  - exfalso. destruct HL as (mm & at0 & vs & jc & jp & jv & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & Hi & _ & _). lia.
  - apply (sr_step_cf i fx' L A regs mem md HL). intros fx'' L' A' regs' mem' md' HL'.
    apply (IHk (S i) fx'' L' A' regs' mem' md'); [lia | exact HL'].
Qed.

Hypothesis Hres0 : res_ok_slots A0 b.

(* 0x12b68: the prologue and the first loop head *)
Lemma sr_entry_cf : frm_zero (@fp_csr fx) ->
  SRcf B (mkCfg (@YK11.mkst fx regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 (YK11.seg_rom (ms_segs B))) md0) Post.
Proof.
  intros Hfrm.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5 & B6). pose proof YM05.alloc_ceiling_value as Hac.
  pose proof f_p'range as HP'.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & Herr0 & Hp0 & Hn11 &
    Hpl0 & Hrod0).
  pose proof (lf_fr_init B API stk empty L0 A0 regs0 mem0 md0 ra p n Hpre Hro) as FR0.
  assert (Esp : Sx = bv_unsigned (reg_get regs0 2)) by reflexivity.
  assert (E10 : reg_get regs0 10 = Z_to_bv 64 P') by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (E11 : reg_get regs0 11 = Z_to_bv 64 n) by exact Hn11.
  assert (ST0 : Frame.stk rsegs (normalize rsegs mem0) (Sx - stk) (bv_unsigned (reg_get regs0 2))).
  { rewrite <- Esp. apply lf_stk; [lia | lia |].
    intros a Ha. unfold writable_at.
    assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
    rewrite (wview_rel_rw rsegs mem0 (normalize rsegs mem0) _ (mem_rel_normalize rsegs mem0 Hro)
               (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
    rewrite <- SEGS. exact (Hstw0 a Ha). }
  assert (HPB : 0 < n -> bytes_at rsegs (normalize rsegs mem0) P' pl).
  { intros Hn0. destruct (f_pay Hn0) as (_ & P1 & P2 & E). rewrite E in *.
    apply bytes_at_normalize; [exact Hro|]. apply (LW.blk_bytes_at B); [exact SEGS | lia | lia | exact Hpd]. }
  rewrite SEGS.
  eapply (g_run_cf B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 md0 L0 A0).
  { exact FR0. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of, LLVM_ENTRY. rewrite E10, E11.
    eapply LW.e0_evt with (pl := pl).
    - exact ST0.
    - rewrite <- Esp. lia.
    - exact (mem_inv_normalize rsegs mem0).
    - rewrite <- Esp. lia.
    - lia.
    - exact HP'.
    - exact Hlen.
    - exact HPB.
    - intros Hn0. destruct (f_pay Hn0) as (_ & P1 & P2 & _). lia.
    - intros Hn0. destruct (f_pay Hn0) as (_ & P1 & P2 & _). lia. }
  { intros ms (R & m' & mm & at0 & vs & jc & jp & jv & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & MU & WM & _).
    do 5 eexists. exists [(bv_unsigned (reg_get regs0 2) - 128, bv_unsigned (reg_get regs0 2))].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply LW.en_out1 in NO. rewrite <- Esp in NO. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx1 Hrel1 FR1.
  destruct HQ as (R' & m'' & mm & at0 & vs & jc & jp & jv & HE & V2 & V3 & V4 & V8 & V9 & V18 & V21 & V22 & V23 &
    V24 & V25 & V26 & V27 & Hmm & Hat & Hlv & Hi & Hvs & _ & _ & FRc).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  pose proof (lf_rw_cells_rel m1 _ _ _ Hrel1 FRc) as FC1.
  rewrite <- Esp in V2, V24, FC1.
  rewrite <- SEGS.
  apply (sr_loop_cf 5 0 (mkFP (@fp_regs fx) (@fp_csr fx)) L0 A0 regs1 m1 md0 eq_refl).
  exists mm, at0, vs, jc, jp, jv.
  split; [exact Hfrm|]. split; [exact FR1|]. split; [exact Hres0|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V2|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V3|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V4|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V8|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V9|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V18|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V21|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V22|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V23|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V24|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V25|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V26|].
  split; [rewrite (lf_getr_eqv _ _ _ Hx1); exact V27|].
  split; [exact Hmm|]. split; [exact Hat|]. split; [exact Hlv|]. split; [exact Hi|].
  split; [exact Hvs | exact FC1].
Qed.

End Run.

(* decode's llvm_n_bound: the payload size is that of a live block, or 0 *)
Lemma llvm_n_bound : forall stk empty L A regs mem md ra p n,
  lib_pre B API stk empty L A regs mem md ra p n -> 0 <= n < 2 ^ 47.
Proof.
  intros stk empty L A regs mem md ra p n (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpl & _).
  pose proof YM05.alloc_ceiling_value as Hac.
  destruct Hpl as [[-> _] | [Hn (q & Hq & _)]]; [lia|].
  destruct (mr_blocks B _ (aa_laws API) L A mem md q n 0 HM Hq ltac:(lia)) as (_ & H1 & H2 & _). lia.
Qed.

Theorem LLVMFuzzerTestOneInput_holds_of_cf : LLVMFuzzerTestOneInput_sr_contract_cf B API.
Proof using ERRNO_LOW SINK CNO CV CC.
  intros BI j Hj ra empty stk Hk Hra L A regs mem md p n pl b Hpre Hn Hpl Hsn Hsp Hres Hroom Hro Hrelro HGI Hfrm.
  pose proof (llvm_n_bound stk empty L A regs mem md ra p n Hpre) as Hnb.
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn11 & _).
  destruct (Z_lt_le_dec n (2 ^ 26)) as [Hsmall|Hbig].
  2:{ apply (llvm_early_cf B API SINK j stk empty L A regs mem md ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm).
      rewrite Hn11. rewrite MState.unsigned_lit by lia. exact Hbig. }
  exact (sr_entry_cf stk empty L A regs mem md ra p n pl b j BI Hk Hra Hpre Hn Hpl Hsn Hsp Hroom Hro Hsmall Hres Hfrm).
Qed.

End M.
