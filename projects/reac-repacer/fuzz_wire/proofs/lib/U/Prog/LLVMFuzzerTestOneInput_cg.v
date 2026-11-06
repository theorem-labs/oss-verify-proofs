(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for reac-repacer/fuzz_wire: the cut-free (SRcf) walk of fuzz_wire's LLVMFuzzerTestOneInput on the UBSan image,
   against lib/U/Prog/LLVMFuzzerTestOneInput_cfb.v's LLVMFuzzerTestOneInput_sr_contract_cf:
   LLVMFuzzerTestOneInput_holds_of_cf, as libreac/fuzz_decode's released lib/U/Prog/LLVMFuzzerTestOneInput_cg.v (with
   its fd_*_cg files, 25e3d17bdb5) and reac-repacer/fuzz_uci's (ddb6d58bbed) are to their U walks. Sections G and M
   are lib/U/Prog/LLVMFuzzerTestOneInput.v's with SR replaced by SRcf (SRcf_bind / SRcf_ret, llvm_run_norm_cf),
   malloc and free taken at the kit's agree contracts (malloc_contract_ag at room_ag, free_contract_cf), check_copy at
   its cf contract (check_copy_ccf.v, room cc_room_cf), the room of each from llvm_room_cf, and the early exit by
   llvm_early_cf; the instruction segments (e1_evt .. e6_evt, chk_call), the frame cells and the list lemmas are that
   file's, used as they are (module LW). The same instructions are walked and the same branches refuted, for the
   reasons that file's header gives. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import memcpy_c check_forward_c check_ret_c
  check_downstream_c check_meter_c check_counter_c check_width_c check_read_c rp_copy_untag_c FuzzDup check_copy_c
  FrameBytes cc_segs cc_glue LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_early.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import LLVMFuzzerTestOneInput_cfb check_copy_ccf
  LLVMFuzzerTestOneInput_early_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require LLVMFuzzerTestOneInput.
Import ListNotations.
Open Scope Z_scope.

Module LW := OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog.LLVMFuzzerTestOneInput.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis HGG : ms_got_guard B = LLVM_GUARD_GOT.
Hypothesis HMAL : ms_malloc B = LLVM_MALLOC.
Hypothesis HFRE : ms_free B = LLVM_FREE.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract_ag fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract_cf fx' rc B API.

Lemma blk_keep : forall stk Sw L A mem md LX AXX memX mdX x bs,
  lf_fr B API stk Sw L A mem md LX AXX memX mdX -> In (x, Z.of_nat (length bs)) (blocks L A) ->
  blk_data B mem x bs -> blk_data B memX x bs.
Proof.
  intros stk Sw L A mem md LX AXX memX mdX x bs (_ & _ & _ & _ & _ & _ & _ & _ & Hbyt & _) Hin HD i Hi.
  rewrite (Hbyt x _ i Hin Hi). exact (HD i Hi).
Qed.

Lemma norm_stk : forall mem lo hi, ro_agree rsegs mem -> LF_RES_TOP <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at (ms_segs B) mem a) -> Frame.stk rsegs (normalize rsegs mem) lo hi.
Proof.
  intros mem lo hi Hro Hlo Hhi H. apply lf_stk; [exact Hlo | exact Hhi |]. intros a Ha.
  assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
  unfold writable_at. rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem Hro)
    (lf_ro_addr_out B a SEGS Hni ltac:(unfold LF_RES_TOP in Hlo; lia))).
  pose proof (H a Ha) as W. rewrite SEGS in W. exact W.
Qed.

Lemma norm_blk : forall L A mem md x n, aa_MR API L A mem md -> In (x, n) (blocks L A) -> 0 < n ->
  ro_agree rsegs mem -> exists junk, rw_cells rsegs (normalize rsegs mem) x [CB (Z.to_nat n) junk].
Proof.
  intros L A mem md x n HM Hin Hn Hro. pose proof Hin as Hin'. apply blocks_In in Hin' as (q & Hq & Hqin).
  pose proof (mr_blocks_range B _ (aa_laws API) L A mem md q n HM Hqin) as (R1 & R2). rewrite Hq in R1, R2.
  pose proof YM05.alloc_ceiling_value as Hac.
  assert (ST : Frame.stk rsegs (normalize rsegs mem) x (x + n)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    destruct (mr_blocks B _ (aa_laws API) L A mem md q n (a - x) HM Hqin ltac:(lia)) as ((v & Hv) & _).
    pose proof (ax_blocks_img AX L A mem md q n (a - x) HM Hqin ltac:(lia)) as Hni.
    rewrite Hq in Hv, Hni. replace (x + (a - x)) with a in Hv, Hni by lia.
    assert (E : normalize rsegs mem (Z_to_bv 64 a) = Some v).
    { rewrite (mem_rel_rw rsegs mem (normalize rsegs mem) (Z_to_bv 64 a) (mem_rel_normalize rsegs mem Hro)
        (lf_ro_addr_out B a SEGS Hni ltac:(lia))). exact Hv. }
    unfold wa. split.
    - unfold wview. rewrite E. discriminate.
    - exists v. unfold mrd. rewrite E. reflexivity. }
  destruct (stk_carve rsegs _ x (x + n) (Z.to_nat n) ST ltac:(rewrite Z2Nat.id by lia; lia)) as [_ [junk HR]].
  rewrite Z2Nat.id in HR by lia. replace (x + n - n) with x in HR by lia. exists junk. exact HR.
Qed.

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

(* g_above over check_copy's call_post_x *)
Lemma g_above_x : forall stk S L A regs mem md K gone L' A' regs' mem' md',
  aa_MR API L A mem md ->
  call_post_x B API K L A regs mem md gone L' A' regs' mem' md' ->
  YM05.alloc_ceiling + stk <= S -> S - stk <= spZ regs - K -> S <= 2 ^ 64 -> 0 <= K ->
  forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
    (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a).
Proof.
  intros stk S L A regs mem md K gone L' A' regs' mem' md' HM
    (HM2 & _ & _ & _ & _ & _ & _ & Hfr & _) H1 H2 H3 HK0 a Ha.
  pose proof YM05.alloc_ceiling_value as Hac.
  apply Hfr.
  - left. lia.
  - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM Ho). lia.
  - intros Ho. pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ a HM2 Ho). lia.
  - unfold scratch_k. intros [Hs|Hs]; [lia | pose proof (lf_errno_low B ERRNO_LOW a Hs); lia].
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

Lemma g_malloc_cf : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A n bres (P : config -> Prop),
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - ALLOC_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) -> YK11.getr regs 10 = Z_to_bv 64 n ->
  res_ok_slots A bres -> room_ag bres n ->
  (forall L' A' regs' mem' md' res,
     lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     YK11.getr regs' 10 = Z_to_bv 64 res -> 4096 <= res -> res + n <= YM05.alloc_ceiling -> res mod 16 = 0 ->
     (forall i, 0 <= i < n -> ~ in_img B (res + i)) ->
     (exists b1 b2, blocks L' A' = b1 ++ (res, n) :: b2 /\ blocks L A = b1 ++ b2) ->
     res_ok_slots A' (sb_malloc bres n) ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     blocks_kept B L A mem mem' (fun _ => False) ->
     SRcf B (mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 LLVM_MALLOC) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A n bres P FR Hc HS Hra Hal H1 H2 H63 Htp H10 Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  eapply (SRcf_bind B).
  { replace (Z_to_bv 64 LLVM_MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite HMAL; reflexivity).
    apply (MALLOC fx' L A regs mem md n bres).
    - apply call_pre_k_alloc. exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs ALLOC_STACK FR Hra Hal H1 H2
        ltac:(unfold ALLOC_STACK; lia) Hc H63 Htp).
    - rewrite SEGS. exact MI.
    - exact H10.
    - exact Hres.
    - exact Hroom. }
  intros c2 (L2 & A2 & regs2 & mem2 & md2 & res & -> & Hpost & G10 & Hres0 & Hal16 & (Hf1 & Hf2 & Hf3)
    & (b1 & b2 & Eb1 & Eb2) & Hkept & Hro2 & Hgk & Hub & Hidt & Hlen & Hres2).
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | unfold ALLOC_STACK in *; lia | lia | | | | | | exact Hidt | | ].
    - intros a Ha. exfalso. exact Ha.
    - intros a Ha. right. intros Hf. exact Hf.
    - intros a Hf Ha. exfalso. exact Hf.
    - intros a0 k0 Hin. pose proof (Hblk a0 k0 Hin) as Hin2. rewrite Eb2 in Hin2. rewrite Eb1.
      apply in_app_or in Hin2. apply in_or_app. destruct Hin2 as [Hin2|Hin2]; [left; exact Hin2 | right; right; exact Hin2].
    - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i (Hblk a0 k0 Hin) (fun H => H) Hi).
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K L2 A2 regs2 mem2 md2 res FR2 Hrp G10 ltac:(lia) ltac:(lia) Hal16 Hf3 (ex_intro _ b1 (ex_intro _ b2 (conj Eb1 Eb2)))
    Hres2).
  - apply (g_above stk S L A regs mem md ALLOC_STACK (fun _ => False) L2 A2 regs2 mem2 md2 HM).
    + apply call_post_k_alloc. exact Hpost.
    + exact Hc.
    + exact H1.
    + exact HS.
    + unfold ALLOC_STACK; lia.
    + intros a Ha. destruct Ha.
  - exact Hkept.
Qed.

Lemma g_free_cf : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A x n bres (P : config -> Prop),
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - ALLOC_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) -> YK11.getr regs 10 = Z_to_bv 64 x ->
  In (x, n) (blocks L A) -> 0 < n -> (forall a k, In (a, k) (blocks L0 A0) -> a + k <= x \/ x + n <= a) ->
  res_ok_slots A bres ->
  (forall L' A' regs' mem' md',
     lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     (exists b1 b2, blocks L A = b1 ++ (x, n) :: b2 /\ blocks L' A' = b1 ++ b2) ->
     res_ok_slots A' (sb_free bres n) ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     blocks_kept B L A mem mem' (fun a => a = x) ->
     SRcf B (mkCfg (@YK11.mkst fx' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 LLVM_FREE) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A x n bres P FR Hc HS Hra Hal H1 H2 H63 Htp H10 Hin Hn Hd Hres K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  pose proof YM05.alloc_ceiling_value as Hac.
  pose proof Hin as Hin'. apply blocks_In in Hin' as (q & Hq & Hqin).
  assert (Hfreed : forall a, x <= a < x + n -> a < YM05.alloc_ceiling /\ ~ in_img B a).
  { intros a Ha.
    destruct (mr_blocks B (aa_MR API) (aa_laws API) L A mem md q n (a - x) HM Hqin ltac:(lia)) as (_ & R1 & R2 & _).
    pose proof (ax_blocks_img AX L A mem md q n (a - x) HM Hqin ltac:(lia)) as Himgx.
    rewrite Hq in R1, R2, Himgx. replace (x + (a - x)) with a in Himgx by lia. split; [lia | exact Himgx]. }
  eapply (SRcf_bind B).
  { replace (Z_to_bv 64 LLVM_FREE) with (Z_to_bv 64 (ms_free B)) by (rewrite HFRE; reflexivity).
    apply (FREE fx' L A regs mem md q n bres).
    - apply call_pre_k_alloc. exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs ALLOC_STACK FR Hra Hal H1 H2
        ltac:(unfold ALLOC_STACK; lia) Hc H63 Htp).
    - rewrite SEGS. exact MI.
    - exact Hqin.
    - rewrite H10, Hq. reflexivity.
    - exact Hres. }
  intros c2 (L2 & A2 & regs2 & mem2 & md2 & -> & Hpost & (b1 & b2 & Eb1 & Eb2) & Hkept & Hro2 & Hgk & Hub & Hidt
    & Hlen & Hres2).
  apply call_post_k_alloc in Hpost.
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  rewrite Hq in Eb1, Hkept.
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | unfold ALLOC_STACK in *; lia | lia | | | | | | exact (Hidt HID) | | ].
    - intros a Ha. right. rewrite Hq in Ha. exact (Hfreed a Ha).
    - intros a Ha. right. intros Hf. rewrite Hq in Hf. destruct (Hfreed a Hf). lia.
    - intros a Hf Ha. rewrite Hq in Hf. destruct (Hfreed a Hf). lia.
    - intros a0 k0 Hin0. pose proof (Hblk a0 k0 Hin0) as Hin2. rewrite Eb1 in Hin2. rewrite Eb2.
      apply in_app_or in Hin2. apply in_or_app.
      destruct Hin2 as [Hin2|[Hin2|Hin2]]; [left; exact Hin2 | | right; exact Hin2].
      exfalso. injection Hin2 as E1 E2. subst a0 k0. destruct (Hd _ _ Hin0); lia.
    - intros a0 k0 i Hin0 Hi. apply (Hkept a0 k0 i (Hblk a0 k0 Hin0)); [|exact Hi].
      intros E. subst a0. destruct (Hd _ _ Hin0); lia.
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K L2 A2 regs2 mem2 md2 FR2 Hrp (ex_intro _ b1 (ex_intro _ b2 (conj Eb1 Eb2))) Hres2).
  - apply (g_above stk S L A regs mem md ALLOC_STACK (fun a => ptr_addr L q <= a < ptr_addr L q + n)
      L2 A2 regs2 mem2 md2 HM Hpost Hc H1 HS ltac:(unfold ALLOC_STACK; lia)).
    intros a Ha. rewrite Hq in Ha. exact (proj1 (Hfreed a Ha)).
  - exact Hkept.
Qed.

(* check_copy(c, f, n) at 0x13550 (fuzz_wire.c:275): its frame is the caller's frame below spZ regs; c is no entry
   block, so the entry blocks' bytes come from blocks_kept with the exception c *)
Lemma g_cc_cf : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A c f n kc bs bres
    (P : config -> Prop),
  (forall fx'' : YK11.FPState, @check_copy_contract_cf fx'' rc B API) ->
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - CC_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  YK11.getr regs 10 = Z_to_bv 64 c -> YK11.getr regs 11 = Z_to_bv 64 f -> YK11.getr regs 12 = Z_to_bv 64 n ->
  n <= 1600 -> Z.of_nat (length bs) = n -> In (c, kc) (blocks L A) -> n <= kc ->
  (exists qf kf, In (qf, kf) (blocks L A) /\ qf <> c /\ qf <= f /\ f + n <= qf + kf) ->
  Mem.bytes_at (ms_segs B) mem c bs -> Mem.bytes_at (ms_segs B) mem f bs ->
  (forall a k, In (a, k) (blocks L0 A0) -> a <> c) ->
  frm_zero (@fp_csr fx') -> res_ok_slots A bres -> cc_room_cf bres n ->
  (forall (fx'' : YK11.FPState) L' A' regs' mem' md',
     frm_zero (@fp_csr fx'') ->
     lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     YK11.getr regs' 10 = Z_to_bv 64 (copy_untag_result n bs) ->
     Mem.bytes_at (ms_segs B) mem' c (cu_bytes n bs) ->
     blocks L' A' = blocks L A -> res_ok_slots A' bres ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     SRcf B (mkCfg (@YK11.mkst fx'' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 CHECK_COPY) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A c f n kc bs bres P CC FR Hc HS Hra Hal H1 H2 H63 Htp
    G10 G11 G12 Hn Hlen Hinc Hkc Hinf BC BF Hnc Hfrm Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  eapply (SRcf_bind B).
  { apply (CC fx' L A regs mem md c f n kc bs bres SEGS).
    - exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs CC_STACK FR Hra Hal H1 H2
        ltac:(unfold CC_STACK, CHECK_COPY_FRAME, ALLOC_STACK; lia) Hc H63 Htp).
    - exact HID.
    - exact G10.
    - exact G11.
    - exact G12.
    - exact Hn.
    - exact Hlen.
    - exact Hinc.
    - exact Hkc.
    - exact Hinf.
    - exact BC.
    - exact BF.
    - rewrite SEGS. exact MI.
    - exact Hfrm.
    - exact Hres.
    - exact Hroom. }
  intros c2 (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & Hfrm2 & Hpost & G210 & BC2 & Eb & Hkept & Hgk & Hro2 & Hres2
    & Hidt).
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & _).
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call_x B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | unfold CC_STACK, CHECK_COPY_FRAME, ALLOC_STACK in *; lia | lia | | | exact Hidt | | ].
    - intros a0 k0 Hin. rewrite Eb. exact (Hblk a0 k0 Hin).
    - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i (Hblk a0 k0 Hin) (Hnc a0 k0 Hin) Hi).
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp G210 BC2 Eb Hres2).
  apply (g_above_x stk S L A regs mem md CC_STACK (fun a => a = c) L2 A2 regs2 mem2 md2 HM Hpost Hc H1 HS
    ltac:(unfold CC_STACK, CHECK_COPY_FRAME, ALLOC_STACK; lia)).
Qed.

End G.

(* that file's two tactics of the SR level (LW.sr_side / LW.cs) *)
Local Ltac sr_side Hsp1 Q1 := first [ lia
  | rewrite Hsp1; unfold CC_STACK, CHECK_COPY_FRAME, ALLOC_STACK; lia
  | rewrite Q1; apply ret_ok_even; reflexivity
  | rewrite Hsp1; Z.div_mod_to_equations; lia ].

Local Ltac cs := unfold callee_saved; lia.

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract_ag fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract_cf fx' rc B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis SINK : lf_sink_env B.
Hypothesis BND : blocks_nodup B API.
Hypothesis CT : ctx_owned B API.
Hypothesis MC : memcpy_contract.
Hypothesis CF : check_forward_contract.
Hypothesis CR : check_ret_contract.
Hypothesis CD : check_downstream_contract.
Hypothesis CM : check_meter_contract.
Hypothesis CN : check_counter_contract.
Hypothesis CW : check_width_contract.
Hypothesis CRD : check_read_contract.
Hypothesis CC : forall fx' : YK11.FPState, @check_copy_contract_cf fx' rc B API.

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
Hypothesis Hn : 1 <= n < 2 ^ 26.

Local Abbreviation Sx := (spZ regs0).
Local Abbreviation Sp := (spZ regs0 - 64).
Local Abbreviation nn := (LW.nclamp n).
Local Abbreviation n1 := (fuzz_dup_size (LW.nclamp n)).
Local Abbreviation sv0 := (LW.lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
  (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21) (reg_get regs0 22)).
Local Abbreviation Post := (llvm_sr_post B API stk L0 A0 regs0 mem0 md0 ra p n b j).

(* the registers the walk never writes and every callee keeps: gp, tp, s7..s11 *)
Definition kp (regs : bvmap 5 word) : Prop :=
  YK11.getr regs 3 = YK11.getr regs0 3 /\ YK11.getr regs 4 = YK11.getr regs0 4 /\
  YK11.getr regs 23 = YK11.getr regs0 23 /\ YK11.getr regs 24 = YK11.getr regs0 24 /\
  YK11.getr regs 25 = YK11.getr regs0 25 /\ YK11.getr regs 26 = YK11.getr regs0 26 /\
  YK11.getr regs 27 = YK11.getr regs0 27.

Lemma kp_pres : forall r r', kp r -> regs_preserved r r' -> kp r'.
Proof.
  intros r r' (H3 & H4 & H23 & H24 & H25 & H26 & H27) Hp.
  assert (X : forall k, callee_saved k -> YK11.getr r' (Z_to_bv 5 k) = YK11.getr r (Z_to_bv 5 k)) by exact Hp.
  split; [exact (eq_trans (X 3 ltac:(unfold callee_saved; lia)) H3)|].
  split; [exact (eq_trans (X 4 ltac:(unfold callee_saved; lia)) H4)|].
  split; [exact (eq_trans (X 23 ltac:(unfold callee_saved; lia)) H23)|].
  split; [exact (eq_trans (X 24 ltac:(unfold callee_saved; lia)) H24)|].
  split; [exact (eq_trans (X 25 ltac:(unfold callee_saved; lia)) H25)|].
  split; [exact (eq_trans (X 26 ltac:(unfold callee_saved; lia)) H26)|].
  exact (eq_trans (X 27 ltac:(unfold callee_saved; lia)) H27).
Qed.

Lemma f_bounds : 8304 <= stk /\ YM05.alloc_ceiling + stk <= Sx /\ Sx mod 16 = 0 /\ Sx <= 2 ^ 47 /\
  LF_RES_TOP < YM05.alloc_ceiling.
Proof.
  pose proof Hpre as (_ & _ & _ & _ & _ & Hal & Hceil & _).
  pose proof Hk as Hk'. unfold LLVM_K, LLVM_FRAME, CC_STACK, CHECK_COPY_FRAME, ALLOC_STACK in Hk'.
  pose proof lf_ceiling as Hrt.
  split; [lia|]. split; [exact Hceil|]. split; [exact Hal|]. split; [exact Hsp | exact Hrt].
Qed.

(* size >= 1: data is the driver's payload block, in [4096, alloc_ceiling) *)
Lemma f_pay : In (p, n) (blocks L0 A0) /\ 4096 <= p /\ p + n <= YM05.alloc_ceiling /\
  reg_get regs0 10 = Z_to_bv 64 p /\ reg_get regs0 11 = Z_to_bv 64 n.
Proof.
  pose proof Hpre as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & Hn1 & Hpl & _).
  destruct Hpl as [[E _] | [_ (q & Hq & Hqp)]]; [lia|].
  pose proof (mr_blocks_range B _ (aa_laws API) L0 A0 mem0 md0 q n HM Hq) as (R1 & R2). rewrite Hqp in R1, R2.
  split; [apply blocks_In; exists q; split; [exact Hqp | exact Hq]|]. split; [lia|]. split; [lia|].
  split; [exact Hp | exact Hn1].
Qed.

(* the payload is a live block of every later state, with its bytes *)
Lemma f_blk : forall L A mem md, lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md ->
  In (p, n) (blocks L A) /\ blk_data B mem p pl.
Proof.
  intros L A mem md (HM & _ & _ & _ & _ & _ & _ & Hblk & Hbyt & _).
  destruct f_pay as (Hin & H1 & H2 & _).
  split; [exact (Hblk _ _ Hin)|].
  intros i Hi. rewrite (Hbyt _ _ i Hin ltac:(lia)). exact (Hpd i Hi).
Qed.

Lemma f_norm : forall L A mem md cs, lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md ->
  (cells_size cs <= 64)%nat -> rw_cells rsegs mem Sp cs -> rw_cells rsegs (normalize rsegs mem) Sp cs.
Proof.
  intros L A mem md cs FR Hsz HC. pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI).
  pose proof BI as (SEGS & _).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5).
  apply (lf_rw_cells_norm B mem Sp cs SEGS MI); [|exact HC].
  intros i Hi Himg. pose proof (lf_in_img_top B _ SEGS Himg). pose proof (rw_cells_bound _ _ _ _ HC). lia.
Qed.

Lemma f_stk : forall L A mem md, lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md ->
  Frame.stk rsegs (normalize rsegs mem) (Sx - stk) Sp.
Proof.
  intros L A mem md FR. pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hstw & _ & _ & MI).
  pose proof BI as (SEGS & _).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5). pose proof YM05.alloc_ceiling_value as Hac.
  apply lf_stk; [lia | lia |]. intros a Ha. unfold writable_at.
  assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
  rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem MI)
             (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
  rewrite <- SEGS. exact (Hstw a ltac:(lia)).
Qed.

Lemma f_blk_range : forall L A mem md x k, lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md ->
  In (x, k) (blocks L A) -> 4096 <= x /\ x + k <= YM05.alloc_ceiling.
Proof.
  intros L A mem md x k (HM & _) Hin. apply blocks_In in Hin as (q & Hq & Hqin).
  pose proof (mr_blocks_range B _ (aa_laws API) L A mem md q k HM Hqin) as (R1 & R2). rewrite Hq in R1, R2. lia.
Qed.

(* 0x12f04: the return value 0, the epilogue and ret *)
Lemma sr_tail_cf : forall (fx' : YK11.FPState) L A regs mem md,
  frm_zero (@fp_csr fx') -> lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md -> res_ok_slots A b ->
  YK11.getr regs 2 = Z_to_bv 64 Sp -> kp regs -> rw_cells rsegs mem Sp sv0 ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12f04) mem (YK11.seg_rom (ms_segs B))) md) Post.
Proof.
  intros fx' L A regs mem md Hfrm FR Hres G2 (G3 & G4 & G23 & G24 & G25 & G26 & G27) HC.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5). pose proof YM05.alloc_ceiling_value as Hac.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & _).
  pose proof (f_norm L A mem md sv0 FR ltac:(cbn; lia) HC) as HCn.
  assert (E2 : reg_get regs 2 = Z_to_bv 64 Sp) by exact G2.
  assert (E3 : reg_get regs 3 = reg_get regs0 3) by exact G3.
  assert (E4 : reg_get regs 4 = reg_get regs0 4) by exact G4.
  assert (E23 : reg_get regs 23 = reg_get regs0 23) by exact G23.
  assert (E24 : reg_get regs 24 = reg_get regs0 24) by exact G24.
  assert (E25 : reg_get regs 25 = reg_get regs0 25) by exact G25.
  assert (E26 : reg_get regs 26 = reg_get regs0 26) by exact G26.
  assert (E27 : reg_get regs 27 = reg_get regs0 27) by exact G27.
  rewrite SEGS.
  eapply (g_run_cf B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx' regs (Z_to_bv 64 0x12f04) mem md L A).
  { exact FR. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. rewrite E2, E3, E4, E23, E24, E25, E26, E27.
    apply LW.e6_evt. rewrite unsigned_lit by lia. exact HCn. }
  { intros ms ->. do 5 eexists. exists (@nil (Z * Z)).
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    intros x Hx NO. exfalso. apply NO. exact I. }
  intros R F pc' fc m0' HQ regs' m' Hx Hrel FR'.
  injection HQ as ER EF EP EC EM. subst R F pc' fc m0'.
  apply (SRcf_ret B).
  assert (G10 : YK11.getr regs' 10 = Z_to_bv 64 0) by (rewrite (lf_getr_eqv _ _ _ Hx); reflexivity).
  assert (RP : regs_preserved regs0 regs').
  { intros r Hr. rewrite (lf_getr_eqv _ _ _ Hx).
    destruct (LW.lf_callee_cases r Hr) as [-> | Hr'].
    - transitivity (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (spZ regs0 - 64)) + 64)); [reflexivity|].
      rewrite unsigned_lit by lia. replace (spZ regs0 - 64 + 64) with (spZ regs0) by lia. unfold spZ.
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

(* 0x12efc: free(f) *)
Lemma sr_free2_cf : forall (fx' : YK11.FPState) L A regs mem md f,
  frm_zero (@fp_csr fx') -> lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md -> res_ok_slots A (sb_malloc b n1) ->
  In (f, n1) (blocks L A) -> (forall a k, In (a, k) (blocks L0 A0) -> a + k <= f \/ f + n1 <= a) ->
  YK11.getr regs 2 = Z_to_bv 64 Sp -> kp regs -> YK11.getr regs 8 = Z_to_bv 64 f -> rw_cells rsegs mem Sp sv0 ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12efc) mem (YK11.seg_rom (ms_segs B))) md) Post.
Proof.
  intros fx' L A regs mem md f Hfrm FR Hres Hin Hd G2 KP G8 HC.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5). pose proof YM05.alloc_ceiling_value as Hac.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & _).
  pose proof FR as (HM & _).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof (fuzz_dup_size_range nn ltac:(unfold LW.nclamp; lia)) as [D1 D2].
  assert (E8 : reg_get regs 8 = Z_to_bv 64 f) by exact G8.
  rewrite SEGS.
  apply (llvm_run_cf B SEGS fx' regs (Z_to_bv 64 0x12efc) mem md
    (fun ms => exists R, ms = MS R (@fp_regs fx') (Z_to_bv 64 0x14758) (@fp_csr fx') None mem (YK11.seg_rom rsegs) /\
       reg_get R 1 = Z_to_bv 64 0x12f04 /\ reg_get R 10 = Z_to_bv 64 f /\
       forall x, callee_saved x -> reg_get R (Z_to_bv 5 x) = reg_get regs (Z_to_bv 5 x)));
    [exact Hh | exact Hl | | |].
  { unfold Regs6ss.mkR_of. eapply evt_cut; [apply LW.e5_evt|].
    intros ms' ->. apply evt_done. eexists. split; [reflexivity|]. split; [reflexivity|].
    split; [exact E8|].
    intros x Hx. destruct (LW.lf_callee_cases x Hx) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
      reflexivity. }
  { intros ms (R & -> & _). do 5 eexists. reflexivity. }
  intros R F pc' fc m' (R' & HE & H1 & H10 & Hcs) regs' Hx.
  injection HE as ER EF EP EC EM. subst R F pc' fc m'.
  assert (Q1 : YK11.getr regs' 1 = Z_to_bv 64 0x12f04) by (rewrite (lf_getr_eqv _ _ _ Hx); exact H1).
  assert (Q10 : YK11.getr regs' 10 = Z_to_bv 64 f) by (rewrite (lf_getr_eqv _ _ _ Hx); exact H10).
  assert (RP1 : regs_preserved regs regs').
  { intros x Hx2. rewrite (lf_getr_eqv _ _ _ Hx), !LW.lf_getr_cs by exact Hx2. exact (Hcs x Hx2). }
  assert (Q2 : YK11.getr regs' 2 = Z_to_bv 64 Sp) by exact (LW.pres_get regs regs' 2 _ RP1 ltac:(cs) G2).
  assert (Hsp1 : spZ regs' = Sp) by (unfold spZ at 1; rewrite Q2; apply MState.unsigned_lit; lia).
  pose proof (kp_pres regs regs' KP RP1) as KP1.
  assert (Q4 : YK11.getr regs' 4 = Z_to_bv 64 (ms_tp B)) by (destruct KP1 as (_ & K4 & _); rewrite K4; exact Htp0).
  rewrite <- SEGS. change (Z_to_bv 64 0x14758) with (Z_to_bv 64 LLVM_FREE).
  eapply g_free_cf with (stk := stk) (S := Sx) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0) (x := f) (n := n1)
    (bres := sb_malloc b n1).
  all: try eassumption.
  { lia. }
  { rewrite Q1. apply ret_ok_even. reflexivity. }
  { rewrite Hsp1. replace (spZ regs0 - 64) with (spZ regs0 + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact B3. }
  { rewrite Hsp1. unfold ALLOC_STACK. lia. }
  { lia. } { lia. }
  intros L2 A2 regs2 mem2 md2 FR2 Hrp2 (b1 & b2 & Eb1 & Eb2) Hres2 Hab2 Hkept2.
  rewrite Q1.
  rewrite sb_free_malloc in Hres2.
  apply (sr_tail_cf (mkFP (@fp_regs fx') (@fp_csr fx')) L2 A2 regs2 mem2 md2 Hfrm FR2 Hres2).
  - exact (LW.pres_get regs' regs2 2 _ Hrp2 ltac:(cs) Q2).
  - exact (kp_pres regs' regs2 KP1 Hrp2).
  - apply (LW.lf_rw_cells_frame mem); [exact HC|]. intros a Ha. cbn [cells_size csize LW.lsv Nat.add] in Ha.
    rewrite <- SEGS. apply Hab2. lia.
Qed.

(* 0x12ee0: `if (len) check_read(c, len, slot)` (fuzz_wire.c:277-278), then free(c) *)
Lemma sr_ccr_cf : forall (fx' : YK11.FPState) L A regs mem md f c bs,
  frm_zero (@fp_csr fx') -> lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md ->
  res_ok_slots A (sb_malloc (sb_malloc b n1) n1) ->
  In (f, n1) (blocks L A) -> In (c, n1) (blocks L A) -> f <> c ->
  (forall a k, In (a, k) (blocks L0 A0) -> a + k <= f \/ f + n1 <= a) ->
  (forall a k, In (a, k) (blocks L0 A0) -> a + k <= c \/ c + n1 <= a) ->
  Z.of_nat (length bs) = nn ->
  YK11.getr regs 2 = Z_to_bv 64 Sp -> kp regs -> YK11.getr regs 8 = Z_to_bv 64 f ->
  YK11.getr regs 19 = Z_to_bv 64 c -> YK11.getr regs 10 = Z_to_bv 64 (copy_untag_result nn bs) ->
  Mem.bytes_at (ms_segs B) mem c (cu_bytes nn bs) -> rw_cells rsegs mem Sp sv0 ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12ee0) mem (YK11.seg_rom (ms_segs B))) md) Post.
Proof.
  intros fx' L A regs mem md f c bs Hfrm FR Hres Hinf Hinc Hfc Hdf Hdc HL G2 KP G8 G19 G10 BC HC.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5). pose proof YM05.alloc_ceiling_value as Hac.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & _).
  pose proof FR as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI).
  destruct (LW.nclamp_range n ltac:(lia)) as (N1 & N2 & N3).
  pose proof (LW.fds_ge nn ltac:(lia)) as (D3 & D4). pose proof (fuzz_dup_size_range nn ltac:(lia)) as [D1 D2].
  pose proof (got_le nn bs ltac:(lia)) as GL.
  destruct (f_blk_range L A mem md c n1 FR Hinc) as (C1 & C2).
  destruct (f_blk_range L A mem md f n1 FR Hinf) as (F1 & F2).
  assert (BC' : bytes_at rsegs (normalize rsegs mem) c
                  (firstn (Z.to_nat (copy_untag_result nn bs)) (cu_bytes nn bs))).
  { rewrite SEGS in BC. pose proof (bytes_at_normalize rsegs mem c _ MI BC) as X.
    pose proof (bytes_at_mid _ c _ 0 (Z.to_nat (copy_untag_result nn bs)) X) as Y.
    cbn [skipn] in Y. replace (c + Z.of_nat 0) with c in Y by lia. apply Y.
    rewrite cu_bytes_len by exact HL. lia. }
  pose proof (f_norm L A mem md sv0 FR ltac:(cbn; lia) HC) as HCn.
  pose proof (f_stk L A mem md FR) as STn.
  destruct KP as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
  assert (E2 : reg_get regs 2 = Z_to_bv 64 Sp) by exact G2.
  assert (E3 : reg_get regs 3 = reg_get regs0 3) by exact G3.
  assert (E4 : reg_get regs 4 = reg_get regs0 4) by exact G4.
  assert (E23 : reg_get regs 23 = reg_get regs0 23) by exact G23.
  assert (E24 : reg_get regs 24 = reg_get regs0 24) by exact G24.
  assert (E25 : reg_get regs 25 = reg_get regs0 25) by exact G25.
  assert (E26 : reg_get regs 26 = reg_get regs0 26) by exact G26.
  assert (E27 : reg_get regs 27 = reg_get regs0 27) by exact G27.
  assert (E8 : reg_get regs 8 = Z_to_bv 64 f) by exact G8.
  assert (E10 : reg_get regs 10 = Z_to_bv 64 (copy_untag_result nn bs)) by exact G10.
  assert (E19 : reg_get regs 19 = Z_to_bv 64 c) by exact G19.
  rewrite SEGS.
  eapply (g_run_cf B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx' regs (Z_to_bv 64 0x12ee0) mem md L A).
  { exact FR. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. rewrite E2, E3, E4, E8, E10, E19, E23, E24, E25, E26, E27.
    eapply (LW.e4_evt CRD) with (lo := Sx - stk) (bs := firstn (Z.to_nat (copy_untag_result nn bs)) (cu_bytes nn bs))
      (cs := sv0); rewrite ?(unsigned_lit (spZ regs0 - 64)) by lia.
    - unfold LF_RES_TOP in B5. lia.
    - lia.
    - Z.div_mod_to_equations. lia.
    - lia.
    - lia.
    - lia.
    - rewrite length_firstn, cu_bytes_len by exact HL. lia.
    - exact (mem_inv_normalize rsegs mem).
    - exact STn.
    - exact BC'.
    - exact HCn.
    - reflexivity. }
  { intros ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & FRc).
    do 5 eexists. exists [(Sx - stk, Sp)].
    split; [reflexivity|]. split; [rewrite unsigned_lit in MU by lia; exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply LW.en_out1 in NO. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx1 Hrel1 FR1.
  destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m'' & HE & MU & WM & FRc).
  injection HE as ER EF EP EC EM. subst R F pc' fc m''.
  rewrite unsigned_lit in FRc by lia.
  pose proof (lf_rw_cells_rel m1 _ _ _ Hrel1 FRc) as FC1.
  assert (Q1 : YK11.getr regs1 1 = Z_to_bv 64 0x12efc) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q2 : YK11.getr regs1 2 = Z_to_bv 64 Sp) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q8 : YK11.getr regs1 8 = Z_to_bv 64 f) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q10 : YK11.getr regs1 10 = Z_to_bv 64 c) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (KP1 : kp regs1) by (unfold kp; rewrite !(lf_getr_eqv _ _ _ Hx1); repeat split; reflexivity).
  assert (Hsp1 : spZ regs1 = Sp) by (unfold spZ at 1; rewrite Q2; apply MState.unsigned_lit; lia).
  assert (Q4 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)) by (destruct KP1 as (_ & K4 & _); rewrite K4; exact Htp0).
  rewrite <- SEGS. change (Z_to_bv 64 0x14758) with (Z_to_bv 64 LLVM_FREE).
  eapply g_free_cf with (stk := stk) (S := Sx) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0) (x := c) (n := n1)
    (bres := sb_malloc (sb_malloc b n1) n1).
  all: try eassumption.
  all: try sr_side Hsp1 Q1.
  intros L2 A2 regs2 mem2 md2 FR2 Hrp2 (b1 & b2 & Eb1 & Eb2) Hres2 Hab2 Hkept2.
  rewrite Q1. rewrite sb_free_malloc in Hres2.
  apply (sr_free2_cf (mkFP (@fp_regs fx') (@fp_csr fx')) L2 A2 regs2 mem2 md2 f Hfrm FR2 Hres2).
  - rewrite Eb2. apply (ccg_in_del b1 b2 (c, n1)); [rewrite <- Eb1; exact Hinf|].
    intros E. injection E as E1. exact (Hfc E1).
  - exact Hdf.
  - exact (LW.pres_get regs1 regs2 2 _ Hrp2 ltac:(cs) Q2).
  - exact (kp_pres regs1 regs2 KP1 Hrp2).
  - exact (LW.pres_get regs1 regs2 8 _ Hrp2 ltac:(cs) Q8).
  - apply (LW.lf_rw_cells_frame m1); [exact FC1|]. intros a Ha. cbn [cells_size csize LW.lsv Nat.add] in Ha.
    rewrite <- SEGS. apply Hab2. lia.
Qed.

(* 0x12eb4: fuzz_dup(f, n)'s NULL test and memcpy for c, then check_copy(c, f, n) *)
Lemma sr_mid2_cf : forall (fx' : YK11.FPState) L A regs mem md f c src,
  frm_zero (@fp_csr fx') -> lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md ->
  res_ok_slots A (sb_malloc (sb_malloc b n1) n1) ->
  In (f, n1) (blocks L A) -> In (c, n1) (blocks L A) -> f <> c -> f + n1 <= c \/ c + n1 <= f ->
  (forall a k, In (a, k) (blocks L0 A0) -> a + k <= f \/ f + n1 <= a) ->
  (forall a k, In (a, k) (blocks L0 A0) -> a + k <= c \/ c + n1 <= a) ->
  (forall a k, In (a, k) (blocks L0 A0) -> a <> c) ->
  Z.of_nat (length src) = nn -> blk_data B mem f src ->
  YK11.getr regs 2 = Z_to_bv 64 Sp -> kp regs -> YK11.getr regs 8 = Z_to_bv 64 f ->
  YK11.getr regs 9 = Z_to_bv 64 nn -> YK11.getr regs 10 = Z_to_bv 64 c -> YK11.getr regs 22 = Z_to_bv 64 (n - 1) ->
  rw_cells rsegs mem Sp sv0 ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12eb4) mem (YK11.seg_rom (ms_segs B))) md) Post.
Proof.
  intros fx' L A regs mem md f c src Hfrm FR Hres Hinf Hinc Hfc Hdj Hdf Hdc Hnc HL BD G2 KP G8 G9 G10 G22 HC.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5). pose proof YM05.alloc_ceiling_value as Hac.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & _).
  pose proof FR as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI).
  destruct (LW.nclamp_range n ltac:(lia)) as (N1 & N2 & N3).
  pose proof (LW.fds_ge nn ltac:(lia)) as (D3 & D4). pose proof (fuzz_dup_size_range nn ltac:(lia)) as [D1 D2].
  destruct (f_blk_range L A mem md c n1 FR Hinc) as (C1 & C2).
  destruct (f_blk_range L A mem md f n1 FR Hinf) as (F1 & F2).
  assert (BF : bytes_at rsegs (normalize rsegs mem) f src).
  { apply bytes_at_normalize; [exact MI|]. apply (LW.blk_bytes_at B); [exact SEGS | lia | lia | exact BD]. }
  assert (JK : exists junk, 0 < nn -> rw_cells rsegs (normalize rsegs mem) c [CB (Z.to_nat nn) junk]).
  { destruct (Z_lt_le_dec 0 nn) as [Hp0|Hp0].
    - destruct (norm_blk B API SEGS AX L A mem md c n1 HM Hinc D1 MI) as [junk HJ].
      rewrite (D4 Hp0) in HJ. exists junk. intros _. exact HJ.
    - exists []. intros H. lia. }
  destruct JK as [junk JK].
  pose proof (f_norm L A mem md sv0 FR ltac:(cbn; lia) HC) as HCn.
  destruct KP as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
  assert (E2 : reg_get regs 2 = Z_to_bv 64 Sp) by exact G2.
  assert (E3 : reg_get regs 3 = reg_get regs0 3) by exact G3.
  assert (E4 : reg_get regs 4 = reg_get regs0 4) by exact G4.
  assert (E23 : reg_get regs 23 = reg_get regs0 23) by exact G23.
  assert (E24 : reg_get regs 24 = reg_get regs0 24) by exact G24.
  assert (E25 : reg_get regs 25 = reg_get regs0 25) by exact G25.
  assert (E26 : reg_get regs 26 = reg_get regs0 26) by exact G26.
  assert (E27 : reg_get regs 27 = reg_get regs0 27) by exact G27.
  assert (E8 : reg_get regs 8 = Z_to_bv 64 f) by exact G8.
  assert (E9 : reg_get regs 9 = Z_to_bv 64 nn) by exact G9.
  assert (E10 : reg_get regs 10 = Z_to_bv 64 c) by exact G10.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 (n - 1)) by exact G22.
  rewrite SEGS.
  eapply (g_run_cf B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx' regs (Z_to_bv 64 0x12eb4) mem md L A).
  { exact FR. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. rewrite E2, E3, E4, E8, E9, E10, E22, E23, E24, E25, E26, E27.
    eapply (LW.e3_evt MC) with (src := src) (junk := junk) (cs := sv0); rewrite ?(unsigned_lit (spZ regs0 - 64)) by lia.
    - lia.
    - exact HL.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact (mem_inv_normalize rsegs mem).
    - exact BF.
    - exact JK.
    - exact HCn. }
  { intros ms (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & BC0 & BF0 & FRc).
    do 5 eexists. exists [(c, c + nn)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. apply LW.en_out1 in NO. right. exists c, n1. split; [|lia].
    split; [exact Hinc|]. split; [exact D1 | exact Hdc]. }
  intros R F pc' fc m0' HQ regs1 m1 Hx1 Hrel1 FR1.
  destruct HQ as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m'' & HE & MU & WM & BC0 & BF0 & FRc).
  injection HE as ER EF EP EC EM. subst R F pc' fc m''.
  rewrite unsigned_lit in FRc by lia.
  pose proof (lf_rw_cells_rel m1 _ _ _ Hrel1 FRc) as FC1.
  assert (BC1 : Mem.bytes_at (ms_segs B) m1 c src)
    by (rewrite SEGS; exact (proj2 (bytes_at_rel rsegs m1 m0' c src Hrel1) BC0)).
  assert (BF1 : Mem.bytes_at (ms_segs B) m1 f src)
    by (rewrite SEGS; exact (proj2 (bytes_at_rel rsegs m1 m0' f src Hrel1) BF0)).
  assert (Q1 : YK11.getr regs1 1 = Z_to_bv 64 0x12ee0) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q2 : YK11.getr regs1 2 = Z_to_bv 64 Sp) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q8 : YK11.getr regs1 8 = Z_to_bv 64 f) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q10 : YK11.getr regs1 10 = Z_to_bv 64 c) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q11 : YK11.getr regs1 11 = Z_to_bv 64 f) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q12 : YK11.getr regs1 12 = Z_to_bv 64 nn) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q19 : YK11.getr regs1 19 = Z_to_bv 64 c) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (KP1 : kp regs1) by (unfold kp; rewrite !(lf_getr_eqv _ _ _ Hx1); repeat split; reflexivity).
  assert (Hsp1 : spZ regs1 = Sp) by (unfold spZ at 1; rewrite Q2; apply MState.unsigned_lit; lia).
  assert (Q4 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)) by (destruct KP1 as (_ & K4 & _); rewrite K4; exact Htp0).
  rewrite <- SEGS. change (Z_to_bv 64 0x13550) with (Z_to_bv 64 CHECK_COPY).
  eapply g_cc_cf with (stk := stk) (S := Sx) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0) (c := c) (f := f)
    (n := nn) (kc := n1) (bs := src) (bres := sb_malloc (sb_malloc b n1) n1).
  all: try eassumption.
  all: try sr_side Hsp1 Q1.
  { exists f, n1. split; [exact Hinf|]. split; [exact Hfc|]. lia. }
  { destruct Hroom as (R1 & R2 & R3). unfold cc_room_cf, sb_malloc; cbn [sb_live sb_bytes sb_cap]; unfold CAP_AG in *; lia. }
  intros fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp2 G210 BC2 Eb2 Hres2 Hab2.
  rewrite Q1.
  apply (sr_ccr_cf fx2 L2 A2 regs2 mem2 md2 f c src Hfrm2 FR2 Hres2).
  - rewrite Eb2. exact Hinf.
  - rewrite Eb2. exact Hinc.
  - exact Hfc.
  - exact Hdf.
  - exact Hdc.
  - exact HL.
  - exact (LW.pres_get regs1 regs2 2 _ Hrp2 ltac:(cs) Q2).
  - exact (kp_pres regs1 regs2 KP1 Hrp2).
  - exact (LW.pres_get regs1 regs2 8 _ Hrp2 ltac:(cs) Q8).
  - exact (LW.pres_get regs1 regs2 19 _ Hrp2 ltac:(cs) Q19).
  - exact G210.
  - exact BC2.
  - apply (LW.lf_rw_cells_frame m1); [exact FC1|]. intros a Ha. cbn [cells_size csize LW.lsv Nat.add] in Ha.
    rewrite <- SEGS. apply Hab2. lia.
Qed.

(* 0x12e2c: fuzz_dup(data + 1, n)'s NULL test and memcpy for f, the seven checks, then malloc for c *)
Lemma sr_mid1_cf : forall (fx' : YK11.FPState) L A regs mem md f (b0 : byte),
  frm_zero (@fp_csr fx') -> lf_fr B API stk Sx L0 A0 mem0 md0 L A mem md -> res_ok_slots A (sb_malloc b n1) ->
  In (f, n1) (blocks L A) -> (forall a k, In (a, k) (blocks L0 A0) -> a + k <= f \/ f + n1 <= a) ->
  YK11.getr regs 2 = Z_to_bv 64 Sp -> kp regs -> YK11.getr regs 9 = Z_to_bv 64 nn ->
  YK11.getr regs 10 = Z_to_bv 64 f -> YK11.getr regs 18 = zxb b0 -> YK11.getr regs 19 = Z_to_bv 64 n1 ->
  YK11.getr regs 20 = Z_to_bv 64 p -> YK11.getr regs 22 = Z_to_bv 64 (n - 1) ->
  rw_cells rsegs mem Sp sv0 ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 0x12e2c) mem (YK11.seg_rom (ms_segs B))) md) Post.
Proof.
  intros fx' L A regs mem md f b0 Hfrm FR Hres Hinf Hdf G2 KP G9 G10 G18 G19 G20 G22 HC.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5). pose proof YM05.alloc_ceiling_value as Hac.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & _).
  pose proof FR as (HM & _ & _ & _ & _ & _ & _ & Hblk & _ & _ & _ & _ & MI).
  destruct (LW.nclamp_range n ltac:(lia)) as (N1 & N2 & N3).
  pose proof (LW.fds_ge nn ltac:(lia)) as (D3 & D4). pose proof (fuzz_dup_size_range nn ltac:(lia)) as [D1 D2].
  destruct (f_blk_range L A mem md f n1 FR Hinf) as (F1 & F2).
  destruct (f_blk L A mem md FR) as (Hinp & BDp).
  destruct f_pay as (Hinp0 & P1 & P2 & _ & _).
  set (src := firstn (Z.to_nat nn) (skipn 1 pl)).
  assert (HLs : Z.of_nat (length src) = nn) by (unfold src; rewrite length_firstn, length_skipn; lia).
  assert (BS : bytes_at rsegs (normalize rsegs mem) (p + 1) src).
  { assert (X : bytes_at rsegs (normalize rsegs mem) p pl).
    { apply bytes_at_normalize; [exact MI|]. apply (LW.blk_bytes_at B); [exact SEGS | lia | lia | exact BDp]. }
    exact (bytes_at_mid _ p pl 1 (Z.to_nat nn) X ltac:(lia)). }
  assert (DJ : p + 1 + nn <= f \/ f + nn <= p + 1) by (destruct (Hdf p n Hinp0); lia).
  assert (JK : exists junk, 0 < nn -> rw_cells rsegs (normalize rsegs mem) f [CB (Z.to_nat nn) junk]).
  { destruct (Z_lt_le_dec 0 nn) as [Hp0|Hp0].
    - destruct (norm_blk B API SEGS AX L A mem md f n1 HM Hinf D1 MI) as [junk HJ].
      rewrite (D4 Hp0) in HJ. exists junk. intros _. exact HJ.
    - exists []. intros H. lia. }
  destruct JK as [junk JK].
  pose proof (f_norm L A mem md sv0 FR ltac:(cbn; lia) HC) as HCn.
  pose proof (f_stk L A mem md FR) as STn.
  destruct KP as (G3 & G4 & G23 & G24 & G25 & G26 & G27).
  assert (E2 : reg_get regs 2 = Z_to_bv 64 Sp) by exact G2.
  assert (E3 : reg_get regs 3 = reg_get regs0 3) by exact G3.
  assert (E4 : reg_get regs 4 = reg_get regs0 4) by exact G4.
  assert (E23 : reg_get regs 23 = reg_get regs0 23) by exact G23.
  assert (E24 : reg_get regs 24 = reg_get regs0 24) by exact G24.
  assert (E25 : reg_get regs 25 = reg_get regs0 25) by exact G25.
  assert (E26 : reg_get regs 26 = reg_get regs0 26) by exact G26.
  assert (E27 : reg_get regs 27 = reg_get regs0 27) by exact G27.
  assert (E9 : reg_get regs 9 = Z_to_bv 64 nn) by exact G9.
  assert (E10 : reg_get regs 10 = Z_to_bv 64 f) by exact G10.
  assert (E18 : reg_get regs 18 = zxb b0) by exact G18.
  assert (E19 : reg_get regs 19 = Z_to_bv 64 n1) by exact G19.
  assert (E20 : reg_get regs 20 = Z_to_bv 64 p) by exact G20.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 (n - 1)) by exact G22.
  rewrite SEGS.
  eapply (g_run_cf B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx' regs (Z_to_bv 64 0x12e2c) mem md L A).
  { exact FR. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. rewrite E2, E3, E4, E9, E10, E18, E19, E20, E22, E23, E24, E25, E26, E27.
    eapply LW.e2_evt with (lo := Sx - stk) (src := src) (cs := sv0) (junk := junk);
      rewrite ?(unsigned_lit (spZ regs0 - 64)) by lia;
      first [ eassumption | exact (mem_inv_normalize rsegs mem) | reflexivity | (unfold LF_RES_TOP in B5; lia)
            | lia | (Z.div_mod_to_equations; lia) ]. }
  { intros ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & sl & bt & m' & -> & MU & WM &
      BF0 & FRc).
    do 5 eexists. exists [(Sx - stk, Sp); (f, f + nn)].
    split; [reflexivity|]. split; [rewrite unsigned_lit in MU by lia; exact MU|]. split; [exact WM|].
    intros x Hx NO. destruct (LW.en_out2 _ _ _ _ _ NO) as [H|H]; [left; lia|].
    right. exists f, n1. split; [|lia]. split; [exact Hinf|]. split; [exact D1 | exact Hdf]. }
  intros R F pc' fc m0' HQ regs1 m1 Hx1 Hrel1 FR1.
  destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & sl & bt & m'' & HE & MU & WM &
    BF0 & FRc).
  injection HE as ER EF EP EC EM. subst R F pc' fc m''.
  rewrite unsigned_lit in FRc by lia.
  pose proof (lf_rw_cells_rel m1 _ _ _ Hrel1 FRc) as FC1.
  assert (BD1 : blk_data B m1 f src).
  { apply (LW.bytes_at_blk B); [exact SEGS|]. exact (proj2 (bytes_at_rel rsegs m1 m0' f src Hrel1) BF0). }
  assert (Q1 : YK11.getr regs1 1 = Z_to_bv 64 0x12eb4) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q2 : YK11.getr regs1 2 = Z_to_bv 64 Sp) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q8 : YK11.getr regs1 8 = Z_to_bv 64 f) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q9 : YK11.getr regs1 9 = Z_to_bv 64 nn) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q10 : YK11.getr regs1 10 = Z_to_bv 64 n1) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q22 : YK11.getr regs1 22 = Z_to_bv 64 (n - 1)) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (KP1 : kp regs1) by (unfold kp; rewrite !(lf_getr_eqv _ _ _ Hx1); repeat split; reflexivity).
  assert (Hsp1 : spZ regs1 = Sp) by (unfold spZ at 1; rewrite Q2; apply MState.unsigned_lit; lia).
  assert (Q4 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)) by (destruct KP1 as (_ & K4 & _); rewrite K4; exact Htp0).
  rewrite <- SEGS. change (Z_to_bv 64 0x14898) with (Z_to_bv 64 LLVM_MALLOC).
  eapply g_malloc_cf with (stk := stk) (S := Sx) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0) (n := n1)
    (bres := sb_malloc b n1).
  all: try eassumption.
  all: try sr_side Hsp1 Q1.
  { destruct Hroom as (R1 & R2 & R3). apply room_ag_gen; unfold sb_malloc; cbn [sb_live sb_bytes sb_cap]; unfold CAP_AG in *; lia. }
  intros L2 A2 regs2 mem2 md2 c FR2 Hrp2 G210 Hc1 Hc2 Hc16 Hcimg (b1 & b2 & Eb1 & Eb2) Hres2 Hab2 Hkept2.
  rewrite Q1.
  pose proof FR2 as (HM2 & _).
  pose proof FR1 as (_ & _ & _ & _ & _ & _ & _ & Hblk1 & _).
  assert (PW : pairwise ranges_disjoint (b1 ++ (c, n1) :: b2))
    by (rewrite <- Eb1; exact (mr_blocks_disjoint B _ (aa_laws API) L2 A2 mem2 md2 HM2)).
  assert (Hinf' : In (f, n1) (b1 ++ b2)) by (rewrite <- Eb2; exact Hinf).
  pose proof (LW.disj_mid b1 (c, n1) b2 (f, n1) PW Hinf') as Dcf. cbn [fst snd] in Dcf.
  assert (Hdc : forall a k, In (a, k) (blocks L0 A0) -> a + k <= c \/ c + n1 <= a).
  { intros a k Hak. pose proof (Hblk1 a k Hak) as Hak1. rewrite Eb2 in Hak1.
    pose proof (LW.disj_mid b1 (c, n1) b2 (a, k) PW Hak1) as H. cbn [fst snd] in H. lia. }
  assert (Hnc : forall a k, In (a, k) (blocks L0 A0) -> a <> c).
  { intros a k Hak Ea. subst a. pose proof (BND L2 A2 mem2 md2 HM2) as ND. rewrite Eb1, map_app in ND.
    cbn [map fst] in ND. apply NoDup_ListNoDup in ND. apply NoDup_remove_2 in ND. apply ND. rewrite <- map_app, <- Eb2.
    apply in_map_iff. exists (c, k). split; [reflexivity | exact (Hblk1 _ _ Hak)]. }
  apply (sr_mid2_cf (mkFP (@fp_regs fx') (@fp_csr fx')) L2 A2 regs2 mem2 md2 f c src Hfrm FR2 Hres2).
  - rewrite Eb1. apply ccg_in_ins. exact Hinf'.
  - rewrite Eb1. apply ccg_in_mid.
  - intros E. rewrite E in Dcf. lia.
  - lia.
  - exact Hdf.
  - exact Hdc.
  - exact Hnc.
  - exact HLs.
  - intros i Hi. rewrite (Hkept2 f n1 i Hinf (fun H => H) ltac:(lia)). exact (BD1 i Hi).
  - exact (LW.pres_get regs1 regs2 2 _ Hrp2 ltac:(cs) Q2).
  - exact (kp_pres regs1 regs2 KP1 Hrp2).
  - exact (LW.pres_get regs1 regs2 8 _ Hrp2 ltac:(cs) Q8).
  - exact (LW.pres_get regs1 regs2 9 _ Hrp2 ltac:(cs) Q9).
  - exact G210.
  - exact (LW.pres_get regs1 regs2 22 _ Hrp2 ltac:(cs) Q22).
  - apply (LW.lf_rw_cells_frame m1); [exact FC1|]. intros a Ha. cbn [cells_size csize LW.lsv Nat.add] in Ha.
    rewrite <- SEGS. apply Hab2. lia.
Qed.

Hypothesis Hres0 : res_ok_slots A0 b.

(* 0x12dc0: the prologue up to f = fuzz_dup(data + 1, n)'s malloc *)
Lemma sr_entry_cf : frm_zero (@fp_csr fx) ->
  SRcf B (mkCfg (@YK11.mkst fx regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 (YK11.seg_rom (ms_segs B))) md0) Post.
Proof.
  intros Hfrm.
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5). pose proof YM05.alloc_ceiling_value as Hac.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & _).
  destruct f_pay as (Hinp & P1 & P2 & E10 & E11).
  destruct (LW.nclamp_range n ltac:(lia)) as (N1 & N2 & N3).
  pose proof (LW.fds_ge nn ltac:(lia)) as (D3 & D4). pose proof (fuzz_dup_size_range nn ltac:(lia)) as [D1 D2].
  pose proof (lf_fr_init B API stk empty L0 A0 regs0 mem0 md0 ra p n Hpre Hro) as FR0.
  assert (Esp : Sx = bv_unsigned (reg_get regs0 2)) by reflexivity.
  assert (ST0 : Frame.stk rsegs (normalize rsegs mem0) (Sx - stk) (bv_unsigned (reg_get regs0 2))).
  { rewrite <- Esp. apply lf_stk; [unfold LF_RES_TOP in *; lia | lia |].
    intros a Ha. unfold writable_at.
    assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
    rewrite (wview_rel_rw rsegs mem0 (normalize rsegs mem0) _ (mem_rel_normalize rsegs mem0 Hro)
               (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
    rewrite <- SEGS. exact (Hstw0 a Ha). }
  assert (HPB : bytes_at rsegs (normalize rsegs mem0) p pl).
  { apply bytes_at_normalize; [exact Hro|]. apply (LW.blk_bytes_at B); [exact SEGS | lia | lia | exact Hpd]. }
  rewrite SEGS.
  eapply (g_run_cf B API SEGS AX HGG stk Sx L0 A0 mem0 md0 fx regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 md0 L0 A0).
  { exact FR0. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of, LLVM_ENTRY. rewrite E10, E11.
    eapply LW.e1_evt with (lo := Sx - stk) (pl := pl).
    - exact ST0.
    - rewrite <- Esp. lia.
    - exact (mem_inv_normalize rsegs mem0).
    - exact Hn.
    - exact Hlen.
    - exact HPB.
    - exact P1.
    - lia. }
  { intros ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & FRc).
    do 5 eexists. exists [(bv_unsigned (reg_get regs0 2) - 64, bv_unsigned (reg_get regs0 2))].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply LW.en_out1 in NO. rewrite <- Esp in NO. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx1 Hrel1 FR1.
  destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m'' & HE & MU & WM & FRc).
  injection HE as ER EF EP EC EM. subst R F pc' fc m''.
  rewrite <- Esp in FRc.
  pose proof (lf_rw_cells_rel m1 _ _ _ Hrel1 FRc) as FC1.
  assert (Q1 : YK11.getr regs1 1 = Z_to_bv 64 0x12e2c) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q2 : YK11.getr regs1 2 = Z_to_bv 64 Sp) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q9 : YK11.getr regs1 9 = Z_to_bv 64 nn) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q10 : YK11.getr regs1 10 = Z_to_bv 64 n1) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q18 : YK11.getr regs1 18 = zxb (nth 0 pl (Z_to_bv 8 0))) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q19 : YK11.getr regs1 19 = Z_to_bv 64 n1) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q20 : YK11.getr regs1 20 = Z_to_bv 64 p) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (Q22 : YK11.getr regs1 22 = Z_to_bv 64 (n - 1)) by (rewrite (lf_getr_eqv _ _ _ Hx1); reflexivity).
  assert (KP1 : kp regs1) by (unfold kp; rewrite !(lf_getr_eqv _ _ _ Hx1); repeat split; reflexivity).
  assert (Hsp1 : spZ regs1 = Sp) by (unfold spZ at 1; rewrite Q2; apply MState.unsigned_lit; lia).
  assert (Q4 : YK11.getr regs1 4 = Z_to_bv 64 (ms_tp B)) by (destruct KP1 as (_ & K4 & _); rewrite K4; exact Htp0).
  rewrite <- SEGS. change (Z_to_bv 64 0x14898) with (Z_to_bv 64 LLVM_MALLOC).
  eapply g_malloc_cf with (stk := stk) (S := Sx) (L0 := L0) (A0 := A0) (mem0 := mem0) (md0 := md0) (n := n1) (bres := b).
  all: try eassumption.
  all: try sr_side Hsp1 Q1.
  { destruct Hroom as (R1 & R2 & R3). apply room_ag_gen; unfold CAP_AG in *; lia. }
  intros L2 A2 regs2 mem2 md2 f FR2 Hrp2 G210 Hf1 Hf2 Hf16 Hfimg (b1 & b2 & Eb1 & Eb2) Hres2 Hab2 Hkept2.
  rewrite Q1.
  pose proof FR2 as (HM2 & _).
  assert (PW : pairwise ranges_disjoint (b1 ++ (f, n1) :: b2))
    by (rewrite <- Eb1; exact (mr_blocks_disjoint B _ (aa_laws API) L2 A2 mem2 md2 HM2)).
  assert (Hdf : forall a k, In (a, k) (blocks L0 A0) -> a + k <= f \/ f + n1 <= a).
  { intros a k Hak. rewrite Eb2 in Hak. pose proof (LW.disj_mid b1 (f, n1) b2 (a, k) PW Hak) as H.
    cbn [fst snd] in H. lia. }
  apply (sr_mid1_cf (mkFP (@fp_regs fx) (@fp_csr fx)) L2 A2 regs2 mem2 md2 f (nth 0 pl (Z_to_bv 8 0)) Hfrm FR2 Hres2).
  - rewrite Eb1. apply ccg_in_mid.
  - exact Hdf.
  - exact (LW.pres_get regs1 regs2 2 _ Hrp2 ltac:(cs) Q2).
  - exact (kp_pres regs1 regs2 KP1 Hrp2).
  - exact (LW.pres_get regs1 regs2 9 _ Hrp2 ltac:(cs) Q9).
  - exact G210.
  - exact (LW.pres_get regs1 regs2 18 _ Hrp2 ltac:(cs) Q18).
  - exact (LW.pres_get regs1 regs2 19 _ Hrp2 ltac:(cs) Q19).
  - exact (LW.pres_get regs1 regs2 20 _ Hrp2 ltac:(cs) Q20).
  - exact (LW.pres_get regs1 regs2 22 _ Hrp2 ltac:(cs) Q22).
  - apply (LW.lf_rw_cells_frame m1); [exact FC1|]. intros a Ha. cbn [cells_size csize LW.lsv Nat.add] in Ha.
    rewrite <- SEGS. apply Hab2. lia.
Qed.

End Run.

Theorem LLVMFuzzerTestOneInput_holds_of_cf : LLVMFuzzerTestOneInput_sr_contract_cf B API.
Proof using MALLOC FREE ERRNO_LOW SINK BND CT MC CF CR CD CM CN CW CRD CC.
  intros BI j Hj ra empty stk Hk Hra L A regs mem md p n pl b Hpre Hn Hpl Hsn Hsp Hres Hroom Hro Hrelro HGI Hfrm.
  pose proof (LW.llvm_n_bound B API stk empty L A regs mem md ra p n Hpre) as Hnb.
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn11 & _).
  destruct (Z_lt_le_dec n (2 ^ 26)) as [Hsmall|Hbig].
  - destruct (Z.eq_dec n 0) as [H0|H0].
    + apply (llvm_early_cf B API SINK j stk empty L A regs mem md ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm).
      left. rewrite Hn11. rewrite MState.unsigned_lit by lia. exact H0.
    + exact (sr_entry_cf stk empty L A regs mem md ra p n pl b j BI Hk Hra Hpre Hn Hpl Hsn Hsp Hroom Hro ltac:(lia) Hres
               Hfrm).
  - apply (llvm_early_cf B API SINK j stk empty L A regs mem md ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm).
    right. rewrite Hn11. rewrite MState.unsigned_lit by lia. exact Hbig.
Qed.

End M.
