(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/U/Prog/fd_glue_cg.v at
   25e3d17bdb5059606131377a3722d585415ab5d6; g_run_cf, g_malloc_cf and g_free_cf at this unit's module path (over
   lib/U/Prog/LLVMFuzzerTestOneInput_gl.v's g_pre and g_above), and g_crs_cf, g_cm_cf and g_ci_cf that file's g_crt_cf
   at this program's three K-style callees, the cf twins of lib/U/Prog/LLVMFuzzerTestOneInput_gl.v's g_crs, g_cm and
   g_ci. *)
(* The cut-free (SRcf) walk of fuzz_egress's LLVMFuzzerTestOneInput on the UBSan image, against
   lib/U/Prog/LLVMFuzzerTestOneInput_cfb.v's LLVMFuzzerTestOneInput_sr_contract_cf: LLVMFuzzerTestOneInput_holds_of_cf,
   as reac-repacer/fuzz_uci's lib/U/Prog/LLVMFuzzerTestOneInput_cg.v (at bc49657c087a) is to its U walk. Section M is
   lib/U/Prog/LLVMFuzzerTestOneInput.v's with SR replaced by SRcf (SRcf_bind / SRcf_ret, llvm_run_norm_cf): malloc at
   the agree room (malloc_contract_ag, room_ag), free at free_contract_cf, the three K-style callees at their cf
   contracts (check_restamp_ccf.v, check_mute_ccf.v, check_inject_ccf.v: cr_room_cf / cm_room_cf / ci_room_cf), the
   size >= 64 MiB arm by llvm_early_cf; check_gate, memset and memcpy at the evt contracts the U walk uses; the rooms
   from llvm_room_cf (room_ag_b, room_cr, room_cm, room_ci). The instruction segments (that walk's e1, and s1e .. s1i
   of lib/U/Prog/LLVMFuzzerTestOneInput_evt.v), the states q1 .. qret and the frame helpers outside that walk's
   Section Run (blk_bytes_at, blk_keep, norm_blk, disj_mid, lf_rw_cells_frame) are that walk's, used as they are
   (module LW); its Section Run lemmas are restated here over this section's hypotheses. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import memset_c memcpy_c check_gate_c
  check_restamp_c check_mute_c check_inject_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr
  LLVMFuzzerTestOneInput_evt LLVMFuzzerTestOneInput_gl.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require Import LLVMFuzzerTestOneInput_cfb
  check_restamp_ccf check_mute_ccf check_inject_ccf LLVMFuzzerTestOneInput_early_cg.
From OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog Require LLVMFuzzerTestOneInput.
Import ListNotations.
Open Scope Z_scope.

Module LW := OSSVerify.Proofs.reac_repacer.fuzz_egress.lib.U.Prog.LLVMFuzzerTestOneInput.

(* lib/U/Prog/LLVMFuzzerTestOneInput.v's en_out1, outside a section here (that file's copy sits in its Section Run,
   whose lia proof picks up the section variable pl) *)
Lemma en_out1 : forall lo hi x, ~ outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x NO. destruct (Z_le_dec lo x); destruct (Z_lt_dec x hi); try lia;
    exfalso; apply NO; cbn [outside]; (split; [lia | exact I]).
Qed.

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
    - apply call_pre_k_alloc. exact (g_pre B API stk S L0 A0 mem0 md0 L A mem md regs ALLOC_STACK FR Hra Hal H1 H2
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
  - apply (g_above B API ERRNO_LOW stk S L A regs mem md ALLOC_STACK (fun _ => False) L2 A2 regs2 mem2 md2 HM).
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
    - apply call_pre_k_alloc. exact (g_pre B API stk S L0 A0 mem0 md0 L A mem md regs ALLOC_STACK FR Hra Hal H1 H2
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
  - apply (g_above B API ERRNO_LOW stk S L A regs mem md ALLOC_STACK (fun a => ptr_addr L q <= a < ptr_addr L q + n)
      L2 A2 regs2 mem2 md2 HM Hpost Hc H1 HS ltac:(unfold ALLOC_STACK; lia)).
    intros a Ha. rewrite Hq in Ha. exact (proj1 (Hfreed a Ha)).
  - exact Hkept.
Qed.

(* check_restamp (0x12e58) at the SRcf level: the call and what the harness keeps across it *)
Lemma g_crs_cf : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A f n ctr bres (P : config -> Prop),
  (forall fx'' : YK11.FPState, @check_restamp_contract_cf fx'' rc B API) ->
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - CHECK_RESTAMP_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  YK11.getr regs 10 = Z_to_bv 64 f -> YK11.getr regs 11 = Z_to_bv 64 n -> YK11.getr regs 12 = Z_to_bv 64 ctr ->
  0 <= n <= 1600 -> in_block L A f n ->
  frm_zero (@fp_csr fx') -> res_ok_slots A bres -> cr_room_cf bres n ->
  (forall (fx'' : YK11.FPState) L' A' regs' mem' md',
     frm_zero (@fp_csr fx'') ->
     lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     blocks L' A' = blocks L A -> res_ok_slots A' bres ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     blocks_kept B L A mem mem' (fun _ => False) ->
     SRcf B (mkCfg (@YK11.mkst fx'' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 CHECK_RESTAMP) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A f n ctr bres P CC FR Hc HS Hra Hal H1 H2 H63 Htp
    G10 G11 G12 Hn IB Hfrm Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  eapply (SRcf_bind B).
  { apply (CC fx' L A regs mem md f n ctr bres SEGS).
    - exact (g_pre B API stk S L0 A0 mem0 md0 L A mem md regs CHECK_RESTAMP_STACK FR Hra Hal H1 H2
        ltac:(unfold CHECK_RESTAMP_STACK, CR_FRAME, ALLOC_STACK; lia) Hc H63 Htp).
    - exact G10.
    - exact G11.
    - exact G12.
    - exact Hn.
    - exact IB.
    - rewrite SEGS. exact MI.
    - exact Hfrm.
    - exact Hres.
    - exact Hroom. }
  intros c2 (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & Hfrm2 & Hpost & Eb & Hkept & Hgk & Hro2 & Hres2 & Hidt).
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | unfold CHECK_RESTAMP_STACK, CR_FRAME, ALLOC_STACK in *; lia | lia | | | | | | exact (Hidt HID) | | ].
    - intros a Ha. exfalso. exact Ha.
    - intros a Ha. right. intros Hf. exact Hf.
    - intros a Hf Ha. exfalso. exact Hf.
    - intros a0 k0 Hin. rewrite Eb. exact (Hblk a0 k0 Hin).
    - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i (Hblk a0 k0 Hin) (fun H => H) Hi).
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp Eb Hres2); [| exact Hkept].
  apply (g_above B API ERRNO_LOW stk S L A regs mem md CHECK_RESTAMP_STACK (fun _ => False) L2 A2 regs2 mem2 md2 HM
    Hpost Hc H1 HS ltac:(unfold CHECK_RESTAMP_STACK, CR_FRAME, ALLOC_STACK; lia)).
  intros a Ha. destruct Ha.
Qed.

(* check_mute (0x12f50) at the SRcf level *)
Lemma g_cm_cf : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A f n bres (P : config -> Prop),
  (forall fx'' : YK11.FPState, @check_mute_contract_cf fx'' rc B API) ->
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - CHECK_MUTE_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  YK11.getr regs 10 = Z_to_bv 64 f -> YK11.getr regs 11 = Z_to_bv 64 n ->
  0 <= n <= 1600 -> in_block L A f n ->
  frm_zero (@fp_csr fx') -> res_ok_slots A bres -> cm_room_cf bres n ->
  (forall (fx'' : YK11.FPState) L' A' regs' mem' md',
     frm_zero (@fp_csr fx'') ->
     lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     blocks L' A' = blocks L A -> res_ok_slots A' bres ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     blocks_kept B L A mem mem' (fun _ => False) ->
     SRcf B (mkCfg (@YK11.mkst fx'' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 CHECK_MUTE) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A f n bres P CC FR Hc HS Hra Hal H1 H2 H63 Htp
    G10 G11 Hn IB Hfrm Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  eapply (SRcf_bind B).
  { apply (CC fx' L A regs mem md f n bres SEGS).
    - exact (g_pre B API stk S L0 A0 mem0 md0 L A mem md regs CHECK_MUTE_STACK FR Hra Hal H1 H2
        ltac:(unfold CHECK_MUTE_STACK, CHECK_MUTE_FRAME, ALLOC_STACK; lia) Hc H63 Htp).
    - exact G10.
    - exact G11.
    - exact Hn.
    - exact IB.
    - rewrite SEGS. exact MI.
    - exact Hfrm.
    - exact Hres.
    - exact Hroom. }
  intros c2 (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & Hfrm2 & Hpost & Eb & Hkept & Hgk & Hro2 & Hres2 & Hidt).
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | unfold CHECK_MUTE_STACK, CHECK_MUTE_FRAME, ALLOC_STACK in *; lia | lia | | | | | | exact Hidt | | ].
    - intros a Ha. exfalso. exact Ha.
    - intros a Ha. right. intros Hf. exact Hf.
    - intros a Hf Ha. exfalso. exact Hf.
    - intros a0 k0 Hin. rewrite Eb. exact (Hblk a0 k0 Hin).
    - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i (Hblk a0 k0 Hin) (fun H => H) Hi).
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp Eb Hres2); [| exact Hkept].
  apply (g_above B API ERRNO_LOW stk S L A regs mem md CHECK_MUTE_STACK (fun _ => False) L2 A2 regs2 mem2 md2 HM Hpost
    Hc H1 HS ltac:(unfold CHECK_MUTE_STACK, CHECK_MUTE_FRAME, ALLOC_STACK; lia)).
  intros a Ha. destruct Ha.
Qed.

(* check_inject (0x130b0) at the SRcf level *)
Lemma g_ci_cf : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A f n slot v bres (P : config -> Prop),
  (forall fx'' : YK11.FPState, @check_inject_contract_cf fx'' rc B API) ->
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - CHECK_INJECT_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  YK11.getr regs 10 = Z_to_bv 64 f -> YK11.getr regs 11 = Z_to_bv 64 n ->
  YK11.getr regs 12 = Z_to_bv 64 slot -> YK11.getr regs 13 = Z_to_bv 64 v ->
  0 <= n <= 1600 -> -2 <= slot <= 253 -> in_block L A f n ->
  spZ regs <= v -> v + 48 <= 2 ^ 64 -> v mod 4 = 0 -> (forall i, 0 <= i < 48 -> present mem (v + i)) ->
  frm_zero (@fp_csr fx') -> res_ok_slots A bres -> ci_room_cf bres n ->
  (forall (fx'' : YK11.FPState) L' A' regs' mem' md',
     frm_zero (@fp_csr fx'') ->
     lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     blocks L' A' = blocks L A -> res_ok_slots A' bres ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     blocks_kept B L A mem mem' (fun _ => False) ->
     SRcf B (mkCfg (@YK11.mkst fx'' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') P) ->
  SRcf B (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 CHECK_INJECT) mem (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A f n slot v bres P CC FR Hc HS Hra Hal H1 H2 H63 Htp
    G10 G11 G12 G13 Hn Hslot IB Hv1 Hv2 Hv3 Hvp Hfrm Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  eapply (SRcf_bind B).
  { apply (CC fx' L A regs mem md f n slot v bres SEGS).
    - exact (g_pre B API stk S L0 A0 mem0 md0 L A mem md regs CHECK_INJECT_STACK FR Hra Hal H1 H2
        ltac:(unfold CHECK_INJECT_STACK, CHECK_INJECT_FRAME, ALLOC_STACK; lia) Hc H63 Htp).
    - exact G10.
    - exact G11.
    - exact G12.
    - exact G13.
    - exact Hn.
    - exact Hslot.
    - exact IB.
    - exact Hv1.
    - exact Hv2.
    - exact Hv3.
    - exact Hvp.
    - rewrite SEGS. exact MI.
    - exact Hfrm.
    - exact Hres.
    - exact Hroom. }
  intros c2 (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & Hfrm2 & Hpost & Eb & Hkept & Hgk & Hro2 & Hres2 & Hidt).
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | unfold CHECK_INJECT_STACK, CHECK_INJECT_FRAME, ALLOC_STACK in *; lia | lia | | | | | | exact Hidt | | ].
    - intros a Ha. exfalso. exact Ha.
    - intros a Ha. right. intros Hf. exact Hf.
    - intros a Hf Ha. exfalso. exact Hf.
    - intros a0 k0 Hin. rewrite Eb. exact (Hblk a0 k0 Hin).
    - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i (Hblk a0 k0 Hin) (fun H => H) Hi).
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp Eb Hres2); [| exact Hkept].
  apply (g_above B API ERRNO_LOW stk S L A regs mem md CHECK_INJECT_STACK (fun _ => False) L2 A2 regs2 mem2 md2 HM
    Hpost Hc H1 HS ltac:(unfold CHECK_INJECT_STACK, CHECK_INJECT_FRAME, ALLOC_STACK; lia)).
  intros a Ha. destruct Ha.
Qed.

End G.

(* reg_get facts of a machine state carried to the config registers it is equivalent to (fuzz_uci's idiom) *)
Ltac xr Hx Rk E := lazymatch type of Rk with reg_get _ ?k = ?v => lazymatch type of Hx with Regs6ss.xregs_eqv _ ?r' =>
  assert (E : reg_get r' k = v) by (rewrite <- (Hx k eq_refl); exact Rk) end end.
(* a callee-saved register across a call *)
Tactic Notation "pz" constr(Hrp) constr(E) constr(kz) ident(E') :=
  lazymatch type of E with _ ?r1 _ = ?v => lazymatch type of Hrp with regs_preserved r1 ?r2 =>
  assert (E' : YK11.getr r2 (Z_to_bv 5 kz) = v) by (rewrite (Hrp kz ltac:(unfold callee_saved; lia)); exact E) end end.

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis MALLOC : forall fx' : YK11.FPState, @malloc_contract_ag fx' rc B API.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract_cf fx' rc B API.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= YM05.alloc_ceiling.
Hypothesis SINK : lf_sink_env B.
Hypothesis MSET : memset_contract.
Hypothesis MCPY : memcpy_contract.
Hypothesis CG : check_gate_contract.
Hypothesis CRS : forall fx' : YK11.FPState, @check_restamp_contract_cf fx' rc B API.
Hypothesis CM : forall fx' : YK11.FPState, @check_mute_contract_cf fx' rc B API.
Hypothesis CI : forall fx' : YK11.FPState, @check_inject_contract_cf fx' rc B API.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).

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
Hypothesis Hres0 : res_ok_slots A0 b.

Lemma f_bounds : 8464 <= stk /\ YM05.alloc_ceiling + stk <= spZ regs0 /\ spZ regs0 mod 16 = 0 /\
  spZ regs0 <= 2 ^ 47 /\ LF_RES_TOP < YM05.alloc_ceiling /\ 0 <= n.
Proof.
  pose proof Hpre as (_ & _ & _ & _ & _ & Hal & Hceil & _).
  pose proof Hk as Hk'. unfold LLVM_K, LLVM_FRAME, CHECK_INJECT_STACK, CHECK_INJECT_FRAME, ALLOC_STACK in Hk'.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  split; [lia|]. split; [exact Hceil|]. split; [exact Hal|]. split; [exact Hsp|]. split; [exact Hrt | lia].
Qed.

Lemma f_pay : 0 < n -> In (bv_unsigned (reg_get regs0 10), n) (blocks L0 A0) /\
  4096 <= bv_unsigned (reg_get regs0 10) /\ bv_unsigned (reg_get regs0 10) + n <= YM05.alloc_ceiling /\
  bv_unsigned (reg_get regs0 10) = p.
Proof.
  intros Hn0.
  pose proof Hpre as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _ & Hpl & _).
  pose proof YM05.alloc_ceiling_value as Hac.
  destruct Hpl as [[-> _] | [_ (q & Hq & Hqp)]]; [lia|].
  pose proof (mr_blocks_range B _ (aa_laws API) L0 A0 mem0 md0 q n HM Hq) as (R1 & R2). rewrite Hqp in R1, R2.
  assert (E : bv_unsigned (reg_get regs0 10) = p).
  { assert (E10 : reg_get regs0 10 = Z_to_bv 64 p) by exact Hp. rewrite E10. apply MState.unsigned_lit. lia. }
  rewrite E. split; [apply blocks_In; exists q; split; [exact Hqp | exact Hq]|]. lia.
Qed.

Lemma f_p'range : 0 <= bv_unsigned (reg_get regs0 10) < 2 ^ 64.
Proof.
  pose proof (bv_unsigned_in_range _ (reg_get regs0 10)) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in R. exact R.
Qed.

Lemma f_stk : forall L A mem md hi, lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md ->
  spZ regs0 - stk <= hi <= spZ regs0 ->
  Frame.stk rsegs (normalize rsegs mem) (spZ regs0 - stk) hi.
Proof.
  intros L A mem md hi FR Hhi. pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hstw & _ & _ & MI).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5 & B6). pose proof YM05.alloc_ceiling_value as Hac.
  apply lf_stk; [lia | lia |]. intros a Ha. unfold writable_at.
  assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
  rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem MI)
             (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
  rewrite <- SEGS. exact (Hstw a ltac:(lia)).
Qed.

(* the agree rooms: malloc's (room_ag) and the three K-style callees' (cr / cm / ci_room_cf) after it *)
Lemma room_ag_b : forall k, 0 <= k <= 1600 -> room_ag b k.
Proof.
  intros k Hkk. destruct Hroom as (R1 & R2 & R3). apply room_ag_gen; lia.
Qed.

Lemma room_cr : forall k k', 0 <= k <= 1600 -> 0 <= k' <= 1600 -> cr_room_cf (sb_malloc b k') k.
Proof.
  intros k k' Hkk Hkk'. destruct Hroom as (R1 & R2 & R3).
  unfold cr_room_cf, sb_malloc; cbn [sb_live sb_bytes sb_cap]. repeat split; lia.
Qed.

Lemma room_cm : forall k k', 0 <= k <= 1600 -> 0 <= k' <= 1600 -> cm_room_cf (sb_malloc b k') k.
Proof.
  intros k k' Hkk Hkk'. destruct Hroom as (R1 & R2 & R3).
  unfold cm_room_cf, sb_malloc; cbn [sb_live sb_bytes sb_cap]. repeat split; lia.
Qed.

Lemma room_ci : forall k k', 0 <= k <= 1600 -> 0 <= k' <= 1600 -> ci_room_cf (sb_malloc b k') k.
Proof.
  intros k k' Hkk Hkk'. destruct Hroom as (R1 & R2 & R3).
  unfold ci_room_cf, sb_malloc; cbn [sb_live sb_bytes sb_cap]. repeat split; lia.
Qed.

Lemma f_norm : forall L A mem md Ac cs, lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md ->
  spZ regs0 - stk <= Ac -> Ac + Z.of_nat (cells_size cs) <= spZ regs0 ->
  rw_cells rsegs mem Ac cs -> rw_cells rsegs (normalize rsegs mem) Ac cs.
Proof.
  intros L A mem md Ac cs FR Hlo Hhi HC. pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MI).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5 & B6). pose proof YM05.alloc_ceiling_value as Hac.
  apply (lf_rw_cells_norm B mem Ac cs SEGS MI); [|exact HC].
  intros i Hi Himg. pose proof (lf_in_img_top B _ SEGS Himg). lia.
Qed.

Lemma f_present : forall L A mem md i, lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md ->
  0 <= i < 48 -> present mem (spZ regs0 - 160 + i).
Proof.
  intros L A mem md i FR Hi. pose proof FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hstw & _ & _ & MI).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5 & B6). pose proof YM05.alloc_ceiling_value as Hac.
  apply (lf_present_of_writable B mem _ SEGS).
  - intros Himg. pose proof (lf_in_img_top B _ SEGS Himg). lia.
  - lia.
  - rewrite <- SEGS. apply Hstw. lia.
Qed.

Local Abbreviation Post := (llvm_sr_post B API stk L0 A0 regs0 mem0 md0 ra p n b j).

Lemma sr_entry_cf : frm_zero (@fp_csr fx) ->
  SRcf B (mkCfg (@YK11.mkst fx regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 (YK11.seg_rom (ms_segs B))) md0) Post.
Proof.
  intros Hfrm.
  pose proof BI as (_ & HMAL & HFRE & HGG & HG & _).
  destruct f_bounds as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof YM05.alloc_ceiling_value as Hac.
  pose proof f_p'range as HP'.
  pose proof Hpre as (HM0 & HW0 & HB0 & HID0 & Hra1 & Hal0 & Hceil0 & H630 & Hstw0 & Htp0 & Herr0 & Hp0 & Hn11 &
    Hpl0 & Hrod0).
  pose proof (lf_fr_init B API stk empty L0 A0 regs0 mem0 md0 ra p n Hpre Hro) as FR0.
  assert (HPB : 0 < n -> bytes_at rsegs (normalize rsegs mem0) (bv_unsigned (reg_get regs0 10)) pl).
  { intros Hn0. destruct (f_pay Hn0) as (_ & P1 & P2 & E). rewrite E in *.
    apply bytes_at_normalize; [exact Hro|]. apply (LW.blk_bytes_at B); [exact SEGS | lia | lia | exact Hpd]. }
  assert (HPL : 0 < n -> 4096 <= bv_unsigned (reg_get regs0 10) /\
                         bv_unsigned (reg_get regs0 10) + n <= spZ regs0 - stk).
  { intros Hn0. destruct (f_pay Hn0) as (_ & P1 & P2 & _). lia. }
  pose proof f_pay as PAY.
  remember (bv_unsigned (reg_get regs0 10)) as P' eqn:EP'.
  assert (E10 : reg_get regs0 10 = Z_to_bv 64 P') by (rewrite EP'; symmetry; apply Z_to_bv_bv_unsigned).
  assert (E11 : reg_get regs0 11 = Z_to_bv 64 n) by exact Hn11.
  rewrite SEGS.
  eapply (g_run_cf B API SEGS AX HGG stk (spZ regs0) L0 A0 mem0 md0 fx regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 md0 L0 A0
    (LW.q1 (@fp_regs fx) (@fp_csr fx) (reg_get regs0 3) (reg_get regs0 4) (reg_get regs0 22) (reg_get regs0 23)
        (reg_get regs0 24) (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) (normalize rsegs mem0)
        (spZ regs0 - stk) (spZ regs0 - 160) n P'
        (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18) (reg_get regs0 19)
             (reg_get regs0 20) (reg_get regs0 21)))).
  { exact FR0. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of, LLVM_ENTRY. rewrite E10, E11.
    apply (LW.e1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@fp_regs fx) (@fp_csr fx)
             (normalize rsegs mem0) (spZ regs0 - stk) P' n pl MSET MCPY).
    - apply (f_stk L0 A0 mem0 md0 (spZ regs0) FR0). lia.
    - unfold spZ in *. lia.
    - exact (mem_inv_normalize rsegs mem0).
    - unfold spZ in *. lia.
    - lia.
    - lia.
    - exact HP'.
    - exact Hlen.
    - exact HPB.
    - exact HPL. }
  { intros ms (R & m' & nf & src & slot & w3 & jv & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
      & _ & _ & _ & _ & _ & _ & MU & WM & _).
    do 5 eexists. exists [(spZ regs0 - 160, spZ regs0 - 160 + 160)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply en_out1 in NO. lia. }
  intros R F pc' fc m0' HQ regs1 m1 Hx1 Hrel1 FR1.
  destruct HQ as (R' & m'' & nf & src & slot & w3 & jv & HE & R1 & R2 & R3 & R4 & R8 & R9 & R10 & R18 & R19 & R20 &
    R21 & R22 & R23 & R24 & R25 & R26 & R27 & Hnf & Hsrc & Hslot & Hjv & MU & WM & MI & ST & FV & FS).
  injection HE as ER EF EP EC EM. subst R' F pc' fc m''.
  xr Hx1 R1 F1. xr Hx1 R2 F2. xr Hx1 R3 F3. xr Hx1 R4 F4. xr Hx1 R8 F8. xr Hx1 R9 F9. xr Hx1 R10 F10.
  xr Hx1 R18 F18. xr Hx1 R19 F19. xr Hx1 R20 F20. xr Hx1 R21 F21. xr Hx1 R22 F22. xr Hx1 R23 F23. xr Hx1 R24 F24.
  xr Hx1 R25 F25. xr Hx1 R26 F26. xr Hx1 R27 F27.
  clear R1 R2 R3 R4 R8 R9 R10 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27.
  pose proof (lf_rw_cells_rel m1 m0' _ _ Hrel1 FV) as FV1.
  pose proof (lf_rw_cells_rel m1 m0' _ _ Hrel1 FS) as FS1.
  clear FV FS ST MI MU WM.
  assert (Hsp1 : spZ regs1 = spZ regs0 - 160)
    by (unfold spZ at 1; change (YK11.getr regs1 2) with (reg_get regs1 2); rewrite F2;
        apply MState.unsigned_lit; lia).
  assert (Hnf0 : 0 <= nf <= 1600) by lia.
  set (nf' := if nf =? 0 then 1 else nf) in *.
  assert (Hnf' : nf' = Z.max nf 1) by (unfold nf'; destruct (Z.eqb_spec nf 0); lia).
  rewrite <- SEGS. change (Z_to_bv 64 0x14240) with (Z_to_bv 64 LLVM_MALLOC).
  eapply (g_malloc_cf B API SEGS AX ERRNO_LOW HMAL MALLOC stk (spZ regs0) L0 A0 mem0 md0
            (mkFP (@fp_regs fx) (@fp_csr fx)) regs1 m1 md0 L0 A0 nf' b).
  { exact FR1. } { lia. } { lia. }
  { change (YK11.getr regs1 1) with (reg_get regs1 1). rewrite F1. apply ret_ok_even. reflexivity. }
  { rewrite Hsp1. replace (spZ regs0 - 160) with (spZ regs0 + (-10) * 16) by lia. rewrite Z.mod_add by lia.
    exact B3. }
  { rewrite Hsp1. unfold ALLOC_STACK. pose proof Hk as Hk'.
    unfold LLVM_K, LLVM_FRAME, CHECK_INJECT_STACK, CHECK_INJECT_FRAME, ALLOC_STACK in Hk'. lia. }
  { lia. } { lia. }
  { change (YK11.getr regs1 4) with (reg_get regs1 4). rewrite F4. exact Htp0. }
  { exact F10. }
  { exact Hres0. }
  { apply room_ag_b. unfold nf'. destruct (Z.eqb_spec nf 0); lia. }
  intros L1 A1 regs2 mem2 md2 f FR2 Hrp2 G210 Hf1 Hf2 Hf16 Hnimg (b1 & b2 & Eb1 & Eb2) Hres2 Habove2 Hkept2.
  (* the payload block and the fresh block are disjoint *)
  assert (MINE : forall a k, In (a, k) (blocks L0 A0) -> a + k <= f \/ f + nf' <= a).
  { intros a k Hak.
    assert (PW : pairwise ranges_disjoint (b1 ++ (f, nf') :: b2)).
    { rewrite <- Eb1. pose proof FR2 as (HM2 & _).
      exact (mr_blocks_disjoint B _ (aa_laws API) L1 A1 mem2 md2 HM2). }
    rewrite Eb2 in Hak. pose proof (LW.disj_mid b1 (f, nf') b2 (a, k) PW Hak) as H. cbn [fst snd] in H. lia. }
  assert (Hfin : In (f, nf') (blocks L1 A1)) by (rewrite Eb1; apply in_or_app; right; left; reflexivity).
  assert (Hnf'0 : 0 < nf' <= 1600) by (unfold nf' in *; destruct (Z.eqb_spec nf 0); lia).
  pose proof FR2 as (HM2 & HW2 & HB2 & HID2 & _ & _ & _ & Hblk2 & Hbyt2 & Hstw2 & Herr2 & _ & Hro2).
  destruct (LW.norm_blk B API SEGS AX L1 A1 mem2 md2 f nf' HM2 Hfin ltac:(lia) Hro2) as [junk FB2].
  (* the slice of the payload the copy reads *)
  set (sbs := firstn (Z.to_nat nf) (skipn 53 pl)) in *.
  assert (Hsbs : Z.of_nat (length sbs) = nf).
  { unfold sbs. rewrite firstn_length_le; [lia|]. rewrite length_skipn.
    destruct (Z.eq_dec nf 0) as [E0|E0]; [lia|]. lia. }
  assert (HSB : 0 < nf -> bytes_at rsegs (normalize rsegs mem2) src sbs).
  { intros Hnfp.
    assert (Hn0 : 0 < n) by lia.
    destruct (PAY Hn0) as (Hin0 & P1 & P2 & Ep).
    assert (BD : blk_data B mem2 P' pl).
    { apply (LW.blk_keep B API stk (spZ regs0) L0 A0 mem0 md0 L1 A1 mem2 md2 P' pl FR2); [| rewrite Ep; exact Hpd].
      rewrite <- Hlen. exact Hin0. }
    assert (BA : bytes_at rsegs (normalize rsegs mem2) P' pl).
    { apply bytes_at_normalize; [exact Hro2|]. apply (LW.blk_bytes_at B); [exact SEGS | lia | lia | exact BD]. }
    rewrite <- (firstn_skipn 53 pl) in BA. apply bytes_at_app in BA as [_ BA].
    rewrite firstn_length_le in BA by lia.
    unfold sbs. rewrite <- (firstn_skipn (Z.to_nat nf) (skipn 53 pl)) in BA.
    apply bytes_at_app in BA as [BA _].
    assert (Esrc : src = P' + Z.of_nat 53).
    { rewrite Hsrc. destruct (Z.ltb_spec n 54) as [H54|H54]; [lia | lia]. }
    rewrite Esrc. exact BA. }
  assert (FS2 : rw_cells rsegs mem2 (spZ regs0 - 160 + 104)
                  (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18) (reg_get regs0 19)
                       (reg_get regs0 20) (reg_get regs0 21))).
  { apply (LW.lf_rw_cells_frame m1); [exact FS1|]. intros a Ha.
    cbn [cells_size csize lsv] in Ha. rewrite <- SEGS. apply Habove2. rewrite Hsp1. lia. }
  pose proof (f_norm L1 A1 mem2 md2 (spZ regs0 - 160 + 104)
                (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18) (reg_get regs0 19)
                     (reg_get regs0 20) (reg_get regs0 21)) FR2 ltac:(lia)
                ltac:(cbn [cells_size csize lsv]; lia) FS2) as FS2n.
  pz Hrp2 F2 2 P2. pz Hrp2 F3 3 P3. pz Hrp2 F4 4 P4. pz Hrp2 F8 8 P8. pz Hrp2 F9 9 P9. pz Hrp2 F18 18 P18.
  pz Hrp2 F19 19 P19. pz Hrp2 F20 20 P20. pz Hrp2 F21 21 P21. pz Hrp2 F22 22 P22. pz Hrp2 F23 23 P23.
  pz Hrp2 F24 24 P24. pz Hrp2 F25 25 P25. pz Hrp2 F26 26 P26. pz Hrp2 F27 27 P27.
  assert (Q2 : reg_get regs2 2 = Z_to_bv 64 (spZ regs0 - 160)) by exact P2.
  assert (Q3 : reg_get regs2 3 = reg_get regs0 3) by exact P3.
  assert (Q4 : reg_get regs2 4 = reg_get regs0 4) by exact P4.
  assert (Q8 : reg_get regs2 8 = Z_to_bv 64 n) by exact P8.
  assert (Q9 : reg_get regs2 9 = Z_to_bv 64 P') by exact P9.
  assert (Q18 : reg_get regs2 18 = Z_to_bv 64 slot) by exact P18.
  assert (Q19 : reg_get regs2 19 = w3) by exact P19.
  assert (Q20 : reg_get regs2 20 = Z_to_bv 64 nf) by exact P20.
  assert (Q21 : reg_get regs2 21 = Z_to_bv 64 src) by exact P21.
  assert (Q22 : reg_get regs2 22 = reg_get regs0 22) by exact P22.
  assert (Q23 : reg_get regs2 23 = reg_get regs0 23) by exact P23.
  assert (Q24 : reg_get regs2 24 = reg_get regs0 24) by exact P24.
  assert (Q25 : reg_get regs2 25 = reg_get regs0 25) by exact P25.
  assert (Q26 : reg_get regs2 26 = reg_get regs0 26) by exact P26.
  assert (Q27 : reg_get regs2 27 = reg_get regs0 27) by exact P27.
  assert (G22 : YK11.getr regs2 2 = Z_to_bv 64 (spZ regs0 - 160)) by exact P2.
  assert (Hsp2 : spZ regs2 = spZ regs0 - 160)
    by (unfold spZ at 1; rewrite G22; apply MState.unsigned_lit; lia).
  rewrite SEGS.
  eapply (g_run_cf B API SEGS AX HGG stk (spZ regs0) L0 A0 mem0 md0 (mkFP (@fp_regs fx) (@fp_csr fx)) regs2
            (YK11.getr regs1 1) mem2 md2 L1 A1
    (LW.q2 (@fp_regs fx) (@fp_csr fx) (reg_get regs0 3) (reg_get regs0 4) (reg_get regs0 22) (reg_get regs0 23)
        (reg_get regs0 24) (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) w3
        (normalize rsegs mem2) (spZ regs0 - 160) n nf nf' f src slot (lsv (reg_get regs0 1) (reg_get regs0 8)
          (reg_get regs0 9) (reg_get regs0 18) (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)))).
  { exact FR2. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. change (YK11.getr regs1 1) with (reg_get regs1 1). rewrite F1.
    assert (Q10 : reg_get regs2 10 = Z_to_bv 64 f) by exact G210.
    rewrite Q2, Q3, Q4, Q8, Q9, Q10, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27.
    apply (s1e _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@fp_regs fx) (@fp_csr fx)
             (normalize rsegs mem2) (spZ regs0 - 160) (spZ regs0 - stk) n P' nf nf' f src sbs junk _ MCPY).
    - lia.
    - lia.
    - lia.
    - exact Hnf'.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite Hsrc. destruct (n <? 54); lia.
    - rewrite Hsrc. destruct (Z.ltb_spec n 54) as [H54|H54]; [lia|].
      destruct (PAY ltac:(lia)) as (_ & _ & Pc & _). lia.
    - destruct (Z.eq_dec nf 0) as [E0|E0]; [lia|].
      destruct (PAY ltac:(lia)) as (Hin0 & P1 & Pc & _).
      destruct (MINE P' n Hin0); [left | right]; rewrite Hsrc;
        destruct (Z.ltb_spec n 54) as [H54|H54]; lia.
    - exact HSB.
    - exact Hsbs.
    - exact FB2.
    - exact (mem_inv_normalize rsegs mem2).
    - intros m4 y5 y6 y7 y13 y14 y15 y16 y17 y28 y29 y30 y31 junk' MU4 WM4 MI4 FB4.
      apply evt_done. unfold LW.q2. do 2 eexists; exists junk'.
      split; [reflexivity|]. do 19 (split; [reflexivity|]).
      split; [exact MU4|]. split; [exact WM4|]. split; [exact MI4|]. split; [exact FB4|].
      eapply rw_cells_transport; [exact FS2n | exact MU4 | exact WM4 |].
      cbn [disjoint_from cells_size csize lsv]. split; [lia | exact I]. }
  { intros ms (Rq & mq & junkq & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
      MU & WM & _ & _ & _).
    do 5 eexists. exists [(f, f + nf')].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. right. exists f, nf'. split; [| apply en_out1 in NO; lia].
    unfold lf_mine. split; [exact Hfin|]. split; [lia | exact MINE]. }
  intros R2 F2' pc2 fc2 m2' HQ2 regs3 m3 Hx3 Hrel3 FR3.
  destruct HQ2 as (Ra & ma & junk2 & HEa & S1 & S2 & S3 & S4 & S8 & S9 & S10 & S11 & S12 & S18 & S19 & S20 & S21 &
    S22 & S23 & S24 & S25 & S26 & S27 & MUa & WMa & MIa & FBa & FSa).
  injection HEa as ERa EFa EPa ECa EMa. subst Ra F2' pc2 fc2 ma.
  xr Hx3 S1 T1. xr Hx3 S2 T2. xr Hx3 S3 T3. xr Hx3 S4 T4. xr Hx3 S8 T8. xr Hx3 S9 T9. xr Hx3 S10 T10.
  xr Hx3 S11 T11. xr Hx3 S12 T12. xr Hx3 S18 T18. xr Hx3 S19 T19. xr Hx3 S20 T20. xr Hx3 S21 T21. xr Hx3 S22 T22.
  xr Hx3 S23 T23. xr Hx3 S24 T24. xr Hx3 S25 T25. xr Hx3 S26 T26. xr Hx3 S27 T27.
  pose proof (lf_rw_cells_rel m3 _ _ _ Hrel3 FSa) as FS3.
  assert (Hsp3 : spZ regs3 = spZ regs0 - 160)
    by (unfold spZ at 1; change (YK11.getr regs3 2) with (reg_get regs3 2); rewrite T2;
        apply MState.unsigned_lit; lia).
  assert (Hib : in_block L1 A1 f nf) by (exists f, nf'; split; [exact Hfin | lia]).
  assert (HTP3 : YK11.getr regs3 4 = Z_to_bv 64 (ms_tp B))
    by (change (YK11.getr regs3 4) with (reg_get regs3 4); rewrite T4; exact Htp0).
  (* check_restamp *)
  rewrite <- SEGS. change (Z_to_bv 64 0x12e58) with (Z_to_bv 64 CHECK_RESTAMP).
  eapply (g_crs_cf B API SEGS AX ERRNO_LOW stk (spZ regs0) L0 A0 mem0 md0 (mkFP (@fp_regs fx) (@fp_csr fx)) regs3 m3
            md2 L1 A1 f nf (bv_unsigned w3) (sb_malloc b nf')).
  { exact CRS. } { exact FR3. } { lia. } { lia. }
  { change (YK11.getr regs3 1) with (reg_get regs3 1). rewrite T1. apply ret_ok_even. reflexivity. }
  { rewrite Hsp3. replace (spZ regs0 - 160) with (spZ regs0 + (-10) * 16) by lia. rewrite Z.mod_add by lia.
    exact B3. }
  { rewrite Hsp3. unfold CHECK_RESTAMP_STACK, CR_FRAME, ALLOC_STACK. lia. }
  { lia. } { lia. } { exact HTP3. }
  { change (YK11.getr regs3 10) with (reg_get regs3 10). exact T10. }
  { change (YK11.getr regs3 11) with (reg_get regs3 11). exact T11. }
  { change (YK11.getr regs3 12) with (reg_get regs3 12). rewrite T12. symmetry. apply Z_to_bv_bv_unsigned. }
  { lia. } { exact Hib. } { exact Hfrm. } { exact Hres2. } { apply room_cr; lia. }
  intros fx4 L2 A2 regs4 mem4 md4 Hfrm4 FR4 Hrp4 Eb4 Hres4 Habove4 Hkept4.
  (* check_mute *)
  pz Hrp4 T18 18 U18. pz Hrp4 T2 2 U2. pz Hrp4 T3 3 U3. pz Hrp4 T4 4 U4. pz Hrp4 T8 8 U8. pz Hrp4 T9 9 U9. pz Hrp4 T19 19 U19.
  pz Hrp4 T20 20 U20. pz Hrp4 T21 21 U21. pz Hrp4 T22 22 U22. pz Hrp4 T23 23 U23. pz Hrp4 T24 24 U24.
  pz Hrp4 T25 25 U25. pz Hrp4 T26 26 U26. pz Hrp4 T27 27 U27.
  assert (V2 : reg_get regs4 2 = Z_to_bv 64 (spZ regs0 - 160)) by exact U2.
  assert (V3 : reg_get regs4 3 = reg_get regs0 3) by exact U3.
  assert (V4 : reg_get regs4 4 = reg_get regs0 4) by exact U4.
  assert (V8 : reg_get regs4 8 = Z_to_bv 64 n) by exact U8.
  assert (V9 : reg_get regs4 9 = Z_to_bv 64 f) by exact U9.
  assert (V19 : reg_get regs4 19 = w3) by exact U19.
  assert (V20 : reg_get regs4 20 = Z_to_bv 64 nf) by exact U20.
  assert (V21 : reg_get regs4 21 = Z_to_bv 64 src) by exact U21.
  assert (V22 : reg_get regs4 22 = reg_get regs0 22) by exact U22.
  assert (V23 : reg_get regs4 23 = reg_get regs0 23) by exact U23.
  assert (V24 : reg_get regs4 24 = reg_get regs0 24) by exact U24.
  assert (V25 : reg_get regs4 25 = reg_get regs0 25) by exact U25.
  assert (V26 : reg_get regs4 26 = reg_get regs0 26) by exact U26.
  assert (V27 : reg_get regs4 27 = reg_get regs0 27) by exact U27.
  assert (V18 : reg_get regs4 18 = Z_to_bv 64 slot) by exact U18.
  assert (FS4 : rw_cells rsegs mem4 (spZ regs0 - 160 + 104) (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21))).
  { apply (LW.lf_rw_cells_frame m3); [exact FS3|]. intros a Ha.
    cbn [cells_size csize lsv] in Ha. rewrite <- SEGS. apply Habove4. rewrite Hsp3. lia. }
  pose proof (f_norm L2 A2 mem4 md4 (spZ regs0 - 160 + 104) (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)) FR4 ltac:(lia)
                ltac:(cbn [cells_size csize lsv]; lia) FS4) as FS4n.
  rewrite SEGS.
  eapply (g_run_cf B API SEGS AX HGG stk (spZ regs0) L0 A0 mem0 md0 fx4 regs4 (YK11.getr regs3 1) mem4 md4 L2 A2
    (LW.qmute (@fp_regs fx4) (@fp_csr fx4) (reg_get regs0 3) (reg_get regs0 4) (reg_get regs0 22) (reg_get regs0 23)
       (reg_get regs0 24) (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) w3 (normalize rsegs mem4)
       (spZ regs0 - 160) n nf f slot (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)))).
  { exact FR4. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. change (YK11.getr regs3 1) with (reg_get regs3 1). rewrite T1.
    rewrite V2, V3, V4, V8, V9, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27.
    apply (s1f _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@fp_regs fx4) (@fp_csr fx4)
             (normalize rsegs mem4) (spZ regs0 - 160) nf f).
    apply evt_done. unfold LW.qmute. eexists.
    split; [reflexivity|]. do 17 (split; [reflexivity|]). exact FS4n. }
  { intros ms (Rq & ->  & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    do 5 eexists. exists (@nil (Z * Z)).
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    intros x Hx NO. exfalso. apply NO. exact I. }
  intros R5 Ff5 pc5 fc5 m5' HQ5 regs5 m5 Hx5 Hrel5 FR5.
  destruct HQ5 as (Rb & HEb & W1 & W2 & W3 & W4 & W8 & W9 & W10 & W11 & W18 & W19 & W20 & W22 & W23 & W24 & W25 &
    W26 & W27 & FSb).
  injection HEb as ERb EFb EPb ECb EMb. subst Rb Ff5 pc5 fc5 m5'.
  xr Hx5 W1 X1. xr Hx5 W2 X2. xr Hx5 W3 X3. xr Hx5 W4 X4. xr Hx5 W8 X8. xr Hx5 W9 X9. xr Hx5 W10 X10.
  xr Hx5 W11 X11. xr Hx5 W18 X18. xr Hx5 W19 X19. xr Hx5 W20 X20. xr Hx5 W22 X22. xr Hx5 W23 X23.
  xr Hx5 W24 X24. xr Hx5 W25 X25. xr Hx5 W26 X26. xr Hx5 W27 X27.
  pose proof (lf_rw_cells_rel m5 _ _ _ Hrel5 FSb) as FS5.
  assert (Hsp5 : spZ regs5 = spZ regs0 - 160)
    by (unfold spZ at 1; change (YK11.getr regs5 2) with (reg_get regs5 2); rewrite X2;
        apply MState.unsigned_lit; lia).
  assert (Hib5 : in_block L2 A2 f nf) by (exists f, nf'; split; [rewrite Eb4; exact Hfin | lia]).
  rewrite <- SEGS. change (Z_to_bv 64 0x12f50) with (Z_to_bv 64 CHECK_MUTE).
  eapply (g_cm_cf B API SEGS AX ERRNO_LOW stk (spZ regs0) L0 A0 mem0 md0 (mkFP (@fp_regs fx4) (@fp_csr fx4)) regs5 m5
            md4 L2 A2 f nf (sb_malloc b nf')).
  { exact CM. } { exact FR5. } { lia. } { lia. }
  { change (YK11.getr regs5 1) with (reg_get regs5 1). rewrite X1. apply ret_ok_even. reflexivity. }
  { rewrite Hsp5. replace (spZ regs0 - 160) with (spZ regs0 + (-10) * 16) by lia. rewrite Z.mod_add by lia.
    exact B3. }
  { rewrite Hsp5. unfold CHECK_MUTE_STACK, CHECK_MUTE_FRAME, ALLOC_STACK. lia. }
  { lia. } { lia. }
  { change (YK11.getr regs5 4) with (reg_get regs5 4). rewrite X4. exact Htp0. }
  { change (YK11.getr regs5 10) with (reg_get regs5 10). exact X10. }
  { change (YK11.getr regs5 11) with (reg_get regs5 11). exact X11. }
  { lia. } { exact Hib5. } { exact Hfrm4. } { exact Hres4. } { apply room_cm; lia. }
  intros fx6 L3 A3 regs6 mem6 md6 Hfrm6 FR6 Hrp6 Eb6 Hres6 Habove6 Hkept6.
  (* check_gate (an evt leaf) and check_inject *)
  pz Hrp6 X2 2 Y2. pz Hrp6 X3 3 Y3. pz Hrp6 X4 4 Y4. pz Hrp6 X8 8 Y8. pz Hrp6 X9 9 Y9. pz Hrp6 X18 18 Y18.
  pz Hrp6 X19 19 Y19. pz Hrp6 X20 20 Y20. pz Hrp6 X22 22 Y22. pz Hrp6 X23 23 Y23. pz Hrp6 X24 24 Y24.
  pz Hrp6 X25 25 Y25. pz Hrp6 X26 26 Y26. pz Hrp6 X27 27 Y27.
  assert (Z2 : reg_get regs6 2 = Z_to_bv 64 (spZ regs0 - 160)) by exact Y2.
  assert (Z3 : reg_get regs6 3 = reg_get regs0 3) by exact Y3.
  assert (Z4 : reg_get regs6 4 = reg_get regs0 4) by exact Y4.
  assert (Z8 : reg_get regs6 8 = Z_to_bv 64 n) by exact Y8.
  assert (Z9 : reg_get regs6 9 = Z_to_bv 64 f) by exact Y9.
  assert (Z18 : reg_get regs6 18 = Z_to_bv 64 slot) by exact Y18.
  assert (Z19 : reg_get regs6 19 = w3) by exact Y19.
  assert (Z20 : reg_get regs6 20 = Z_to_bv 64 nf) by exact Y20.
  assert (Z22 : reg_get regs6 22 = reg_get regs0 22) by exact Y22.
  assert (Z23 : reg_get regs6 23 = reg_get regs0 23) by exact Y23.
  assert (Z24 : reg_get regs6 24 = reg_get regs0 24) by exact Y24.
  assert (Z25 : reg_get regs6 25 = reg_get regs0 25) by exact Y25.
  assert (Z26 : reg_get regs6 26 = reg_get regs0 26) by exact Y26.
  assert (Z27 : reg_get regs6 27 = reg_get regs0 27) by exact Y27.
  assert (FS6 : rw_cells rsegs mem6 (spZ regs0 - 160 + 104) (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21))).
  { apply (LW.lf_rw_cells_frame m5); [exact FS5|]. intros a Ha.
    cbn [cells_size csize lsv] in Ha. rewrite <- SEGS. apply Habove6. rewrite Hsp5. lia. }
  pose proof (f_norm L3 A3 mem6 md6 (spZ regs0 - 160 + 104) (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)) FR6 ltac:(lia)
                ltac:(cbn [cells_size csize lsv]; lia) FS6) as FS6n.
  assert (Hfin6 : In (f, nf') (blocks L3 A3)) by (rewrite Eb6, Eb4; exact Hfin).
  pose proof FR6 as (HM6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro6).
  destruct (LW.norm_blk B API SEGS AX L3 A3 mem6 md6 f nf' HM6 Hfin6 ltac:(lia) Hro6) as [junk6 FB6].
  destruct (rwc_cb_inv rsegs (normalize rsegs mem6) f (Z.to_nat nf') junk6 FB6) as (Hj6 & BB6 & _).
  assert (BBn : bytes_at rsegs (normalize rsegs mem6) f (firstn (Z.to_nat nf) junk6)).
  { rewrite <- (firstn_skipn (Z.to_nat nf) junk6) in BB6. apply bytes_at_app in BB6 as [BB6 _]. exact BB6. }
  assert (Hbn : Z.of_nat (length (firstn (Z.to_nat nf) junk6)) = nf)
    by (rewrite firstn_length_le; lia).
  rewrite SEGS.
  eapply (g_run_cf B API SEGS AX HGG stk (spZ regs0) L0 A0 mem0 md0 fx6 regs6 (YK11.getr regs5 1) mem6 md6 L3 A3
    (LW.q4 (@fp_regs fx6) (@fp_csr fx6) (reg_get regs0 3) (reg_get regs0 4) (reg_get regs0 22) (reg_get regs0 23)
       (reg_get regs0 24) (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) w3 (normalize rsegs mem6)
       (spZ regs0 - 160) (spZ regs0 - stk) n nf f slot (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)))).
  { exact FR6. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. change (YK11.getr regs5 1) with (reg_get regs5 1). rewrite X1.
    rewrite Z2, Z3, Z4, Z8, Z9, Z18, Z19, Z20, Z22, Z23, Z24, Z25, Z26, Z27.
    apply (s1g _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@fp_regs fx6) (@fp_csr fx6)
             (normalize rsegs mem6) (spZ regs0 - 160) (spZ regs0 - stk) nf f slot
             (firstn (Z.to_nat nf) junk6) _ CG).
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact BBn.
    - exact Hbn.
    - exact (mem_inv_normalize rsegs mem6).
    - apply (f_stk L3 A3 mem6 md6 (spZ regs0 - 160) FR6). lia.
    - intros m7 y5 y6 y7 y14 y15 y16 y17 y28 y29 y30 y31 MU7 WM7 MI7 ST7.
      apply evt_done. unfold LW.q4. eexists; eexists.
      split; [reflexivity|]. do 19 (split; [reflexivity|]).
      split; [exact MU7|]. split; [exact WM7|]. split; [exact MI7|]. split; [exact ST7|].
      eapply rw_cells_transport; [exact FS6n | exact MU7 | exact WM7 |].
      cbn [disjoint_from cells_size csize lsv]. split; [lia | exact I]. }
  { intros ms (Rq & mq & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MU & WM &
      _ & _ & _).
    do 5 eexists. exists [(spZ regs0 - 160 - 80, spZ regs0 - 160)].
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    intros x Hx NO. left. apply en_out1 in NO. lia. }
  intros R7 Ff7 pc7 fc7 m7' HQ7 regs7 m7 Hx7 Hrel7 FR7.
  destruct HQ7 as (Rc & mc & HEc & C1 & C2 & C3 & C4 & C8 & C9 & C10 & C11 & C12 & C13 & C18 & C19 & C20 & C22 &
    C23 & C24 & C25 & C26 & C27 & MUc & WMc & MIc & STc & FSc).
  injection HEc as ERc EFc EPc ECc EMc. subst Rc Ff7 pc7 fc7 mc.
  xr Hx7 C1 D1. xr Hx7 C2 D2. xr Hx7 C3 D3. xr Hx7 C4 D4. xr Hx7 C8 D8. xr Hx7 C9 D9. xr Hx7 C10 D10.
  xr Hx7 C11 D11. xr Hx7 C12 D12. xr Hx7 C13 D13. xr Hx7 C18 D18. xr Hx7 C19 D19. xr Hx7 C20 D20.
  xr Hx7 C22 D22. xr Hx7 C23 D23. xr Hx7 C24 D24. xr Hx7 C25 D25. xr Hx7 C26 D26. xr Hx7 C27 D27.
  pose proof (lf_rw_cells_rel m7 _ _ _ Hrel7 FSc) as FS7.
  assert (Hsp7 : spZ regs7 = spZ regs0 - 160)
    by (unfold spZ at 1; change (YK11.getr regs7 2) with (reg_get regs7 2); rewrite D2;
        apply MState.unsigned_lit; lia).
  rewrite <- SEGS. change (Z_to_bv 64 0x130b0) with (Z_to_bv 64 CHECK_INJECT).
  eapply (g_ci_cf B API SEGS AX ERRNO_LOW stk (spZ regs0) L0 A0 mem0 md0 (mkFP (@fp_regs fx6) (@fp_csr fx6)) regs7 m7
            md6 L3 A3 f nf slot (spZ regs0 - 160) (sb_malloc b nf')).
  { exact CI. } { exact FR7. } { lia. } { lia. }
  { change (YK11.getr regs7 1) with (reg_get regs7 1). rewrite D1. apply ret_ok_even. reflexivity. }
  { rewrite Hsp7. replace (spZ regs0 - 160) with (spZ regs0 + (-10) * 16) by lia. rewrite Z.mod_add by lia.
    exact B3. }
  { rewrite Hsp7. unfold CHECK_INJECT_STACK, CHECK_INJECT_FRAME, ALLOC_STACK. pose proof Hk as Hk'.
    unfold LLVM_K, LLVM_FRAME, CHECK_INJECT_STACK, CHECK_INJECT_FRAME, ALLOC_STACK in Hk'. lia. }
  { lia. } { lia. }
  { change (YK11.getr regs7 4) with (reg_get regs7 4). rewrite D4. exact Htp0. }
  { change (YK11.getr regs7 10) with (reg_get regs7 10). exact D10. }
  { change (YK11.getr regs7 11) with (reg_get regs7 11). exact D11. }
  { change (YK11.getr regs7 12) with (reg_get regs7 12). exact D12. }
  { change (YK11.getr regs7 13) with (reg_get regs7 13). exact D13. }
  { lia. } { lia. }
  { exists f, nf'. split; [rewrite Eb6, Eb4; exact Hfin | lia]. }
  { rewrite Hsp7. lia. }
  { lia. }
  { replace (spZ regs0 - 160) with (spZ regs0 + (-40) * 4) by lia.
    rewrite Z.mod_add by lia. Z.div_mod_to_equations. lia. }
  { intros i Hi. exact (f_present L3 A3 m7 md6 i FR7 Hi). }
  { exact Hfrm6. } { exact Hres6. } { apply room_ci; lia. }
  intros fx8 L4 A4 regs8 mem8 md8 Hfrm8 FR8 Hrp8 Eb8 Hres8 Habove8 Hkept8.
  (* free(f) *)
  pz Hrp8 D2 2 Ea2. pz Hrp8 D3 3 Ea3. pz Hrp8 D4 4 Ea4. pz Hrp8 D8 8 Ea8. pz Hrp8 D9 9 Ea9.
  pz Hrp8 D18 18 Ea18. pz Hrp8 D19 19 Ea19. pz Hrp8 D20 20 Ea20. pz Hrp8 D22 22 Ea22. pz Hrp8 D23 23 Ea23.
  pz Hrp8 D24 24 Ea24. pz Hrp8 D25 25 Ea25. pz Hrp8 D26 26 Ea26. pz Hrp8 D27 27 Ea27.
  assert (Fa2 : reg_get regs8 2 = Z_to_bv 64 (spZ regs0 - 160)) by exact Ea2.
  assert (Fa3 : reg_get regs8 3 = reg_get regs0 3) by exact Ea3.
  assert (Fa4 : reg_get regs8 4 = reg_get regs0 4) by exact Ea4.
  assert (Fa8 : reg_get regs8 8 = Z_to_bv 64 n) by exact Ea8.
  assert (Fa9 : reg_get regs8 9 = Z_to_bv 64 f) by exact Ea9.
  assert (Fa18 : reg_get regs8 18 = Z_to_bv 64 slot) by exact Ea18.
  assert (Fa19 : reg_get regs8 19 = w3) by exact Ea19.
  assert (Fa20 : reg_get regs8 20 = Z_to_bv 64 nf) by exact Ea20.
  assert (Fa22 : reg_get regs8 22 = reg_get regs0 22) by exact Ea22.
  assert (Fa23 : reg_get regs8 23 = reg_get regs0 23) by exact Ea23.
  assert (Fa24 : reg_get regs8 24 = reg_get regs0 24) by exact Ea24.
  assert (Fa25 : reg_get regs8 25 = reg_get regs0 25) by exact Ea25.
  assert (Fa26 : reg_get regs8 26 = reg_get regs0 26) by exact Ea26.
  assert (Fa27 : reg_get regs8 27 = reg_get regs0 27) by exact Ea27.
  assert (FS8 : rw_cells rsegs mem8 (spZ regs0 - 160 + 104) (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21))).
  { apply (LW.lf_rw_cells_frame m7); [exact FS7|]. intros a Ha.
    cbn [cells_size csize lsv] in Ha. rewrite <- SEGS. apply Habove8. rewrite Hsp7. lia. }
  pose proof (f_norm L4 A4 mem8 md8 (spZ regs0 - 160 + 104) (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)) FR8 ltac:(lia)
                ltac:(cbn [cells_size csize lsv]; lia) FS8) as FS8n.
  rewrite SEGS.
  eapply (g_run_cf B API SEGS AX HGG stk (spZ regs0) L0 A0 mem0 md0 fx8 regs8 (YK11.getr regs7 1) mem8 md8 L4 A4
    (LW.qfree (@fp_regs fx8) (@fp_csr fx8) (reg_get regs0 3) (reg_get regs0 4) (Z_to_bv 64 n) (Z_to_bv 64 f)
       (Z_to_bv 64 slot) w3 (Z_to_bv 64 nf) (reg_get regs0 22) (reg_get regs0 23)
       (reg_get regs0 24) (reg_get regs0 25) (reg_get regs0 26) (reg_get regs0 27) (normalize rsegs mem8)
       (spZ regs0 - 160) f (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)))).
  { exact FR8. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. change (YK11.getr regs7 1) with (reg_get regs7 1). rewrite D1.
    rewrite Fa2, Fa3, Fa4, Fa8, Fa9, Fa18, Fa19, Fa20, Fa22, Fa23, Fa24, Fa25, Fa26, Fa27.
    apply (s1h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@fp_regs fx8) (@fp_csr fx8)
             (normalize rsegs mem8) (spZ regs0 - 160) f).
    apply evt_done. unfold LW.qfree. eexists.
    split; [reflexivity|]. do 16 (split; [reflexivity|]). exact FS8n. }
  { intros ms (Rq & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    do 5 eexists. exists (@nil (Z * Z)).
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    intros x Hx NO. exfalso. apply NO. exact I. }
  intros R9 Ff9 pc9 fc9 m9' HQ9 regs9 m9 Hx9 Hrel9 FR9.
  destruct HQ9 as (Rd & HEd & I1 & I2 & I3 & I4 & I8 & I9 & I10 & I18 & I19 & I20 & I22 & I23 & I24 & I25 &
    I26 & I27 & FSd).
  injection HEd as ERd EFd EPd ECd EMd. subst Rd Ff9 pc9 fc9 m9'.
  xr Hx9 I1 J1. xr Hx9 I2 J2. xr Hx9 I3 J3. xr Hx9 I4 J4. xr Hx9 I8 J8. xr Hx9 I9 J9. xr Hx9 I10 J10.
  xr Hx9 I18 J18. xr Hx9 I19 J19. xr Hx9 I20 J20. xr Hx9 I22 J22. xr Hx9 I23 J23.
  xr Hx9 I24 J24. xr Hx9 I25 J25. xr Hx9 I26 J26. xr Hx9 I27 J27.
  pose proof (lf_rw_cells_rel m9 _ _ _ Hrel9 FSd) as FS9.
  assert (Hsp9 : spZ regs9 = spZ regs0 - 160)
    by (unfold spZ at 1; change (YK11.getr regs9 2) with (reg_get regs9 2); rewrite J2;
        apply MState.unsigned_lit; lia).
  rewrite <- SEGS. change (Z_to_bv 64 0x14100) with (Z_to_bv 64 LLVM_FREE).
  eapply (g_free_cf B API SEGS AX ERRNO_LOW HFRE FREE stk (spZ regs0) L0 A0 mem0 md0
            (mkFP (@fp_regs fx8) (@fp_csr fx8)) regs9 m9 md8 L4 A4 f nf' (sb_malloc b nf')).
  { exact FR9. } { lia. } { lia. }
  { change (YK11.getr regs9 1) with (reg_get regs9 1). rewrite J1. apply ret_ok_even. reflexivity. }
  { rewrite Hsp9. replace (spZ regs0 - 160) with (spZ regs0 + (-10) * 16) by lia. rewrite Z.mod_add by lia.
    exact B3. }
  { rewrite Hsp9. unfold ALLOC_STACK. pose proof Hk as Hk'.
    unfold LLVM_K, LLVM_FRAME, CHECK_INJECT_STACK, CHECK_INJECT_FRAME, ALLOC_STACK in Hk'. lia. }
  { lia. } { lia. }
  { change (YK11.getr regs9 4) with (reg_get regs9 4). rewrite J4. exact Htp0. }
  { change (YK11.getr regs9 10) with (reg_get regs9 10). exact J10. }
  { rewrite Eb8, Eb6, Eb4. exact Hfin. }
  { lia. }
  { exact MINE. }
  { exact Hres8. }
  intros L5 A5 regs10 mem10 md10 FR10 Hrp10 (c1 & c2 & Ec1 & Ec2) Hres10 Habove10 Hkept10.
  (* the epilogue *)
  pz Hrp10 J2 2 K2. pz Hrp10 J3 3 K3. pz Hrp10 J4 4 K4. pz Hrp10 J8 8 K8. pz Hrp10 J9 9 K9.
  pz Hrp10 J18 18 K18. pz Hrp10 J19 19 K19. pz Hrp10 J20 20 K20. pz Hrp10 J22 22 K22.
  pz Hrp10 J23 23 K23. pz Hrp10 J24 24 K24. pz Hrp10 J25 25 K25. pz Hrp10 J26 26 K26. pz Hrp10 J27 27 K27.
  assert (M2 : reg_get regs10 2 = Z_to_bv 64 (spZ regs0 - 160)) by exact K2.
  assert (M3 : reg_get regs10 3 = reg_get regs0 3) by exact K3.
  assert (M4 : reg_get regs10 4 = reg_get regs0 4) by exact K4.
  assert (M22 : reg_get regs10 22 = reg_get regs0 22) by exact K22.
  assert (M23 : reg_get regs10 23 = reg_get regs0 23) by exact K23.
  assert (M24 : reg_get regs10 24 = reg_get regs0 24) by exact K24.
  assert (M25 : reg_get regs10 25 = reg_get regs0 25) by exact K25.
  assert (M26 : reg_get regs10 26 = reg_get regs0 26) by exact K26.
  assert (M27 : reg_get regs10 27 = reg_get regs0 27) by exact K27.
  assert (FS10 : rw_cells rsegs mem10 (spZ regs0 - 160 + 104) (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21))).
  { apply (LW.lf_rw_cells_frame m9); [exact FS9|]. intros a Ha.
    cbn [cells_size csize lsv] in Ha. rewrite <- SEGS. apply Habove10. rewrite Hsp9. lia. }
  pose proof (f_norm L5 A5 mem10 md10 (spZ regs0 - 160 + 104) (lsv (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18)
            (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)) FR10 ltac:(lia)
                ltac:(cbn [cells_size csize lsv]; lia) FS10) as FS10n.
  rewrite SEGS.
  eapply (g_run_cf B API SEGS AX HGG stk (spZ regs0) L0 A0 mem0 md0 (mkFP (@fp_regs fx8) (@fp_csr fx8)) regs10
            (YK11.getr regs9 1) mem10 md10 L5 A5
    (LW.qret (@fp_regs fx8) (@fp_csr fx8) (reg_get regs0 1) (reg_get regs0 3) (reg_get regs0 4) (reg_get regs0 8)
       (reg_get regs0 9) (reg_get regs0 18) (reg_get regs0 19) (reg_get regs0 20) (reg_get regs0 21)
       (reg_get regs0 22) (reg_get regs0 23) (reg_get regs0 24) (reg_get regs0 25) (reg_get regs0 26)
       (reg_get regs0 27) (normalize rsegs mem10) (spZ regs0))).
  { exact FR10. } { lia. } { lia. }
  { unfold Regs6ss.mkR_of. change (YK11.getr regs9 1) with (reg_get regs9 1). rewrite J1.
    rewrite M2, M3, M4, M22, M23, M24, M25, M26, M27.
    apply (s1i (reg_get regs0 1) (reg_get regs0 8) (reg_get regs0 9) (reg_get regs0 18) (reg_get regs0 19)
             (reg_get regs0 20) (reg_get regs0 21) (reg_get regs0 3) (reg_get regs0 4)
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (@fp_regs fx8) (@fp_csr fx8)
             (normalize rsegs mem10) (spZ regs0 - 160) (spZ regs0 - stk)).
    - lia.
    - lia.
    - lia.
    - exact FS10n.
    - intros y5 y6 y7 y11 y12 y13 y14 y15 y16 y17.
      apply evt_done. unfold LW.qret. eexists.
      replace (spZ regs0 - 160 + 160) with (spZ regs0) by lia.
      split; [reflexivity|]. do 16 (split; [reflexivity|]). reflexivity. }
  { intros ms (Rq & -> & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
    do 5 eexists. exists (@nil (Z * Z)).
    split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
    intros x Hx NO. exfalso. apply NO. exact I. }
  intros R11 Ff11 pc11 fc11 m11' HQ11 regs11 m11 Hx11 Hrel11 FR11.
  destruct HQ11 as (Re & HEe & N1 & N2 & N3 & N4 & N8 & N9 & N10 & N18 & N19 & N20 & N21 & N22 & N23 & N24 & N25 &
    N26 & N27).
  injection HEe as ERe EFe EPe ECe EMe. subst Re Ff11 pc11 fc11 m11'.
  apply (SRcf_ret B).
  assert (G10f : YK11.getr regs11 10 = Z_to_bv 64 0) by (rewrite (lf_getr_eqv _ _ _ Hx11); exact N10).
  assert (RP : regs_preserved regs0 regs11).
  { intros r Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                  r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (unfold callee_saved in Hr; lia).
    rewrite (lf_getr_eqv _ _ _ Hx11).
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[-> | ->]]]]]]]]]]]]]].
    - transitivity (Z_to_bv 64 (spZ regs0)); [exact N2 | unfold spZ; apply Z_to_bv_bv_unsigned].
    - exact N3.
    - exact N4.
    - exact N8.
    - exact N9.
    - exact N18.
    - exact N19.
    - exact N20.
    - exact N21.
    - exact N22.
    - exact N23.
    - exact N24.
    - exact N25.
    - exact N26.
    - exact N27. }
  destruct (lf_post B API SINK stk empty L0 A0 regs0 mem0 md0 ra p n L5 A5 regs11 m11 md10 Hpre Hsn FR11 G10f RP)
    as (Hpost & Hsn' & Hpay & MI11).
  exists (mkFP (@fp_regs fx8) (@fp_csr fx8)), L5, A5, regs11, m11, md10.
  assert (E1r : YK11.getr regs0 1 = reg_get regs0 1) by reflexivity.
  split; [rewrite SEGS, <- E1r, Hra1, (lf_ret_pc _ Hra); reflexivity|].
  split; [exact Hfrm8|]. split; [exact Hpost|]. split; [exact Hsn'|].
  split; [rewrite sb_free_malloc in Hres10; exact Hres10|].
  split; [exact Hpay|]. split; [exact MI11 | exact I].
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
Proof.
  intros BI j Hj ra empty stk Hk Hra L A regs mem md p n pl b Hpre Hn Hpl Hsn Hsp Hres Hroom Hro Hrelro HGI Hfrm.
  pose proof (llvm_n_bound stk empty L A regs mem md ra p n Hpre) as Hnb.
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn11 & _).
  destruct (Z_lt_le_dec n (2 ^ 26)) as [Hsmall|Hbig].
  2:{ apply (llvm_early_cf B API SINK j stk empty L A regs mem md ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm).
      rewrite Hn11. rewrite MState.unsigned_lit by lia. exact Hbig. }
  apply (sr_entry_cf stk empty L A regs mem md ra p n pl b j); assumption.
Qed.

End M.
