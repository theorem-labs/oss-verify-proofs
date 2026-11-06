(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/U/Prog/LLVMFuzzerTestOneInput.v, with its module paths and module names changed; 100 of its 229 lines of code are new or changed and 1115 lines of the source are left out. *)
(* Glue between the LLVMFuzzerTestOneInput walks (lt_segs.v) and the SR contracts of its callees, for fuzz_lock.plain:
   libreac/fuzz_decode's lib/Prog/fd_glue.v (release 25e3d17bdb50) without its allocator lemmas (fuzz_lock's
   LLVMFuzzerTestOneInput allocates nothing), with g_cno and g_cl, the calls of check_no_overread and check_lookup
   through their contracts, in the form of decode's g_crt. Modified by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import Contract Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import check_no_overread_c check_lookup_c
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr.
Import ListNotations.
Open Scope Z_scope.

Lemma lf_rw_cells_frame : forall m m' A cs,
  rw_cells rsegs m A cs ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) ->
     mbyte rsegs m' a = mbyte rsegs m a /\ (writable_at rsegs m a <-> writable_at rsegs m' a)) ->
  rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs [[Hwf (H0 & H1 & Hb)] (W0 & W1 & Hw)] HE.
  rewrite cells_bytes_length in H1 by exact Hwf.
  split; [split; [exact Hwf|] |].
  - split; [exact H0|]. split; [rewrite cells_bytes_length by exact Hwf; exact H1|].
    intros i Hi. rewrite <- (Hb i Hi). rewrite cells_bytes_length in Hi by exact Hwf.
    change (mrd rsegs m' (wa (A + Z.of_nat i)) = mrd rsegs m (wa (A + Z.of_nat i))).
    exact (proj1 (HE (A + Z.of_nat i) ltac:(lia))).
  - split; [exact W0|]. split; [exact W1|]. intros i Hi.
    apply (proj1 (proj2 (HE (A + i) ltac:(lia)))). exact (Hw i Hi).
Qed.

Lemma bytes_at_frame : forall m m' A bs,
  bytes_at rsegs m A bs ->
  (forall a, A <= a < A + Z.of_nat (length bs) -> mbyte rsegs m' a = mbyte rsegs m a) ->
  bytes_at rsegs m' A bs.
Proof.
  intros m m' A bs (H0 & H1 & Hb) HE. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (Hb i Hi).
  change (mrd rsegs m' (wa (A + Z.of_nat i)) = mrd rsegs m (wa (A + Z.of_nat i))).
  exact (HE (A + Z.of_nat i) ltac:(lia)).
Qed.

Lemma blk_bytes_at : forall B m A bs, ms_segs B = rsegs -> 0 <= A -> A + Z.of_nat (length bs) <= 2 ^ 64 ->
  blk_data B m A bs -> bytes_at rsegs m A bs.
Proof.
  intros B m A bs HS H0 H1 HD. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  pose proof (HD (Z.of_nat i) ltac:(lia)) as E. rewrite Nat2Z.id in E. rewrite <- E, HS. reflexivity.
Qed.

Lemma bytes_at_blk : forall B m A bs, ms_segs B = rsegs -> bytes_at rsegs m A bs -> blk_data B m A bs.
Proof.
  intros B m A bs HS (H0 & H1 & Hb) i Hi. rewrite HS.
  pose proof (Hb (Z.to_nat i) ltac:(lia)) as E. rewrite Z2Nat.id in E by lia. exact E.
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
Hypothesis CNO : forall fx' : YK11.FPState, @check_no_overread_contract fx' rc B API.
Hypothesis CL : forall fx' : YK11.FPState, @check_lookup_contract fx' rc B API.

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

Lemma g_cno : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A t n pa rate T P SL bres
    (Pc : config -> Prop),
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - CNO_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  YK11.getr regs 10 = Z_to_bv 64 t -> YK11.getr regs 11 = Z_to_bv 64 n ->
  YK11.getr regs 12 = Z_to_bv 64 pa -> YK11.getr regs 13 = Z_to_bv 64 rate ->
  0 <= n < 2 ^ 26 -> Z.of_nat (length T) = n ->
  0 < t < 2 ^ 63 -> in_block L A t n -> blk_data B mem t T ->
  spZ regs <= pa -> pa mod 8 = 0 -> pa + 16 <= 2 ^ 63 ->
  length (P ++ Z_to_bv 8 0 :: SL) = 16%nat -> ~ In (Z_to_bv 8 0) P ->
  blk_data B mem pa (P ++ Z_to_bv 8 0 :: SL) ->
  0 <= rate < 2 ^ 64 -> frm_zero (@fp_csr fx') ->
  res_ok_slots A bres ->
  sb_live bres + 2 <= sb_cap bres <= CAPMAX /\ 0 <= sb_bytes bres /\ sb_bytes bres + 2 * (n + 1) <= 2 ^ 40 ->
  (forall (fx'' : YK11.FPState) L' A' regs' mem' md',
     frm_zero (@fp_csr fx'') ->
     lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     blocks L' A' = blocks L A -> res_ok_slots A' bres ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     blocks_kept B L A mem mem' (fun _ => False) ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx'' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') Pc) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 CHECK_NO_OVERREAD) mem (YK11.seg_rom (ms_segs B))) md) Pc.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A t n pa rate T P SL bres Pc FR Hc HS Hra Hal H1 H2 H63 Htp
    G10 G11 G12 G13 Hn HT Ht IBt BDt Hpa1 Hpa8 Hpa2 HPL NP BDp Hr Hfrm Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  eapply SR_bind.
  { apply (CNO fx' L A regs mem md t n pa rate T P SL bres SEGS);
      first [ exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs CNO_STACK FR Hra Hal H1 H2
                ltac:(unfold CNO_STACK, CNO_FRAME, ALLOC_STACK; lia) Hc H63 Htp)
            | assumption | (rewrite SEGS; exact MI) ]. }
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
  - apply (g_above stk S L A regs mem md CNO_STACK (fun _ => False) L2 A2 regs2 mem2 md2 HM Hpost Hc H1 HS
      ltac:(unfold CNO_STACK, CNO_FRAME, ALLOC_STACK; lia)).
    intros a Ha. destruct Ha.
  - exact Hkept.
Qed.

Lemma g_cl : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs mem md L A t n pa k rate T P SL bres
    (Pc : config -> Prop),
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> YM05.alloc_ceiling + stk <= S -> S <= 2 ^ 64 ->
  YK0s.ret_ok (YK11.getr regs 1) -> spZ regs mod 16 = 0 -> S - stk <= spZ regs - CL_STACK -> spZ regs <= S ->
  spZ regs < 2 ^ 63 -> YK11.getr regs 4 = Z_to_bv 64 (ms_tp B) ->
  YK11.getr regs 10 = Z_to_bv 64 t -> YK11.getr regs 11 = Z_to_bv 64 n ->
  YK11.getr regs 12 = Z_to_bv 64 pa -> YK11.getr regs 13 = Z_to_bv 64 k -> YK11.getr regs 14 = Z_to_bv 64 rate ->
  0 <= n < 2 ^ 26 -> Z.of_nat (length T) = n ->
  0 < t < 2 ^ 63 -> in_block L A t n -> blk_data B mem t T ->
  spZ regs <= pa -> pa mod 8 = 0 -> pa + 16 <= 2 ^ 63 ->
  length (P ++ Z_to_bv 8 0 :: SL) = 16%nat -> ~ In (Z_to_bv 8 0) P -> Z.of_nat (length P) = k ->
  blk_data B mem pa (P ++ Z_to_bv 8 0 :: SL) ->
  0 <= rate < 2 ^ 64 -> frm_zero (@fp_csr fx') ->
  res_ok_slots A bres ->
  sb_live bres + 1 <= sb_cap bres <= CAPMAX /\ 0 <= sb_bytes bres /\ sb_bytes bres + (n + 1) <= 2 ^ 40 ->
  (forall (fx'' : YK11.FPState) L' A' regs' mem' md',
     frm_zero (@fp_csr fx'') ->
     lf_fr B API stk S L0 A0 mem0 md0 L' A' mem' md' -> regs_preserved regs regs' ->
     blocks L' A' = blocks L A -> res_ok_slots A' bres ->
     (forall a, spZ regs <= a < S -> mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
        (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
     blocks_kept B L A mem mem' (fun _ => False) ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx'' regs' (YK11.getr regs 1) mem' (YK11.seg_rom (ms_segs B))) md') Pc) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 CHECK_LOOKUP) mem (YK11.seg_rom (ms_segs B))) md) Pc.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs mem md L A t n pa k rate T P SL bres Pc FR Hc HS Hra Hal H1 H2 H63 Htp
    G10 G11 G12 G13 G14 Hn HT Ht IBt BDt Hpa1 Hpa8 Hpa2 HPL NP HPk BDp Hr Hfrm Hres Hroom K.
  pose proof FR as (HM & HW & HB & HID & Hmd & Hhigh & Himg & Hblk & Hbyt & Hstw & Herr & Hgd & MI).
  eapply SR_bind.
  { apply (CL fx' L A regs mem md t n pa k rate T P SL bres SEGS);
      first [ exact (g_pre stk S L0 A0 mem0 md0 L A mem md regs CL_STACK FR Hra Hal H1 H2
                ltac:(unfold CL_STACK, CL_FRAME, ALLOC_STACK; lia) Hc H63 Htp)
            | assumption | (rewrite SEGS; exact MI) ]. }
  intros c2 (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & Hfrm2 & Hpost & Eb & Hkept & Hgk & Hro2 & Hres2 & Hidt).
  pose proof Hpost as (HM2 & HW2 & HB2 & Hle & Hstab & Hrp & (vm2 & Hvm2) & Hfr2 & Hkeep2 & Hscr2).
  assert (FR2 : lf_fr B API stk S L0 A0 mem0 md0 L2 A2 mem2 md2).
  { eapply (lf_fr_call B API SEGS AX ERRNO_LOW); [exact FR | lia | lia | exact Hpost
      | unfold CL_STACK, CL_FRAME, ALLOC_STACK in *; lia | lia | | | | | | exact Hidt | | ].
    - intros a Ha. exfalso. exact Ha.
    - intros a Ha. right. intros Hf. exact Hf.
    - intros a Hf Ha. exfalso. exact Hf.
    - intros a0 k0 Hin. rewrite Eb. exact (Hblk a0 k0 Hin).
    - intros a0 k0 i Hin Hi. exact (Hkept a0 k0 i (Hblk a0 k0 Hin) (fun H => H) Hi).
    - rewrite <- SEGS. exact Hro2.
    - exact Hgk. }
  apply (K fx2 L2 A2 regs2 mem2 md2 Hfrm2 FR2 Hrp Eb Hres2).
  - apply (g_above stk S L A regs mem md CL_STACK (fun _ => False) L2 A2 regs2 mem2 md2 HM Hpost Hc H1 HS
      ltac:(unfold CL_STACK, CL_FRAME, ALLOC_STACK; lia)).
    intros a Ha. destruct Ha.
  - exact Hkept.
Qed.

Lemma g_run : forall stk S L0 A0 mem0 md0 (fx' : YK11.FPState) regs pc mem md L A
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
     SR rsegs (mkCfg (@YK11.mkst (mkFP F fc) regs' pc' m' (YK11.seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (@YK11.mkst fx' regs pc mem (YK11.seg_rom rsegs)) md) P.
Proof.
  intros stk S L0 A0 mem0 md0 fx' regs pc mem md L A Q P FR Hc HS HE Hform HK.
  pose proof FR as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hro).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  apply (llvm_run_norm fx' regs pc mem md Q P Hh Hl Hro HE).
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

End G.
