(* ARM 4 (op_decide) glue, part 2: the four allocator-facing calls of op_decide, text_of at 0x13aa4 and
   0x13ab4, free at 0x13ae8 and 0x13af0. For each call cut of LC45Defs:
   - lg4_form_*: the cut is at the callee's pc (the form LFrRun.cut_evt asks);
   - lg4_pre_*: the registers and cells the step's premise reads (ra, sp, tp, a0, a1; the cursor cells, the
     *own cell and the input bytes for text_of);
   - lg4_ad_*: the return adapter: the call cut's facts at m, the step's facts at m' (the callee-saved
     registers, lcarry over the kept regions, the post memory facts, the callee's answer) give LC45Defs'
     return cut of the canonical register file mkR_of regs'; free(NULL) keeps registers and memory.
   K is the region the step keeps (LFr lkeep at the glue); the hypothesis `lh_reg E x -> K x` is
   LG4Lib.lg4_keep. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss MState.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem text_of_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr LFrLo
  LC45Defs LC45Call LC45ComLib LG4Lib.
Import ListNotations.
Local Open Scope Z_scope.

Ltac lg4_ar := unfold c45_sp, FO_P, FO_B40, FO_B256, SLOT_FRAME, SLOT_STACK_Z in *; lia.

(* ==========================================================================
   1. The input of text_of: the cursor is a suffix of the payload
   ========================================================================== *)

Lemma lg4_cur_inp : forall E P N m, lenv_ok E -> c45_cur E P N -> bytes_at rsegs m (e_p0 E) (e_pl E) ->
  bv_unsigned (wz P) = P /\ bv_unsigned (wz N) = N /\
  (exists inp, bytes_at rsegs m P inp /\ Z.of_nat (length inp) = N) /\
  e_p0 E <= P /\ P + N = e_p0 E + Z.of_nat (length (e_pl E)) /\ 0 <= N.
Proof.
  intros E P N m HE (k & Hk & -> & ->) Hpl.
  pose proof HE as (HS1 & HS2 & _ & _ & _ & _ & _ & _ & _ & (Bp1 & Bp2 & _) & _).
  destruct (lg4_bytes_skip m (e_p0 E) (e_pl E) k Hpl Hk) as [Hb Hl].
  split; [unfold wz; apply MState.unsigned_lit; unfold SLOT_STACK_Z in *; lia|].
  split; [unfold wz; apply MState.unsigned_lit; unfold SLOT_STACK_Z in *; lia|].
  split; [exists (skipn (Z.to_nat k) (e_pl E)); split; [exact Hb | exact Hl]|].
  lia.
Qed.

(* ==========================================================================
   2. The call cuts: their pc, and what the steps read
   ========================================================================== *)

Lemma lg4_form_aa4 : forall E i gp ms, c45_13aa4 E i gp ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 TEXT_OF) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E i gp ms (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6 & F & fc & m
    & P & N & kbs & mbs & gbs & j0 & j1 & j2 & w2 & EQ & FC & _).
  subst ms. eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma lg4_form_ab4 : forall E i gp own1 ms, c45_13ab4 E i gp own1 ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 TEXT_OF) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E i gp own1 ms (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6 & F & fc & m
    & P & N & s1 & kbs & mbs & gbs & j0 & j1 & j2 & t1v & w1 & EQ & FC & _).
  subst ms. eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma lg4_form_ae8 : forall E i gp own1 own2 ms, c45_13ae8 E i gp own1 own2 ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E i gp own1 own2 ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6
    & F & fc & m & P & N & kbs & mbs & gbs & j0 & j1 & j2 & EQ & FC & _).
  subst ms. eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma lg4_form_af0 : forall E i gp own1 own2 ms, c45_13af0 E i gp own1 own2 ms ->
  exists R F fc m, ms = MS R F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs) /\ frm0 fc.
Proof.
  intros E i gp own1 own2 ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6
    & F & fc & m & P & N & kbs & mbs & gbs & j0 & j1 & j2 & EQ & FC & _).
  subst ms. eexists _, F, fc, m. split; [reflexivity | exact FC].
Qed.

Lemma lg4_pre_aa4 : forall E i gp ms, lenv_ok E -> c45_13aa4 E i gp ms ->
  getr (ms_regs ms) 1 = Z_to_bv 64 C45_TO1_RA /\ getr (ms_regs ms) 2 = Z_to_bv 64 (e_S E - SLOT_FRAME) /\
  getr (ms_regs ms) 4 = Z_to_bv 64 A_TP /\ getr (ms_regs ms) 10 = Z_to_bv 64 (c45_sp E + FO_P) /\
  getr (ms_regs ms) 11 = Z_to_bv 64 (c45_sp E + FO_B256) /\
  exists c0 c1 : word,
    rw_cells rsegs (ms_mem ms) (c45_sp E + FO_P) [C8 c0; C8 c1] /\
    (exists w, rw_cells rsegs (ms_mem ms) (c45_sp E + FO_B256) [C8 w]) /\
    (exists inp, bytes_at rsegs (ms_mem ms) (bv_unsigned c0) inp /\ Z.of_nat (length inp) = bv_unsigned c1) /\
    e_p0 E <= bv_unsigned c0 /\ bv_unsigned c0 + bv_unsigned c1 <= e_p0 E + Z.of_nat (length (e_pl E)).
Proof.
  intros E i gp ms HE (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6 & F & fc & m
    & P & N & kbs & mbs & gbs & j0 & j1 & j2 & w2 & -> & _ & _ & (_ & Fc & _) & Hc & _ & B256 & _ & _ & KEEP & _).
  cbn [ms_regs ms_mem MS].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|].
  destruct KEEP as (_ & _ & _ & _ & _ & _ & _ & _ & PL).
  destruct (lg4_cur_inp E P N m HE Hc PL) as (U1 & U2 & Hinp & H1 & H2 & _).
  exists (wz P), (wz N). rewrite U1, U2.
  split; [exact Fc|]. split; [exists w2; exact B256|]. split; [exact Hinp|]. lia.
Qed.

Lemma lg4_pre_ab4 : forall E i gp own1 ms, lenv_ok E -> c45_13ab4 E i gp own1 ms ->
  getr (ms_regs ms) 1 = Z_to_bv 64 C45_TO2_RA /\ getr (ms_regs ms) 2 = Z_to_bv 64 (e_S E - SLOT_FRAME) /\
  getr (ms_regs ms) 4 = Z_to_bv 64 A_TP /\ getr (ms_regs ms) 10 = Z_to_bv 64 (c45_sp E + FO_P) /\
  getr (ms_regs ms) 11 = Z_to_bv 64 (c45_sp E + FO_B40) /\
  exists c0 c1 : word,
    rw_cells rsegs (ms_mem ms) (c45_sp E + FO_P) [C8 c0; C8 c1] /\
    (exists w, rw_cells rsegs (ms_mem ms) (c45_sp E + FO_B40) [C8 w]) /\
    (exists inp, bytes_at rsegs (ms_mem ms) (bv_unsigned c0) inp /\ Z.of_nat (length inp) = bv_unsigned c1) /\
    e_p0 E <= bv_unsigned c0 /\ bv_unsigned c0 + bv_unsigned c1 <= e_p0 E + Z.of_nat (length (e_pl E)).
Proof.
  intros E i gp own1 ms HE (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6 & F & fc & m
    & P & N & s1 & kbs & mbs & gbs & j0 & j1 & j2 & t1v & w1 & -> & _ & _ & (_ & Fc & _) & Hc & B40
    & _ & _ & _ & _ & _ & _ & _ & KEEP & _).
  cbn [ms_regs ms_mem MS].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|].
  destruct KEEP as (_ & _ & _ & _ & _ & _ & _ & _ & PL).
  destruct (lg4_cur_inp E P N m HE Hc PL) as (U1 & U2 & Hinp & H1 & H2 & _).
  exists (wz P), (wz N). rewrite U1, U2.
  split; [exact Fc|]. split; [exists w1; exact B40|]. split; [exact Hinp|]. lia.
Qed.

Lemma lg4_pre_ae8 : forall E i gp own1 own2 ms, c45_13ae8 E i gp own1 own2 ms ->
  getr (ms_regs ms) 1 = Z_to_bv 64 C45_FR1_RA /\ getr (ms_regs ms) 2 = Z_to_bv 64 (e_S E - SLOT_FRAME) /\
  getr (ms_regs ms) 4 = Z_to_bv 64 A_TP /\ getr (ms_regs ms) 10 = Z_to_bv 64 own1.
Proof.
  intros E i gp own1 own2 ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6
    & F & fc & m & P & N & kbs & mbs & gbs & j0 & j1 & j2 & -> & _).
  cbn [ms_regs MS]. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma lg4_pre_af0 : forall E i gp own1 own2 ms, c45_13af0 E i gp own1 own2 ms ->
  getr (ms_regs ms) 1 = Z_to_bv 64 C45_FR2_RA /\ getr (ms_regs ms) 2 = Z_to_bv 64 (e_S E - SLOT_FRAME) /\
  getr (ms_regs ms) 4 = Z_to_bv 64 A_TP /\ getr (ms_regs ms) 10 = Z_to_bv 64 own2.
Proof.
  intros E i gp own1 own2 ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6
    & F & fc & m & P & N & kbs & mbs & gbs & j0 & j1 & j2 & -> & _).
  cbn [ms_regs MS]. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
Qed.

(* ==========================================================================
   3. The return adapters
   ========================================================================== *)

(* text_of (kind) at 0x13aa4, back at 0x13aa8: a0 = the string s, own1 = own in the ok cell *)
Lemma lg4_ad_to1 : forall E i gp (K : Z -> Prop) R F fc m regs' m' (c0 c1 : word) own k s t,
  lenv_ok E -> (forall x, lh_reg E x -> K x) ->
  c45_13aa4 E i gp (MS R F (Z_to_bv 64 TEXT_OF) fc None m (seg_rom rsegs)) ->
  rw_cells rsegs m (c45_sp E + FO_P) [C8 c0; C8 c1] ->
  regs_preserved R regs' -> getr regs' 10 = Z_to_bv 64 s -> s <> 0 ->
  lcarry (fun x => K x /\ ~ (c45_sp E + FO_P <= x < c45_sp E + FO_P + 16) /\
                   ~ (c45_sp E + FO_B256 <= x < c45_sp E + FO_B256 + 8)) m m' ->
  mem_inv rsegs m' -> MemNorm.task_mem rsegs m' -> stk rsegs m' (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  wr_at rsegs m' A_ERRNO 4 -> guard_m m' ->
  cstr_at m' s t ->
  rw_cells rsegs m' (c45_sp E + FO_B256) [C8 (Z_to_bv 64 own)] ->
  (exists adv, 0 <= adv <= bv_unsigned c1 /\
     rw_cells rsegs m' (c45_sp E + FO_P)
       [C8 (Z_to_bv 64 (bv_unsigned c0 + adv)); C8 (Z_to_bv 64 (bv_unsigned c1 - adv))]) ->
  (own = 0 -> A_RO_LO <= s /\ s + Z.of_nat (length t) + 1 <= A_RO_END) ->
  (own <> 0 -> own = s /\ 1 <= k <= 320 /\ Z.of_nat (length t) + 1 <= k /\
     4096 <= own /\ own + k <= e_S E - SLOT_STACK_Z) ->
  c45_13aa8 E i gp own (MS (Regs6ss.mkR_of regs') F (Z_to_bv 64 C45_TO1_RA) fc None m' (seg_rom rsegs)) /\
  lg4_x1 own k m'.
Proof.
  intros E i gp K R F fc m regs' m' c0 c1 own k s t HE HK H C01 RP G10 Hs C M1 M2 M3 M4 M5 Ht Hown
    (adv & Hadv & Hcur) Hz Hnz.
  destruct H as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6 & F0 & fc0 & m0
    & P & N & kbs & mbs & gbs & j0 & j1 & j2 & w2 & EQ & FC & Hi & (Fp & Fc & Fs) & Hc & B40 & B256 & B256x
    & KMG & KEEP & MACH).
  pose proof (f_equal ms_regs EQ) as ER. pose proof (f_equal ms_fcsr EQ) as EF.
  pose proof (f_equal ms_mem EQ) as EM.
  cbn [ms_regs ms_fcsr ms_mem MS] in ER, EF, EM. subst R fc0 m0.
  destruct (lg4_cells2_det m _ c0 c1 (wz P) (wz N) C01 Fc) as [-> ->].
  pose proof KEEP as (_ & _ & _ & _ & _ & _ & _ & _ & PL).
  destruct (lg4_cur_inp E P N m HE Hc PL) as (U1 & U2 & _ & _ & _ & _).
  rewrite U1, U2 in Hcur. rewrite U2 in Hadv.
  pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsv).
  set (U := fun x => K x /\ ~ (c45_sp E + FO_P <= x < c45_sp E + FO_P + 16) /\
                     ~ (c45_sp E + FO_B256 <= x < c45_sp E + FO_B256 + 8)) in C.
  assert (HUf : forall x, e_S E - SLOT_FRAME <= x < e_S E -> ~ (c45_sp E + FO_P <= x < c45_sp E + FO_P + 16) ->
                ~ (c45_sp E + FO_B256 <= x < c45_sp E + FO_B256 + 8) -> U x).
  { intros x H1 H2 H3. split; [apply HK, lh_reg_frame; unfold lo_rng; lia | split; assumption]. }
  assert (HUn : forall x, lh_reg E x -> x < e_S E - SLOT_FRAME -> U x).
  { intros x H1 H2. split; [exact (HK x H1)|]. split; lg4_ar. }
  destruct (lg4_kk E i kbs mbs gbs U m m' HE HUn C M4 M5 KMG KEEP) as [KMG' KEEP'].
  assert (Fp' : rw_cells rsegs m' (c45_sp E) (c45_ptrs E j0)).
  { apply (lg4_rw U m m' _ _ C); [|exact Fp]. intros x Hx.
    change (Z.of_nat (cells_size (c45_ptrs E j0))) with 64 in Hx. apply HUf; lg4_ar. }
  assert (Fs' : bytes_at rsegs m' (e_S E - 104) (e_saved E)).
  { apply (lg4_bytes U m m' _ _ C); [|exact Fs]. intros x Hx. rewrite Hsv in Hx.
    change (Z.of_nat 104) with 104 in Hx. apply HUf; lg4_ar. }
  assert (B40' : rw_cells rsegs m' (c45_sp E + FO_B40) [CB 40 j1]).
  { apply (lg4_rw U m m' _ _ C); [|exact B40]. intros x Hx.
    change (Z.of_nat (cells_size [CB 40 j1])) with 40 in Hx. apply HUf; lg4_ar. }
  assert (B256x' : rw_cells rsegs m' (c45_sp E + FO_B256 + 8) [CB 248 j2]).
  { apply (lg4_rw U m m' _ _ C); [|exact B256x]. intros x Hx.
    change (Z.of_nat (cells_size [CB 248 j2])) with 248 in Hx. apply HUf; lg4_ar. }
  unfold c45_R in RP.
  pose proof (c45_canon_of_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs' RP) as CN.
  assert (H10 : reg_get regs' 10 = wz s) by (unfold wz; rewrite <- G10; reflexivity).
  split.
  - rewrite CN, H10.
    exists (reg_get regs' 1), (reg_get regs' 5), (reg_get regs' 6), (reg_get regs' 7), (reg_get regs' 11),
      (reg_get regs' 12), (reg_get regs' 13), (reg_get regs' 14), (reg_get regs' 15), (reg_get regs' 16),
      (reg_get regs' 17), s2, s3, s4, (reg_get regs' 28), (reg_get regs' 29), (reg_get regs' 30),
      (reg_get regs' 31), F, fc, m', (P + adv), (N - adv), s, kbs, mbs, gbs, j0, j1, j2, t.
    split; [reflexivity|]. split; [exact FC|]. split; [exact Hi|].
    split; [split; [exact Fp' | split; [exact Hcur | exact Fs']]|].
    split; [destruct Hc as (k0 & Hk0 & -> & ->); exists (k0 + adv); lia|].
    split; [exact B40'|]. split; [exact Hown|]. split; [exact B256x'|].
    split; [exact Hs|]. split; [exact Ht|].
    split.
    + unfold c45_loc. destruct (Z.eq_dec own 0) as [E0|E0].
      * left. destruct (Hz E0) as [Z1 Z2]. split; [exact E0 | split; [exact Z1 | exact Z2]].
      * right. destruct (Hnz E0) as (Es & Hk1 & Hk2 & Hk3 & Hk4).
        split; [exact E0|]. split; [symmetry; exact Es|]. exists k. repeat split; lia.
    + split; [exact KMG'|]. split; [exact KEEP'|]. split; [exact M1 | split; [exact M2 | exact M3]].
  - intros E0. destruct (Hnz E0) as (Es & _ & Hk & _). exists t. rewrite Es. split; [exact Ht | exact Hk].
Qed.

(* text_of (alias) at 0x13ab4, back at 0x13ab8: a0 = the string s, own2 = own in the oa cell; the kind
   string s1 is carried (read-only, or inside own1's block, which the step keeps) *)
Lemma lg4_ad_to2 : forall E i gp own1 k1 (K : Z -> Prop) R F fc m regs' m' (c0 c1 : word) own k s t,
  lenv_ok E -> (forall x, lh_reg E x -> K x) ->
  (own1 <> 0 -> 1 <= k1 <= 320 /\ 4096 <= own1 /\ own1 + k1 <= e_S E - SLOT_STACK_Z /\
     (forall x, own1 <= x < own1 + k1 -> K x)) ->
  c45_13ab4 E i gp own1 (MS R F (Z_to_bv 64 TEXT_OF) fc None m (seg_rom rsegs)) -> lg4_x1 own1 k1 m ->
  rw_cells rsegs m (c45_sp E + FO_P) [C8 c0; C8 c1] ->
  regs_preserved R regs' -> getr regs' 10 = Z_to_bv 64 s -> s <> 0 ->
  lcarry (fun x => K x /\ ~ (c45_sp E + FO_P <= x < c45_sp E + FO_P + 16) /\
                   ~ (c45_sp E + FO_B40 <= x < c45_sp E + FO_B40 + 8)) m m' ->
  mem_inv rsegs m' -> MemNorm.task_mem rsegs m' -> stk rsegs m' (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  wr_at rsegs m' A_ERRNO 4 -> guard_m m' ->
  cstr_at m' s t ->
  rw_cells rsegs m' (c45_sp E + FO_B40) [C8 (Z_to_bv 64 own)] ->
  (exists adv, 0 <= adv <= bv_unsigned c1 /\
     rw_cells rsegs m' (c45_sp E + FO_P)
       [C8 (Z_to_bv 64 (bv_unsigned c0 + adv)); C8 (Z_to_bv 64 (bv_unsigned c1 - adv))]) ->
  (own = 0 -> A_RO_LO <= s /\ s + Z.of_nat (length t) + 1 <= A_RO_END) ->
  (own <> 0 -> own = s /\ 1 <= k <= 320 /\ Z.of_nat (length t) + 1 <= k /\
     4096 <= own /\ own + k <= e_S E - SLOT_STACK_Z) ->
  c45_13ab8 E i gp own1 own (MS (Regs6ss.mkR_of regs') F (Z_to_bv 64 C45_TO2_RA) fc None m' (seg_rom rsegs)).
Proof.
  intros E i gp own1 k1 K R F fc m regs' m' c0 c1 own k s t HE HK HB1 H X1 C01 RP G10 Hs C M1 M2 M3 M4 M5 Ht Hown
    (adv & Hadv & Hcur) Hz Hnz.
  destruct H as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & s3 & s4 & t3 & t4 & t5 & t6 & F0 & fc0 & m0
    & P & N & s1 & kbs & mbs & gbs & j0 & j1 & j2 & t1v & w1 & EQ & FC & Hi & (Fp & Fc & Fs) & Hc & B40 & B40x
    & B256 & B256x & Hs1 & Hc1 & Hl1 & KMG & KEEP & MACH).
  pose proof (f_equal ms_regs EQ) as ER. pose proof (f_equal ms_fcsr EQ) as EF.
  pose proof (f_equal ms_mem EQ) as EM.
  cbn [ms_regs ms_fcsr ms_mem MS] in ER, EF, EM. subst R fc0 m0.
  destruct (lg4_cells2_det m _ c0 c1 (wz P) (wz N) C01 Fc) as [-> ->].
  pose proof KEEP as (_ & _ & _ & _ & _ & _ & _ & _ & PL).
  destruct (lg4_cur_inp E P N m HE Hc PL) as (U1 & U2 & _ & _ & _ & _).
  rewrite U1, U2 in Hcur. rewrite U2 in Hadv.
  pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsv).
  set (U := fun x => K x /\ ~ (c45_sp E + FO_P <= x < c45_sp E + FO_P + 16) /\
                     ~ (c45_sp E + FO_B40 <= x < c45_sp E + FO_B40 + 8)) in C.
  assert (HUf : forall x, e_S E - SLOT_FRAME <= x < e_S E -> ~ (c45_sp E + FO_P <= x < c45_sp E + FO_P + 16) ->
                ~ (c45_sp E + FO_B40 <= x < c45_sp E + FO_B40 + 8) -> U x).
  { intros x H1 H2 H3. split; [apply HK, lh_reg_frame; unfold lo_rng; lia | split; assumption]. }
  assert (HUn : forall x, lh_reg E x -> x < e_S E - SLOT_FRAME -> U x).
  { intros x H1 H2. split; [exact (HK x H1)|]. split; lg4_ar. }
  destruct (lg4_kk E i kbs mbs gbs U m m' HE HUn C M4 M5 KMG KEEP) as [KMG' KEEP'].
  assert (Fp' : rw_cells rsegs m' (c45_sp E) (c45_ptrs E j0)).
  { apply (lg4_rw U m m' _ _ C); [|exact Fp]. intros x Hx.
    change (Z.of_nat (cells_size (c45_ptrs E j0))) with 64 in Hx. apply HUf; lg4_ar. }
  assert (Fs' : bytes_at rsegs m' (e_S E - 104) (e_saved E)).
  { apply (lg4_bytes U m m' _ _ C); [|exact Fs]. intros x Hx. rewrite Hsv in Hx.
    change (Z.of_nat 104) with 104 in Hx. apply HUf; lg4_ar. }
  assert (B40x' : rw_cells rsegs m' (c45_sp E + FO_B40 + 8) [CB 32 j1]).
  { apply (lg4_rw U m m' _ _ C); [|exact B40x]. intros x Hx.
    change (Z.of_nat (cells_size [CB 32 j1])) with 32 in Hx. apply HUf; lg4_ar. }
  assert (B256' : rw_cells rsegs m' (c45_sp E + FO_B256) [C8 (wz own1)]).
  { apply (lg4_rw U m m' _ _ C); [|exact B256]. intros x Hx.
    change (Z.of_nat (cells_size [C8 (wz own1)])) with 8 in Hx. apply HUf; lg4_ar. }
  assert (B256x' : rw_cells rsegs m' (c45_sp E + FO_B256 + 8) [CB 248 j2]).
  { apply (lg4_rw U m m' _ _ C); [|exact B256x]. intros x Hx.
    change (Z.of_nat (cells_size [CB 248 j2])) with 248 in Hx. apply HUf; lg4_ar. }
  assert (S1 : exists t1w, cstr_at m' s1 t1w /\ c45_loc E own1 s1 t1w).
  { destruct (Z.eq_dec own1 0) as [E0|E0].
    - destruct Hl1 as [(_ & Hlo & Hhi) | (Hne & _)]; [|contradiction].
      exists t1v. split; [exact (lg4_ro_cstr m m' s1 t1v (proj1 MACH) M1 Hlo Hhi Hc1)|].
      left. split; [exact E0 | split; [exact Hlo | exact Hhi]].
    - destruct Hl1 as [(Hz1 & _) | (_ & Es1 & _)]; [contradiction|].
      destruct (HB1 E0) as (Hk1 & H4096 & Htop & HKb).
      destruct (X1 E0) as (tq & Hcq & Hlq).
      exists tq. subst s1. split.
      + apply (lg4_cstr U m m' own1 tq C); [|exact Hcq]. intros x Hx. split; [apply HKb; lia|].
        split; lg4_ar.
      + right. split; [exact E0|]. split; [reflexivity|]. exists k1. repeat split; lia. }
  destruct S1 as (t1w & Hc1' & Hl1').
  unfold c45_R in RP.
  pose proof (c45_canon_of_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs' RP) as CN.
  assert (H10 : reg_get regs' 10 = wz s) by (unfold wz; rewrite <- G10; reflexivity).
  rewrite CN, H10.
  exists (reg_get regs' 1), (reg_get regs' 5), (reg_get regs' 6), (reg_get regs' 7), (reg_get regs' 11),
    (reg_get regs' 12), (reg_get regs' 13), (reg_get regs' 14), (reg_get regs' 15), (reg_get regs' 16),
    (reg_get regs' 17), s3, s4, (reg_get regs' 28), (reg_get regs' 29), (reg_get regs' 30),
    (reg_get regs' 31), F, fc, m', (P + adv), (N - adv), s1, s, kbs, mbs, gbs, j0, j1, j2, t1w, t.
  split; [reflexivity|]. split; [exact FC|]. split; [exact Hi|].
  split; [split; [exact Fp' | split; [exact Hcur | exact Fs']]|].
  split; [destruct Hc as (k0 & Hk0 & -> & ->); exists (k0 + adv); lia|].
  split; [exact Hown|]. split; [exact B40x'|]. split; [exact B256'|]. split; [exact B256x'|].
  split; [exact Hs1|]. split; [exact Hc1'|]. split; [exact Hl1'|].
  split; [exact Hs|]. split; [exact Ht|].
  split.
  - unfold c45_loc. destruct (Z.eq_dec own 0) as [E0|E0].
    + left. destruct (Hz E0) as [Z1 Z2]. split; [exact E0 | split; [exact Z1 | exact Z2]].
    + right. destruct (Hnz E0) as (Es & Hk1 & Hk2 & Hk3 & Hk4).
      split; [exact E0|]. split; [symmetry; exact Es|]. exists k. repeat split; lia.
  - split; [exact KMG'|]. split; [exact KEEP'|]. split; [exact M1 | split; [exact M2 | exact M3]].
Qed.

(* free at 0x13ae8 (own1), back at 0x13aec: the whole frame and the kept regions are carried *)
Lemma lg4_ad_fr1 : forall E i gp own1 own2 (K : Z -> Prop) R F fc m regs' m',
  lenv_ok E -> (forall x, lh_reg E x -> K x) ->
  c45_13ae8 E i gp own1 own2 (MS R F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs)) ->
  regs_preserved R regs' -> lcarry K m m' ->
  mem_inv rsegs m' -> MemNorm.task_mem rsegs m' -> stk rsegs m' (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  wr_at rsegs m' A_ERRNO 4 -> guard_m m' ->
  c45_13aec E i gp own1 own2 (MS (Regs6ss.mkR_of regs') F (Z_to_bv 64 C45_FR1_RA) fc None m' (seg_rom rsegs)).
Proof.
  intros E i gp own1 own2 K R F fc m regs' m' HE HK H RP C M1 M2 M3 M4 M5.
  destruct H as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6 & F0 & fc0 & m0
    & P & N & kbs & mbs & gbs & j0 & j1 & j2 & EQ & FC & Hi & (Fp & Fc & Fs) & Hc & B40 & B40x & B256 & B256x
    & KMG & KEEP & MACH).
  pose proof (f_equal ms_regs EQ) as ER. pose proof (f_equal ms_fcsr EQ) as EF.
  pose proof (f_equal ms_mem EQ) as EM.
  cbn [ms_regs ms_fcsr ms_mem MS] in ER, EF, EM. subst R fc0 m0.
  pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsv).
  assert (HUf : forall x, e_S E - SLOT_FRAME <= x < e_S E -> K x).
  { intros x Hx. apply HK, lh_reg_frame. unfold lo_rng. lia. }
  destruct (lg4_kk E i kbs mbs gbs K m m' HE (fun x H _ => HK x H) C M4 M5 KMG KEEP) as [KMG' KEEP'].
  assert (HF : forall A cs n, rw_cells rsegs m A cs -> Z.of_nat (cells_size cs) = n ->
                 e_S E - SLOT_FRAME <= A -> A + n <= e_S E -> rw_cells rsegs m' A cs).
  { intros A cs n H En H1 H2. apply (lg4_rw K m m' A cs C); [|exact H]. intros x Hx. apply HUf. lia. }
  assert (Fs' : bytes_at rsegs m' (e_S E - 104) (e_saved E)).
  { apply (lg4_bytes K m m' _ _ C); [|exact Fs]. intros x Hx. rewrite Hsv in Hx.
    change (Z.of_nat 104) with 104 in Hx. apply HUf; lg4_ar. }
  unfold c45_R in RP.
  pose proof (c45_canon_of_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs' RP) as CN.
  rewrite CN.
  exists (reg_get regs' 1), (reg_get regs' 5), (reg_get regs' 6), (reg_get regs' 7), (reg_get regs' 10),
    (reg_get regs' 11), (reg_get regs' 12), (reg_get regs' 13), (reg_get regs' 14), (reg_get regs' 15),
    (reg_get regs' 16), (reg_get regs' 17), s2, s3, s4, (reg_get regs' 28), (reg_get regs' 29),
    (reg_get regs' 30), (reg_get regs' 31), F, fc, m', P, N, kbs, mbs, gbs, j0, j1, j2.
  split; [reflexivity|]. split; [exact FC|]. split; [exact Hi|].
  split; [split; [exact (HF _ _ 64 Fp eq_refl ltac:(lg4_ar) ltac:(lg4_ar)) |
                  split; [exact (HF _ _ 16 Fc eq_refl ltac:(lg4_ar) ltac:(lg4_ar)) | exact Fs']]|].
  split; [exact Hc|].
  split; [exact (HF _ _ 8 B40 eq_refl ltac:(lg4_ar) ltac:(lg4_ar))|].
  split; [exact (HF _ _ 32 B40x eq_refl ltac:(lg4_ar) ltac:(lg4_ar))|].
  split; [exact (HF _ _ 8 B256 eq_refl ltac:(lg4_ar) ltac:(lg4_ar))|].
  split; [exact (HF _ _ 248 B256x eq_refl ltac:(lg4_ar) ltac:(lg4_ar))|].
  split; [exact KMG'|]. split; [exact KEEP'|]. split; [exact M1 | split; [exact M2 | exact M3]].
Qed.

(* free at 0x13af0 (own2), back at 0x13af4 *)
Lemma lg4_ad_fr2 : forall E i gp own1 own2 (K : Z -> Prop) R F fc m regs' m',
  lenv_ok E -> (forall x, lh_reg E x -> K x) ->
  c45_13af0 E i gp own1 own2 (MS R F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs)) ->
  regs_preserved R regs' -> lcarry K m m' ->
  mem_inv rsegs m' -> MemNorm.task_mem rsegs m' -> stk rsegs m' (e_S E - SLOT_STACK_Z) (e_S E - SLOT_FRAME) ->
  wr_at rsegs m' A_ERRNO 4 -> guard_m m' ->
  c45_13af4 E i gp own1 own2 (MS (Regs6ss.mkR_of regs') F (Z_to_bv 64 C45_FR2_RA) fc None m' (seg_rom rsegs)).
Proof.
  intros E i gp own1 own2 K R F fc m regs' m' HE HK H RP C M1 M2 M3 M4 M5.
  destruct H as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6 & F0 & fc0 & m0
    & P & N & kbs & mbs & gbs & j0 & j1 & j2 & EQ & FC & Hi & (Fp & Fc & Fs) & Hc & B40 & B40x & B256 & B256x
    & KMG & KEEP & MACH).
  pose proof (f_equal ms_regs EQ) as ER. pose proof (f_equal ms_fcsr EQ) as EF.
  pose proof (f_equal ms_mem EQ) as EM.
  cbn [ms_regs ms_fcsr ms_mem MS] in ER, EF, EM. subst R fc0 m0.
  pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsv).
  assert (HUf : forall x, e_S E - SLOT_FRAME <= x < e_S E -> K x).
  { intros x Hx. apply HK, lh_reg_frame. unfold lo_rng. lia. }
  destruct (lg4_kk E i kbs mbs gbs K m m' HE (fun x H _ => HK x H) C M4 M5 KMG KEEP) as [KMG' KEEP'].
  assert (HF : forall A cs n, rw_cells rsegs m A cs -> Z.of_nat (cells_size cs) = n ->
                 e_S E - SLOT_FRAME <= A -> A + n <= e_S E -> rw_cells rsegs m' A cs).
  { intros A cs n H En H1 H2. apply (lg4_rw K m m' A cs C); [|exact H]. intros x Hx. apply HUf. lia. }
  assert (Fs' : bytes_at rsegs m' (e_S E - 104) (e_saved E)).
  { apply (lg4_bytes K m m' _ _ C); [|exact Fs]. intros x Hx. rewrite Hsv in Hx.
    change (Z.of_nat 104) with 104 in Hx. apply HUf; lg4_ar. }
  unfold c45_R in RP.
  pose proof (c45_canon_of_preserved _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs' RP) as CN.
  rewrite CN.
  exists (reg_get regs' 1), (reg_get regs' 5), (reg_get regs' 6), (reg_get regs' 7), (reg_get regs' 10),
    (reg_get regs' 11), (reg_get regs' 12), (reg_get regs' 13), (reg_get regs' 14), (reg_get regs' 15),
    (reg_get regs' 16), (reg_get regs' 17), s2, s3, s4, (reg_get regs' 28), (reg_get regs' 29),
    (reg_get regs' 30), (reg_get regs' 31), F, fc, m', P, N, kbs, mbs, gbs, j0, j1, j2.
  split; [reflexivity|]. split; [exact FC|]. split; [exact Hi|].
  split; [split; [exact (HF _ _ 64 Fp eq_refl ltac:(lg4_ar) ltac:(lg4_ar)) |
                  split; [exact (HF _ _ 16 Fc eq_refl ltac:(lg4_ar) ltac:(lg4_ar)) | exact Fs']]|].
  split; [exact Hc|].
  split; [exact (HF _ _ 8 B40 eq_refl ltac:(lg4_ar) ltac:(lg4_ar))|].
  split; [exact (HF _ _ 32 B40x eq_refl ltac:(lg4_ar) ltac:(lg4_ar))|].
  split; [exact (HF _ _ 8 B256 eq_refl ltac:(lg4_ar) ltac:(lg4_ar))|].
  split; [exact (HF _ _ 248 B256x eq_refl ltac:(lg4_ar) ltac:(lg4_ar))|].
  split; [exact KMG'|]. split; [exact KEEP'|]. split; [exact M1 | split; [exact M2 | exact M3]].
Qed.

(* free(NULL) at either site: the registers and the memory as they were, at the return address *)
Lemma lg4_ad_fn1 : forall E i gp own2 R F fc m,
  c45_13ae8 E i gp 0 own2 (MS R F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs)) ->
  c45_13aec E i gp 0 own2 (MS R F (Z_to_bv 64 C45_FR1_RA) fc None m (seg_rom rsegs)).
Proof.
  intros E i gp own2 R F fc m (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6
    & F0 & fc0 & m0 & P & N & kbs & mbs & gbs & j0 & j1 & j2 & EQ & FC & Rest).
  pose proof (f_equal ms_regs EQ) as ER. pose proof (f_equal ms_fcsr EQ) as EF.
  pose proof (f_equal ms_mem EQ) as EM.
  cbn [ms_regs ms_fcsr ms_mem MS] in ER, EF, EM. subst R fc0 m0.
  exists (wz C45_FR1_RA), t0, t1, t2, (wz 0), a1, a2, a3, a4, a5, a6, a7, s2, s3, s4, t3, t4, t5, t6,
    F, fc, m, P, N, kbs, mbs, gbs, j0, j1, j2.
  split; [reflexivity|]. split; [exact FC | exact Rest].
Qed.

Lemma lg4_ad_fn2 : forall E i gp own1 R F fc m,
  c45_13af0 E i gp own1 0 (MS R F (Z_to_bv 64 LLVM_FREE) fc None m (seg_rom rsegs)) ->
  c45_13af4 E i gp own1 0 (MS R F (Z_to_bv 64 C45_FR2_RA) fc None m (seg_rom rsegs)).
Proof.
  intros E i gp own1 R F fc m (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & t3 & t4 & t5 & t6
    & F0 & fc0 & m0 & P & N & kbs & mbs & gbs & j0 & j1 & j2 & EQ & FC & Rest).
  pose proof (f_equal ms_regs EQ) as ER. pose proof (f_equal ms_fcsr EQ) as EF.
  pose proof (f_equal ms_mem EQ) as EM.
  cbn [ms_regs ms_fcsr ms_mem MS] in ER, EF, EM. subst R fc0 m0.
  exists (wz C45_FR2_RA), t0, t1, t2, (wz 0), a1, a2, a3, a4, a5, a6, a7, s2, s3, s4, t3, t4, t5, t6,
    F, fc, m, P, N, kbs, mbs, gbs, j0, j1, j2.
  split; [reflexivity|]. split; [exact FC | exact Rest].
Qed.
