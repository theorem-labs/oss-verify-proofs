(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: the early path of LLVMFuzzerTestOneInput on the UBSan image (fuzz_decode.ubsan,
   entry 0x12cfc, frame 0x1f0), the sizes the harness refuses without an allocation (fuzz_decode.c,
   `if (size >= FUZZ_INPUT_MAX || size == 0) return 0;`, FUZZ_INPUT_MAX = 2^26). The same shape as libreac/fuzz_decode's
   released lib/U/Prog/LLVMFuzzerTestOneInput_early.v; the frame is 496 bytes, and the test also covers size = 0.
   - llvm_early_cond: the size test 0x12d38-0x12d44 (`lui a1, 0xfc000`; `add a2, s2, a1`; `addiw a1, a1, 1`;
     `bltu a2, a1`): a2 = size + (2^64 - 2^26) mod 2^64 is below 2^64 - 2^26 + 1 exactly when size = 0 or
     2^26 <= size (both directions).
   - llvm_early_evt: from 0x12cfc, `addi sp, sp, -0x1f0`, the thirteen saves of ra, s0..s11 at sp + 0x188 .. sp + 0x1e8,
     0x12d34 `mv s2, a1`, the size test taken to 0x13398, `mv a0, zero`, the thirteen restores, 0x133d0
     `addi sp, sp, 0x1f0` and 0x133d4 `ret`: the state at the return address with a0 = 0, every other register but
     a1 / a2 as at entry, and the memory changed only in the 496 bytes of the frame.
   - llvm_early: the same path as an SR step of the entry contract, to llvm_sr_post (no allocation, the frame
     released). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_fr.
Import ListNotations.
Open Scope Z_scope.

(* the size test: a2 = size - 2^26 mod 2^64 against the constant 2^64 - 2^26 + 1 *)
Lemma llvm_early_cond : forall u, 0 <= u < 2 ^ 64 ->
  ((u + (2 ^ 64 - 2 ^ 26)) mod 2 ^ 64 < 2 ^ 64 - 2 ^ 26 + 1 <-> u = 0 \/ 2 ^ 26 <= u).
Proof.
  intros u Hu. destruct (Z_lt_dec u (2 ^ 26)) as [Hlt|Hge].
  - rewrite Z.mod_small by lia. split; intros H; lia.
  - replace (u + (2 ^ 64 - 2 ^ 26)) with ((u - 2 ^ 26) + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. split; intros H; lia.
Qed.

(* the same test as the walk meets it at 0x12d44: a2 = size + -2^26 (`lui a1, 0xfc000`; `add a2, s2, a1`),
   a1 = -2^26 + 1 (`addiw a1, a1, 1`), compared unsigned *)
Lemma llvm_early_bltu : forall a1 : word,
  bv_ltu (Z_to_bv 64 (bv_unsigned a1 + -67108864)) (Z_to_bv 64 (-67108863)) = true <->
  (bv_unsigned a1 = 0 \/ 2 ^ 26 <= bv_unsigned a1).
Proof.
  intros a1. pose proof (bv_unsigned_in_range 64 a1) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in R.
  unfold bv_ltu. rewrite !unsigned_lit_wrap. rewrite Z.ltb_lt.
  replace ((-67108863) mod 2 ^ 64) with (2 ^ 64 - 2 ^ 26 + 1) by reflexivity.
  replace ((bv_unsigned a1 + -67108864) mod 2 ^ 64) with ((bv_unsigned a1 + (2 ^ 64 - 2 ^ 26)) mod 2 ^ 64).
  - exact (llvm_early_cond (bv_unsigned a1) R).
  - replace (bv_unsigned a1 + (2 ^ 64 - 2 ^ 26)) with ((bv_unsigned a1 + -67108864) + 1 * 2 ^ 64) by lia.
    apply Z.mod_add. lia.
Qed.

Lemma llvm_early_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 496 <= bv_unsigned sp -> mem_inv rsegs m ->
    (bv_unsigned a1 = 0 \/ 2 ^ 26 <= bv_unsigned a1) ->
    evt rsegs
      (fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 496, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12cfc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO MI H26.
  pose proof (munch_refl [(bv_unsigned sp - 496, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra1.
  carve_frame 496%nat ST.
  do 19 step.
  if_true_by (proj2 (llvm_early_bltu a1) H26).
  do 16 step.
  release_frame FR ST (bv_unsigned sp).
  finish.
Qed.

Section E.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis SINK : lf_sink_env B.

Lemma llvm_early : forall j stk empty L A regs mem md ra p n b,
  llvm_binds B API -> LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
  lib_pre B API stk empty L A regs mem md ra p n -> sink_none B mem md ->
  res_ok_slots A b -> ro_agree rsegs mem -> frm_zero fp_csr ->
  (bv_unsigned (YK11.getr regs 11) = 0 \/ 2 ^ 26 <= bv_unsigned (YK11.getr regs 11)) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs (Z_to_bv 64 LLVM_ENTRY) mem (seg_rom (ms_segs B))) md)
    (llvm_sr_post B API stk L A regs mem md ra p n b j).
Proof.
  intros j stk empty L A regs mem md ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm Hn.
  destruct BI as (SEGS & _ & _ & HGG & _ & AX).
  pose proof Hpre as (HM & HW & HB & HID & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn1 & Hpl & Hrod).
  pose proof (lf_fr_init B API stk empty L A regs mem md ra p n Hpre Hro) as FR0.
  unfold LLVM_K, LLVM_FRAME, ALLOC_STACK in Hk.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  assert (Esp : spZ regs = bv_unsigned (reg_get regs 2)) by reflexivity.
  assert (E11 : YK11.getr regs 11 = reg_get regs 11) by reflexivity.
  assert (E1 : YK11.getr regs 1 = reg_get regs 1) by reflexivity.
  pose proof (bv_unsigned_in_range _ (reg_get regs 2)) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  rewrite SEGS.
  eapply (llvm_run_norm fx regs (Z_to_bv 64 LLVM_ENTRY) mem md); [exact Hh | exact Hl | exact Hro | | |].
  - unfold Regs6ss.mkR_of, LLVM_ENTRY.
    apply llvm_early_evt with (lo := spZ regs - stk).
    + rewrite <- Esp. apply lf_stk; [lia | lia |].
      intros a Ha. unfold writable_at.
      assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
      rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem Hro)
                 (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
      rewrite <- SEGS. exact (Hstw a Ha).
    + lia.
    + exact (mem_inv_normalize rsegs mem).
    + rewrite <- E11. exact Hn.
  - intros ms (a1' & a2' & m'' & -> & _). do 5 eexists. reflexivity.
  - intros R F pc' fc m0' (a1' & a2' & m'' & HE & MU & WM & MI' & ST') regs' m' Hx Hrel Hsame.
    injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
    apply SR_ret.
    assert (MU' : munch [(bv_unsigned (reg_get regs 2) - 496, bv_unsigned (reg_get regs 2))] mem m')
      by exact (munch_rel rsegs _ mem (normalize rsegs mem) m' m'' (mem_rel_normalize rsegs mem Hro) Hrel Hsame MU).
    assert (WM' : wmono rsegs mem m')
      by exact (wmono_rel rsegs mem (normalize rsegs mem) m' m'' (mem_rel_normalize rsegs mem Hro) Hrel Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs mem m' Hro Hsame).
    assert (FR1 : lf_fr B API stk (spZ regs) L A mem md L A m' md).
    { eapply (lf_fr_evt B API SEGS AX HGG); [exact FR0 | lia | lia | exact MU' | exact WM' | exact Hro' |].
      intros x Hx0 NO. left.
      destruct (Z_le_dec (spZ regs - 496) x); destruct (Z_lt_dec x (spZ regs)); try lia;
        exfalso; apply NO; cbn [Frame.outside]; (split; [lia | exact I]). }
    assert (G10 : YK11.getr regs' 10 = Z_to_bv 64 0).
    { rewrite (lf_getr_eqv _ _ _ Hx). reflexivity. }
    assert (RP : regs_preserved regs regs').
    { intros r Hr. rewrite (lf_getr_eqv _ _ _ Hx). unfold callee_saved in Hr.
      assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                    r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      repeat (destruct Hr' as [-> | Hr']; [reflexivity|]). subst. reflexivity. }
    destruct (lf_post B API SINK stk empty L A regs mem md ra p n L A regs' m' md Hpre Hsn FR1 G10 RP)
      as (Hpost & Hsn' & Hpay & MI2).
    exists (mkFP fp_regs fp_csr), L, A, regs', m', md.
    split; [rewrite SEGS, <- E1, Hra1, (lf_ret_pc _ Hra); reflexivity|].
    split; [exact Hfrm|]. split; [exact Hpost|]. split; [exact Hsn'|].
    split; [exact Hres|]. split; [exact Hpay|]. split; [exact MI2 | exact I].
Qed.

End E.
