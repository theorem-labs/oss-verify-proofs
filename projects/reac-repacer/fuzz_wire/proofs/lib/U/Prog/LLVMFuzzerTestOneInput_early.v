(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/U/Prog/LLVMFuzzerTestOneInput_early_cg.v, with its module paths and numbers changed; 56 of its 130 lines of code are new or changed and 12 lines of the source are left out. *)
(* Modified by Theorem Labs: reac-repacer/fuzz_uci's lib/U/Prog/LLVMFuzzerTestOneInput_early.v (6874bc78b1f,
   itself libreac/fuzz_decode's released early-exit walk) at fuzz_wire's module paths and UBSan image values:
   entry 0x12dc0, frame 0x40; 13 instructions to and with the `bltu` at 0x12df0 (addi sp, 8 sd, lui, add, addiw,
   bltu), the taken branch to 0x12f04, then 11 (mv a0 zero, 8 ld, addi sp, ret). It proves the return 0 of
   fuzz_wire.c:256-257 for size = 0 or size >= 64 MiB; llvm_early_cond is this image's test.
   No UBSan check is on this path (the checks of data, 0x12df8 / 0x12e00, come after the test). *)
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
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.U.Prog Require Import check_copy_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr.
Import ListNotations.
Open Scope Z_scope.
(* The early test, `lui a2, 0xfc000; add a3, a1, a2; addiw a2, a2, 1; bltu a3, a2`: size - 2^26 <u 2^64 - 2^26 + 1
   (mod 2^64) holds iff size = 0 or 2^26 <= size (fuzz_wire.c:256-257). *)
Lemma llvm_early_cond : forall u, 0 <= u < 2 ^ 64 -> u = 0 \/ 2 ^ 26 <= u ->
  bv_ltu (Z_to_bv 64 (u + -67108864)) (Z_to_bv 64 (-67108863)) = true.
Proof.
  intros u Hu Hc. unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  apply Z.ltb_lt. Z.div_mod_to_equations. lia.
Qed.

Ltac llvm_early_branch u Hu Hc :=
  first [ if_true_by (llvm_early_cond u Hu Hc)
        | lazymatch goal with
          | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
              replace c with true;
              [ cbv iota
              | symmetry; unfold c_ltu, bv_ltu; rewrite ?Z_to_bv_unsigned, ?unsigned_lit_wrap;
                unfold bv_wrap, bv_modulus; apply Z.ltb_lt; Z.div_mod_to_equations; lia ]
          end ].

Lemma llvm_early_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp -> mem_inv rsegs m ->
    bv_unsigned a1 = 0 \/ 2 ^ 26 <= bv_unsigned a1 ->
    evt rsegs
      (fun ms' => exists (a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2' a3' a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12dc0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO MI H26.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra1.
  carve_frame 64%nat ST.
  do 13 step.
  llvm_early_branch (bv_unsigned a1) ltac:(lia) H26.
  do 11 step.
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
  bv_unsigned (YK11.getr regs 11) = 0 \/ 2 ^ 26 <= bv_unsigned (YK11.getr regs 11) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs (Z_to_bv 64 LLVM_ENTRY) mem (seg_rom (ms_segs B))) md)
    (llvm_sr_post B API stk L A regs mem md ra p n b j).
Proof.
  intros j stk empty L A regs mem md ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm Hn.
  destruct BI as (SEGS & _ & _ & HGG & _ & AX).
  pose proof Hpre as (HM & HW & HB & HID & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn1 & Hpl & Hrod).
  pose proof (lf_fr_init B API stk empty L A regs mem md ra p n Hpre Hro) as FR0.
  unfold LLVM_K, LLVM_FRAME, CC_STACK, CHECK_COPY_FRAME, ALLOC_STACK in Hk.
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
  - intros ms (a2' & a3' & m'' & -> & _). do 5 eexists. reflexivity.
  - intros R F pc' fc m0' (a2' & a3' & m'' & HE & MU & WM & MI' & ST') regs' m' Hx Hrel Hsame.
    injection HE as ER EF EP EC EM. subst R F pc' fc m0'.
    apply SR_ret.
    assert (MU' : munch [(bv_unsigned (reg_get regs 2) - 64, bv_unsigned (reg_get regs 2))] mem m')
      by exact (munch_rel rsegs _ mem (normalize rsegs mem) m' m'' (mem_rel_normalize rsegs mem Hro) Hrel Hsame MU).
    assert (WM' : wmono rsegs mem m')
      by exact (wmono_rel rsegs mem (normalize rsegs mem) m' m'' (mem_rel_normalize rsegs mem Hro) Hrel Hsame WM).
    assert (Hro' : ro_agree rsegs m') by exact (ro_agree_same rsegs mem m' Hro Hsame).
    assert (FR1 : lf_fr B API stk (spZ regs) L A mem md L A m' md).
    { eapply (lf_fr_evt B API SEGS AX HGG); [exact FR0 | lia | lia | exact MU' | exact WM' | exact Hro' |].
      intros x Hx0 NO. left.
      destruct (Z_le_dec (spZ regs - 64) x); destruct (Z_lt_dec x (spZ regs)); try lia;
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
