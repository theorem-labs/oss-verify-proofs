(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/U/Prog/LLVMFuzzerTestOneInput_early_cg.v, with its module paths and numbers changed; 37 of its 94 lines of code are new or changed and 29 lines of the source are left out. *)
(* fuzz_lock.ubsan's LLVMFuzzerTestOneInput on a size below 2 or of 2 ^ 26 and more: it returns 0 and writes
   only its own frame. The shape of libreac/fuzz_decode's released lib/U/Prog/LLVMFuzzerTestOneInput_early.v
   (25e3d17bdb50) over lt_segs.v's lt_early. Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.U.Prog Require Import check_no_overread_c check_lookup_c LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_fr lt_segs.
Import ListNotations.
Open Scope Z_scope.

Section E.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis SINK : lf_sink_env B.

Lemma llvm_early : forall j stk empty L A regs mem md ra p n pl b,
  llvm_binds B API -> LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
  lib_pre B API stk empty L A regs mem md ra p n -> sink_none B mem md ->
  res_ok_slots A b -> ro_agree rsegs mem -> frm_zero fp_csr ->
  n = Z.of_nat (length pl) -> (n < 2 \/ 2 ^ 26 <= n) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs (Z_to_bv 64 LLVM_ENTRY) mem (seg_rom (ms_segs B))) md)
    (llvm_sr_post B API (lock_ret pl) stk L A regs mem md ra p n b j).
Proof.
  intros j stk empty L A regs mem md ra p n pl b BI Hk Hra Hpre Hsn Hres Hro Hfrm Hn HC.
  destruct BI as (SEGS & _ & _ & HGG & _ & AX).
  pose proof Hpre as (HM & HW & HB & HID & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn1 & Hpl & Hrod).
  pose proof (lf_fr_init B API stk empty L A regs mem md ra p n Hpre Hro) as FR0.
  unfold LLVM_K, LLVM_FRAME, CL_STACK, CL_FRAME, ALLOC_STACK in Hk.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  assert (Esp : spZ regs = bv_unsigned (reg_get regs 2)) by reflexivity.
  assert (E11 : YK11.getr regs 11 = reg_get regs 11) by reflexivity.
  assert (E1 : YK11.getr regs 1 = reg_get regs 1) by reflexivity.
  pose proof (bv_unsigned_in_range _ (reg_get regs 2)) as Rsp. unfold bv_modulus in Rsp.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp.
  assert (HN64 : 0 <= n < 2 ^ 64).
  { rewrite Hn. pose proof (Zle_0_nat (length pl)). split; [lia|].
    destruct Hpl as [[-> _]|[Hn0 (q & Hq & _)]]; [lia|].
    destruct (mr_blocks B _ (aa_laws API) L A mem md q n 0 HM Hq ltac:(lia)) as (_ & H1 & H2 & _). lia. }
  rewrite SEGS.
  eapply (llvm_run_norm fx regs (Z_to_bv 64 LLVM_ENTRY) mem md); [exact Hh | exact Hl | exact Hro | | |].
  - unfold Regs6ss.mkR_of, LLVM_ENTRY.
    assert (E10 : reg_get regs 10 = Z_to_bv 64 p) by exact Hp.
    assert (E11' : reg_get regs 11 = Z_to_bv 64 n) by exact Hn1.
    rewrite E10, E11'.
    apply (lt_early (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
             (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19)
             (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24)
             (reg_get regs 25) (reg_get regs 26) (reg_get regs 27)
             (reg_get regs 28) (reg_get regs 29) (reg_get regs 30) (reg_get regs 31)
             (@fp_regs fx) (@fp_csr fx) (normalize rsegs mem) p n (spZ regs - stk) pl).
    all: try exact HC. all: try (symmetry; exact Hn). all: try apply mem_inv_normalize. all: try lia.
    apply lf_stk; [lia | lia |].
    intros a Ha. unfold writable_at.
    assert (Hni : ~ in_img B a) by (intros Hi; pose proof (lf_in_img_top B a SEGS Hi); lia).
    rewrite (wview_rel_rw rsegs mem (normalize rsegs mem) _ (mem_rel_normalize rsegs mem Hro)
               (lf_ro_addr_out B a SEGS Hni ltac:(lia))).
    pose proof (Hstw a Ha) as HWa. unfold writable_at in HWa. rewrite SEGS in HWa. exact HWa.
  - intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & u3' & u4' & u5' & u6' & m'' & -> & _). do 5 eexists. reflexivity.
  - intros R F pc' fc m0' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & u3' & u4' & u5' & u6' & m'' & HE & MU & WM) regs' m' Hx Hrel Hsame.
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
    assert (G10 : YK11.getr regs' 10 = Z_to_bv 64 (lock_ret pl)).
    { rewrite (lf_getr_eqv _ _ _ Hx). rewrite (lock_ret_early n pl ltac:(symmetry; exact Hn) HC).
      reflexivity. }
    assert (RP : regs_preserved regs regs').
    { intros r Hr. rewrite (lf_getr_eqv _ _ _ Hx). unfold callee_saved in Hr.
      assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                    r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      repeat (destruct Hr' as [-> | Hr']; [reflexivity|]). subst. reflexivity. }
    destruct (lf_post B API SINK stk empty L A regs mem md ra p n (lock_ret pl) L A regs' m' md Hpre Hsn FR1 G10 RP)
      as (Hpost & Hsn' & Hpay & MI2).
    exists (mkFP fp_regs fp_csr), L, A, regs', m', md.
    split; [rewrite SEGS, <- E1, Hra1, (lf_ret_pc _ Hra); reflexivity|].
    split; [exact Hfrm|]. split; [exact Hpost|]. split; [exact Hsn'|].
    split; [exact Hres|]. split; [exact Hpay|]. split; [exact MI2 | exact I].
Qed.

End E.
