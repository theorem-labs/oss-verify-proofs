(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/U/Prog/LLVMFuzzerTestOneInput.v, with its module paths changed; 39 of its 68 lines of code are new or changed and 1215 lines of the source are left out. *)
(* fuzz_lock's LLVMFuzzerTestOneInput (fuzz_lock.c:185-186) in fuzz_lock.plain, 0x12b78: size < 2 or size >= 2^26
   returns 0 before the frame, in the form of libreac/fuzz_decode's lib/Prog/LLVMFuzzerTestOneInput_early.v (release
   25e3d17bdb50). Written by Theorem Labs. *)
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
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_fr lt_segs.
Import ListNotations.
Open Scope Z_scope.

Section E.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis SINK : lf_sink_env B.

Lemma llvm_n_bound : forall stk empty L A regs mem md ra p n,
  lib_pre B API stk empty L A regs mem md ra p n -> 0 <= n < 2 ^ 47.
Proof.
  intros stk empty L A regs mem md ra p n (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpl & _).
  pose proof YM05.alloc_ceiling_value as Hac.
  destruct Hpl as [[-> _] | [Hn (q & Hq & _)]]; [lia|].
  destruct (mr_blocks B _ (aa_laws API) L A mem md q n 0 HM Hq ltac:(lia)) as (_ & H1 & H2 & _). lia.
Qed.

Lemma llvm_early : forall j stk empty L A regs mem md ra p n pl b,
  llvm_binds B API -> LLVM_K <= stk -> YK0s.ret_ok (Z_to_bv 64 ra) ->
  lib_pre B API stk empty L A regs mem md ra p n -> n = Z.of_nat (length pl) -> sink_none B mem md ->
  res_ok_slots A b -> ro_agree rsegs mem -> frm_zero fp_csr ->
  n < 2 \/ 2 ^ 26 <= n ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs (Z_to_bv 64 LLVM_ENTRY) mem (seg_rom (ms_segs B))) md)
    (llvm_sr_post B API stk L A regs mem md ra p n pl b j).
Proof.
  intros j stk empty L A regs mem md ra p n pl b BI Hk Hra Hpre Hnl Hsn Hres Hro Hfrm Hn.
  destruct BI as (SEGS & _ & _ & HGG & _ & AX).
  pose proof (llvm_n_bound stk empty L A regs mem md ra p n Hpre) as Hnb.
  pose proof Hpre as (HM & HW & HB & HID & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn1 & Hpl & Hrod).
  pose proof (lf_fr_init B API stk empty L A regs mem md ra p n Hpre Hro) as FR0.
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  assert (E11 : reg_get regs 11 = Z_to_bv 64 n) by exact Hn1.
  assert (E1 : YK11.getr regs 1 = reg_get regs 1) by reflexivity.
  rewrite SEGS.
  eapply (llvm_run fx regs (Z_to_bv 64 LLVM_ENTRY) mem md); [exact Hh | exact Hl | | |].
  - unfold Regs6ss.mkR_of, LLVM_ENTRY. rewrite E11. apply lt_early_evt; lia.
  - intros ms (a2' & a3' & ->). do 5 eexists. reflexivity.
  - intros R F pc' fc m' (a2' & a3' & HE) regs' Hx.
    injection HE as ER EF EP EC EM. subst R F pc' fc m'.
    apply SR_ret.
    assert (G10 : YK11.getr regs' 10 = Z_to_bv 64 (lock_ret pl)).
    { rewrite (lf_getr_eqv _ _ _ Hx), (lock_ret_early pl) by lia. reflexivity. }
    assert (RP : regs_preserved regs regs').
    { intros r Hr. rewrite (lf_getr_eqv _ _ _ Hx). unfold callee_saved in Hr.
      assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
                    r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      repeat (destruct Hr' as [-> | Hr']; [reflexivity|]). subst. reflexivity. }
    destruct (lf_post B API SINK stk empty L A regs mem md ra p n L A regs' mem md (lock_ret pl) Hpre Hsn FR0 G10 RP)
      as (Hpost & Hsn' & Hpay & MI2).
    exists (mkFP fp_regs fp_csr), L, A, regs', mem, md.
    split; [rewrite SEGS, <- E1, Hra1, (lf_ret_pc _ Hra); reflexivity|].
    split; [exact Hfrm|]. split; [exact Hpost|]. split; [exact Hsn'|].
    split; [exact Hres|]. split; [exact Hpay|]. split; [exact MI2 | exact I].
Qed.

End E.
