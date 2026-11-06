From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import memcpy_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import
LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_early LLVMFuzzerTestOneInput_top LLVMFuzzerTestOneInput_exit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Section M.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FREE : forall fx' : YK11.FPState, @free_contract fx' rc B API.
Hypothesis MEMCPY : memcpy_contract.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis SINK : lf_sink_env B.

Definition llvm_entry_ok : Prop :=
  forall stk empty L0 A0 regs0 mem0 md0 ra p n b,
    llvm_ctx B API stk empty L0 A0 regs0 mem0 md0 ra p n b ->
    SR (ms_segs B) (mkCfg (mkst regs0 (Z_to_bv 64 LLVM_ENTRY) mem0 (seg_rom (ms_segs B))) md0)
      (fun c => llvm_J B API stk L0 A0 regs0 mem0 md0 p n b 0 1 c \/ llvm_X B API stk L0 A0 regs0 mem0 md0 b 1 c).

Definition llvm_cases_ok : Prop := forall op3, 0 <= op3 <= 3 -> llvm_case_ok B API op3.

Lemma llvm_case_pc_of : forall op, llvm_case_pc (Z.land op 3) = llvm_case_pc (Z.land op 3) /\ 0 <= Z.land op 3 <= 3.
Proof.
  intros op. split; [reflexivity|]. split; [apply Z.land_nonneg; lia|].
  pose proof (Z.land_ones op 2 ltac:(lia)) as E. change (Z.ones 2) with 3 in E. rewrite E.
  pose proof (Z.mod_pos_bound op (2 ^ 2) ltac:(lia)). lia.
Qed.

Lemma llvm_body : llvm_cases_ok -> llvm_join_ok B API ->
  forall stk empty L0 A0 regs0 mem0 md0 ra p n b,
    llvm_ctx B API stk empty L0 A0 regs0 mem0 md0 ra p n b ->
    forall (w : Z * nat) c, llvm_J B API stk L0 A0 regs0 mem0 md0 p n b (fst w) (snd w) c ->
    SR (ms_segs B) c (fun c' => (exists k', llvm_X B API stk L0 A0 regs0 mem0 md0 b k' c') \/
      exists w', (Z.to_nat (64 - fst w') < Z.to_nat (64 - fst w))%nat /\
        llvm_J B API stk L0 A0 regs0 mem0 md0 p n b (fst w') (snd w') c').
Proof.
  intros CASES JOIN stk empty L0 A0 regs0 mem0 md0 ra p n b CTX [i k] c HJ. cbn [fst snd] in HJ |- *.
  assert (Hi : 0 <= i <= 63).
  { destruct HJ as (fx' & regs & mem & md & L & A & r & fab & ip & inn & bs & j0 & j1 & j2 & _ & _ & _ & _ & _ & Hi & _). exact Hi. }
  eapply SR_bind; [exact (llvm_top_holds B API MEMCPY stk empty L0 A0 regs0 mem0 md0 ra p n b i k c CTX HJ)|].
  intros c1 HT.
  pose proof HT as (fx' & regs & mem & md & L & A & r & fab & ip & inn & bs & op & j0 & j1 & jm & E1 & _).
  pose proof (llvm_case_pc_of op) as [_ Hop].
  eapply SR_bind.
  { apply (CASES (Z.land op 3) Hop stk empty L0 A0 regs0 mem0 md0 ra p n b i k c1 CTX HT).
    exists (mkst regs (Z_to_bv 64 (llvm_case_pc (Z.land op 3))) mem (seg_rom (ms_segs B))), md.
    split; [exact E1 | reflexivity]. }
  intros c2 (k' & HK).
  eapply SR_mono; [exact (JOIN stk empty L0 A0 regs0 mem0 md0 ra p n b i k' c2 CTX HK)|].
  intros c3 [HJ3 | HX3].
  - right. exists (i + 1, k'). cbn [fst snd]. split; [lia | exact HJ3].
  - left. exists k'. exact HX3.
Qed.

Lemma llvm_loop : llvm_cases_ok -> llvm_join_ok B API ->
  forall stk empty L0 A0 regs0 mem0 md0 ra p n b,
    llvm_ctx B API stk empty L0 A0 regs0 mem0 md0 ra p n b ->
    forall i k c, llvm_J B API stk L0 A0 regs0 mem0 md0 p n b i k c ->
    SR (ms_segs B) c (fun c' => exists k', llvm_X B API stk L0 A0 regs0 mem0 md0 b k' c').
Proof.
  intros CASES JOIN stk empty L0 A0 regs0 mem0 md0 ra p n b CTX i k c HJ.
  apply (SR_loop (ms_segs B) (Z * nat) (fun w => Z.to_nat (64 - fst w))
           (fun w c => llvm_J B API stk L0 A0 regs0 mem0 md0 p n b (fst w) (snd w) c)
           (fun c' => exists k', llvm_X B API stk L0 A0 regs0 mem0 md0 b k' c')
           (llvm_body CASES JOIN stk empty L0 A0 regs0 mem0 md0 ra p n b CTX) (i, k) c HJ).
Qed.

Lemma llvm_n_bound : forall stk empty L A regs mem md ra p n,
  lib_pre B API stk empty L A regs mem md ra p n -> 0 <= n < 2 ^ 47.
Proof.
  intros stk empty L A regs mem md ra p n (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpl & _).
  pose proof YM05.alloc_ceiling_value as Hac.
  destruct Hpl as [[-> _] | [Hn (q & Hq & _)]]; [lia|].
  destruct (mr_blocks B _ (aa_laws API) L A mem md q n 0 HM Hq ltac:(lia)) as (_ & H1 & H2 & _). lia.
Qed.

Theorem LLVMFuzzerTestOneInput_holds_of : llvm_entry_ok -> llvm_cases_ok -> llvm_join_ok B API ->
  LLVMFuzzerTestOneInput_sr_contract B API.
Proof.
  intros ENTRY CASES JOIN BI j Hj ra empty stk Hk Hra L A regs mem md p n b Hpre Hsn Hsp Hres Hroom Hro Hrelro HGI Hfrm.
  pose proof (llvm_n_bound stk empty L A regs mem md ra p n Hpre) as Hnb.
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn11 & _).
  destruct (Z_lt_le_dec n (2 ^ 26)) as [Hsmall|Hbig].
  - assert (CTX : llvm_ctx B API stk empty L A regs mem md ra p n b)
      by (refine (conj BI (conj Hk (conj Hra (conj Hpre (conj Hsn (conj Hsp (conj Hres (conj Hroom
            (conj Hro (conj Hrelro (conj Hfrm Hsmall)))))))))))).
    eapply SR_bind; [exact (ENTRY stk empty L A regs mem md ra p n b CTX)|].
    intros c [HJ | HX].
    + eapply SR_bind; [exact (llvm_loop CASES JOIN stk empty L A regs mem md ra p n b CTX 0 1 c HJ)|].
      intros c' (k' & HX'). exact (llvm_exit_holds B API FREE ERRNO_LOW SINK stk empty L A regs mem md ra p n b j k' c' CTX HX').
    + exact (llvm_exit_holds B API FREE ERRNO_LOW SINK stk empty L A regs mem md ra p n b j 1 c CTX HX).
  - apply (llvm_early B API SINK j stk empty L A regs mem md ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm).
    rewrite Hn11. rewrite MState.unsigned_lit by lia. exact Hbig.
Qed.

End M.
