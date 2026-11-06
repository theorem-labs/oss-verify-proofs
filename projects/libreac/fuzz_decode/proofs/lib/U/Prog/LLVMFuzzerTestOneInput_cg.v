From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import memcpy_c reac_frame_is_reac_c
  reac_frame_clean_len_c check_round_trip_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr
  LLVMFuzzerTestOneInput_early fd_segments_c fd_glue fd_seghelp fd_exit fd_entry.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_cfb fd_segments_ccf check_round_trip_ccf LLVMFuzzerTestOneInput_early_cg fd_glue_cg fd_exit_cg fd_entry_cg.
Import ListNotations.
Open Scope Z_scope.

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
Context (MC : memcpy_contract) (IIR : reac_frame_is_reac_contract) (ICL : reac_frame_clean_len_contract).
Hypothesis DOWN : forall fx' : YK11.FPState, fd_down_contract_cf (fx := fx') B API.
Hypothesis UP : forall fx' : YK11.FPState, fd_up_contract_cf (fx := fx') B API.

Lemma llvm_n_bound_cf : forall stk empty L A regs mem md ra p n,
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
  pose proof (llvm_n_bound_cf stk empty L A regs mem md ra p n Hpre) as Hnb.
  pose proof Hpre as (HM & HW & HB & HID & Hra1 & Hal & Hceil & H63 & Hstw & Htp & Herr & Hp & Hn11 & Hpl0 & Hrod).
  destruct (Z_lt_le_dec n (2 ^ 26)) as [Hsmall|Hbig].
  2:{ apply (llvm_early_cf B API SINK j stk empty L A regs mem md ra p n b BI Hk Hra Hpre Hsn Hres Hro Hfrm).
      rewrite Hn11. rewrite MState.unsigned_lit by lia. exact Hbig. }
  pose proof BI as (SEGS & HMAL & HFRE & HGG & HG & AX).
  pose proof Hk as Hk'.
  unfold LLVM_K, LLVM_FRAME, CRT_STACK, CRT_FRAME, CALLOC_STACK, ALLOC_STACK in Hk'.
  pose proof YM05.alloc_ceiling_value as Hac.
  assert (ENV : fd_env B API) by (split; [exact BI | exact ERRNO_LOW]).
  eapply (SRcf_bind B); [eapply fd_entry_holds_cf; eassumption|].
  intros c (fx1 & L1 & A1 & regs1 & mem1 & md1 & frame & len & mode & nch & ns & fr & u1 & u2 & u3 & -> & Hfrm1
    & INV1 & H9 & H25 & H19 & MODE & G13 & G14 & FR1 & Hnf & HC1).
  eapply (SRcf_bind B).
  { exact (DOWN fx1 ENV L1 A1 regs1 mem1 md1 (sb_malloc b len) (spZ regs) len frame mode nch ns fr
      INV1 Hfrm1 H9 H25 H19 MODE). }
  intros c (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & Hfrm2 & INV2 & G23 & G24 & BL2 & KEPT2 & G28).
  eapply (SRcf_bind B).
  { exact (UP fx2 ENV L2 A2 regs2 mem2 md2 (sb_malloc b len) (spZ regs) len frame fr INV2 Hfrm2 G28). }
  intros c (fx3 & L3 & A3 & regs3 & mem3 & md3 & -> & Hfrm3 & INV3 & G33 & G34 & BL3 & KEPT3 & G325).
  unfold fd_exit_regs in G325.
  pose proof INV3 as (HM3 & HW3 & HB3 & Hal3 & Hceil3 & H633 & Hstw3 & Hfw3 & Htp3 & Herr3 & HID3 & Hro3 & Hh3
    & Hl3 & Hsp3 & Hlen3 & HLEN3 & Hin3 & Hblk3 & Hres3 & Hroom3).
  unfold fd_kept in KEPT2, KEPT3.
  assert (FRK : lf_fr B API (LLVM_K - FD_KEEP) (spZ regs - FD_KEEP) L1 A1 mem1 md1 L3 A3 mem3 md3).
  { eapply lf_fr_trans with (stk' := LLVM_K - FD_KEEP) (S' := spZ regs - FD_KEEP).
    all: try eassumption.
    all: unfold LLVM_K, LLVM_FRAME, CRT_STACK, CRT_FRAME, CALLOC_STACK, ALLOC_STACK, FD_KEEP; lia. }
  assert (FRG : lf_fr B API stk (spZ regs) L A mem md L3 A3 mem3 md3).
  { eapply lf_fr_trans with (stk' := LLVM_K - FD_KEEP) (S' := spZ regs - FD_KEEP).
    all: try eassumption.
    all: unfold LLVM_K, LLVM_FRAME, CRT_STACK, CRT_FRAME, CALLOC_STACK, ALLOC_STACK, FD_KEEP; lia. }
  pose proof FRK as (_ & _ & _ & _ & _ & HhighK & _).
  assert (SZ : cells_size (C4 u1 :: C4 u2 :: C4 u3 :: llvm_saved_cells regs) = 116%nat) by reflexivity.
  assert (KE : forall a, spZ regs - 116 <= a < spZ regs - 116 +
      Z.of_nat (cells_size (C4 u1 :: C4 u2 :: C4 u3 :: llvm_saved_cells regs)) ->
     mbyte rsegs mem3 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem3 a)).
  { intros a Ha. rewrite SZ in Ha. rewrite <- SEGS. apply HhighK;
      unfold LLVM_K, LLVM_FRAME, CRT_STACK, CRT_FRAME, CALLOC_STACK, ALLOC_STACK, FD_KEEP; lia. }
  assert (KW : forall a, spZ regs - 176 <= a < spZ regs - 116 -> writable_at rsegs mem3 a).
  { intros a Ha. rewrite <- SEGS. apply Hfw3. unfold FD_FRAME. lia. }
  destruct (exit_cells mem1 mem3 (spZ regs) u1 u2 u3 (llvm_saved_cells regs) HC1 KE KW
    ltac:(unfold LF_RES_TOP; lia)) as [jx HCX].
  assert (G32 : YK11.getr regs3 2 = Z_to_bv 64 (spZ regs - 176)).
  { unfold spZ at 1 in Hsp3. unfold FD_FRAME in Hsp3. rewrite <- Hsp3. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (G33' : YK11.getr regs3 3 = YK11.getr regs 3) by (rewrite G33, G23; exact G13).
  assert (G34' : YK11.getr regs3 4 = YK11.getr regs 4) by (rewrite G34, G24; exact G14).
  unfold FD_UP_END.
  eapply fx_exit_holds_cf with (stk := stk) (empty := empty) (L0 := L) (A0 := A) (regs0 := regs) (mem0 := mem)
    (md0 := md) (ra := ra) (p := p) (n := n) (b := b) (j := j) (fx' := fx3) (regs := regs3) (mem := mem3)
    (md := md3) (L := L3) (A := A3) (frame := frame) (len := len) (jx := jx).
  all: eassumption.
Qed.

End M.
