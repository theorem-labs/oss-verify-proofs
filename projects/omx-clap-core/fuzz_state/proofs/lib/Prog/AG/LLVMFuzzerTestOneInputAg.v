From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require Import Contract Img0 FrameAPI AllocSlots AllocRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require Import Ledger GIInit KindBGlue SlotInv SlotDefs
  SlotStep SlotStepA AG.SlotStepBAg AG.SlotStepCAg AG.SlotStepDAg AG.SlotStepEAg AG.SlotStepFAg AG.SlotStepGAg
  LLVMFuzzerTestOneInput AG.StatementHaltsAg
  LLVMFuzzerTestOneInput_c memchr_c memcpy_c fuzz_alloc_live_c fuzz_alloc_peak_reset_c fuzz_alloc_peak_c
  check_bounded_alloc_c check_reject_clean_c check_no_overread_c preset_base64_decode_c check_as_written_c
  check_round_trip_c check_reject_clean_starved_c fuzz_free_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require HsKindB.
Import ListNotations.
Local Open Scope Z_scope.

(* The slot contract of entry_fn (plain, 0x1331c) at the agreement room (AgreeCap.v: sb_cap = CAP_AG): copy by
   script of LLVMFuzzerTestOneInput.slot_run and LLVMFuzzerTestOneInput_holds over the step lemmas of
   AG/SlotStepBAg..GAg, from frame_facts_plain_ag. The callee contracts are LLVMFuzzerTestOneInput.slot_callees. *)

Definition slot_callees_plain_ag : Prop :=
  forall (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head) (SK : sink_syms)
    (empty : Z),
    frame_facts_plain_ag B API LS SH SK empty -> forall (rc : RunCeil) (fx : FPState), @slot_callees fx rc B (API rc).

Section Asm.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variable B : malloc_syms.
Variable API : AllocAPI B.

Lemma slot_run_ag : slot_env B API -> (forall fx' : YK11.FPState, @slot_callees fx' rc B API) ->
  (forall fx' : YK11.FPState, @frame_allocator rc fx' B API) ->
  forall regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j ra b,
  slot_start B API regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j -> getr regs0 1 = Z_to_bv 64 ra ->
  res_ok_slots A0 b -> slot_bnd_ag b -> lib_delta (Z.of_nat (length pl)) b = b -> frm_zero fp_csr ->
  SR (ms_segs B) (mkCfg (mkst regs0 (Z_to_bv 64 0x1331c) mem0 (seg_rom (ms_segs B))) md0)
    (slot_fin B API regs0 L0 A0 mem0 md0 ra p0 (Z.of_nat (length pl)) b j).
Proof.
  intros ENV CAL FA regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j ra b HS HRA RES HB LD FZ.
  pose proof (CAL fx) as (MEMCHR & MEMCPY & FAL & FAPR & FAP & CBA & CRC & CNO & DEC & CAW & CRT & _ & _).
  pose proof (FA fx) as (MALC & _).
  apply (step_A B API ENV MEMCHR regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j ra b HS HRA RES LD FZ).
  intros L1 A1 regs1 mem1 md1 H1.
  apply (step_c0 B API ENV CNO regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L1 A1 regs1 mem1 md1 _ HS HB H1).
  intros L2 A2 regs2 mem2 md2 H2.
  apply (step_mal B API ENV MALC MEMCPY FAL FAPR regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L2 A2 regs2 mem2 md2 _
    HS HB H2).
  intros L3 A3 regs3 mem3 md3 H3.
  apply (step_dec B API ENV DEC FAP CBA regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L3 A3 regs3 mem3 md3 _ HS HB H3).
  intros L4 A4 regs4 mem4 md4 H4.
  assert (TAIL : forall (f : YK11.FPState) K L5 A5 regs5 mem5 md5, K <= 72 ->
            @at_pd f rc B API 0x1340c K (fun _ => True) regs0 L0 A0 mem0 md0 pl cnt0 b L5 A5 regs5 mem5 md5 ->
            SR (ms_segs B) (mkCfg (@mkst f regs5 (Z_to_bv 64 0x13d84) mem5 (seg_rom (ms_segs B))) md5)
              (slot_fin B API regs0 L0 A0 mem0 md0 ra p0 (Z.of_nat (length pl)) b j)).
  { intros f K L5 A5 regs5 mem5 md5 HK H5.
    pose proof (CAL f) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRS & FF).
    pose proof (FA f) as (_ & FRC & _).
    apply (step_c5 B API ENV CRS regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L5 A5 regs5 mem5 md5 K _ HS HB HK H5).
    intros L6 A6 regs6 mem6 md6 H6.
    apply (step_ff B API ENV FF regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L6 A6 regs6 mem6 md6 _ HS H6).
    intros L7 A7 regs7 mem7 md7 H7.
    exact (step_fr B API ENV FRC regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j ra b L7 A7 regs7 mem7 md7 HS HRA LD H7). }
  apply (step_c2 B API ENV CAW CRC regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L4 A4 regs4 mem4 md4 _ HS HB
    (at_c2_pd B API regs0 L0 A0 mem0 md0 pl cnt0 b L4 A4 regs4 mem4 md4 H4)).
  - intros L5 A5 regs5 mem5 md5 H5. exact (TAIL fx 4 L5 A5 regs5 mem5 md5 ltac:(lia) H5).
  - intros L5 A5 regs5 mem5 md5 H5.
    apply (step_c4 B API ENV CRT regs0 L0 A0 mem0 md0 p0 pl peak0 cnt0 j b L5 A5 regs5 mem5 md5 _ HS HB H5).
    intros fx' L6 A6 regs6 mem6 md6 _ H6. exact (TAIL fx' 72 L6 A6 regs6 mem6 md6 ltac:(lia) H6).
Qed.

End Asm.

Theorem LLVMFuzzerTestOneInput_ag_holds : slot_callees_plain_ag -> slot_premise_plain_ag.
Proof.
  intros CAL B API LS SH SK empty FF rc fx.
  pose proof FF as (SEG & MAL & FRE & _ & _ & ERR & GRD & GGD & CTX & LCK & LIBC & SZC & SMC & MDC & DBJ & TP & EOFF &
    _ & VML & DBL & SKH & SKL & SKT & EMPV & _ & _ & FG & _ & LIBK & LD & LR & FA).
  pose proof (FA rc fx) as (_ & _ & _ & _ & _ & BSP & _ & _ & _ & _ & _ & _ & _ & AX & OWN & _).
  assert (ENV : slot_env B (API rc)).
  { split; [exact SEG|]. split; [exact MAL|]. split; [exact FRE|]. split; [exact (ERR rc)|].
    split; [exact AX|]. split; [exact BSP|].
    split; [exact (omx_free B (API rc) SEG AX OWN FG)|].
    exact (sink_facts B SEG CTX LCK LIBC GGD GRD DBJ SZC SMC MDC TP EOFF VML DBL SKH SKL SKT). }
  unfold fuzz_state_slot_contract. intros j ra Hj Hra.
  unfold lib_contract_g. intros L A regs mem md p n pl b K PRE GI _ RA _ FZ HK.
  rewrite LIBK.
  destruct (start_of B (API rc) empty L A regs mem md ra p n pl b j EMPV Hj Hra PRE GI RA) as (peak0 & cnt0 & HS).
  pose proof PRE as ((_ & _ & _ & _ & R1 & _) & Hn & _ & RES & ROOM & _).
  assert (HB : slot_bnd_ag b) by exact (LR b n ROOM).
  assert (CALL : forall fx' : FPState, @slot_callees fx' rc B (API rc)) by (intros fx'; exact (CAL B API LS SH SK empty FF rc fx')).
  assert (FAL : forall fx' : FPState, @frame_allocator rc fx' B (API rc)) by (intros fx'; exact (FA rc fx')).
  subst n.
  apply (slot_run_ag B (API rc) ENV CALL FAL regs L A mem md p pl peak0 cnt0 j ra b HS R1 RES HB (LD _ b) FZ).
  intros c' Hc. apply (HK (LL 0 (m_fs md) []) c'). exact Hc.
Qed.
