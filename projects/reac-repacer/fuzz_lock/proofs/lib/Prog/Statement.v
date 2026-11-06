(* fuzz_lock's plain halting statement from the slot contract of LLVMFuzzerTestOneInput and the frame step of
   FrameRet.v (frame_ret_hyp, for a return of 0 or -1), in the form of libreac/fuzz_decode's lib/Prog/Statement.v
   (release 25e3d17bdb50), which concludes from FrameAPI.v frame_plain. Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Reusable Require Import YK11 YK0s YK15 YM05 YO0f YO0d YO09 YO0o
  YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_repacer.fuzz_lock.lib.Prog Require Import check_lookup_c FrameRet LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_fr.
From OSSVerify.reac_repacer.fuzz_lock Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

(* the allocator and sink facts LLVMFuzzerTestOneInput's walk takes *)
Definition llvm_frame (rc : RunCeil) (B : malloc_syms) (API : AllocAPI B) (SH : sink_head) (SK : sink_syms) : Prop :=
  (forall fx : FPState, @frame_allocator rc fx B API) /\ errno_addr B + 4 <= @alloc_ceiling rc /\
  @lf_sink_env B SH SK.

Definition slot_contract_all : Prop :=
  forall (rc : RunCeil) (fx : FPState) (LS : lib_shape) (B : malloc_syms) (API : AllocAPI B)
         (SH : sink_head) (SK : sink_syms),
    llvm_frame rc B API SH SK ->
    LLVMFuzzerTestOneInput_contract B API.

Lemma llvm_find_img_range : forall B lo n a, ms_segs B = rsegs -> find_segment rsegs lo n <> None ->
  lo <= a < lo + n -> in_img B a.
Proof.
  intros B lo n a HS E Ha. destruct (find_segment rsegs lo n) as [seg|] eqn:F; [|contradiction].
  destruct (lf_find_segment_in rsegs lo n seg F) as (Hin & H1 & H2).
  destruct (lf_rsegs_seg seg Hin) as (R1 & R2 & R3).
  split; [rewrite HS; exact lf_rsegs_nonnil|].
  exists (segment_reservation seg). split; [rewrite HS; unfold segments_reserved; apply in_map; exact Hin | lia].
Qed.

(* The stdout sink words of fuzz_lock.plain (FrameAPI.v: ofl_head 0x4e390, ofl_lock 0x4e388, threaded = libc + 1 at
   0x4df60) lie in [0x4df60, 0x4df60 + 0x438), inside the image's data segment, and outside the allocator's words. *)
Lemma lock_sink_env : forall (B : malloc_syms) (SH : sink_head) (SK : sink_syms),
  ms_segs B = rsegs -> ms_guard B = 0x4df40 -> ms_got_guard B = 0x1c958 ->
  ms_ctx B = 0x4dfd8 -> ms_lock B = 0x4dfd0 -> ms_libc B = 0x4df60 -> ms_size_classes B = 0x10434 ->
  ms_small_cnt B = 0x10494 -> ms_med_cnt B = 0x104af -> ms_debruijn B = 0x10414 -> ms_tp B = 0x2dcd0 ->
  ms_errno_off B = -164 -> ms_vmlock B = None -> ms_debruijn_len B = 32 ->
  @sk_ofl_head SH = 0x4e390 -> @sk_ofl_lock SK = 0x4e388 -> @sk_threaded SK = 0x4df60 + 1 ->
  @lf_sink_env B SH SK.
Proof.
  intros B SH SK HS HG HGG Hctx Hlock Hlibc Hsc Hsmall Hmed Hdb Htp Heo Hvml Hdbl Hhead Hlk Hthr.
  intros a Ha. unfold lf_sink_addr in Ha. rewrite Hhead, Hlk, Hthr in Ha.
  split; [apply (llvm_find_img_range B 0x4df60 0x438 a HS); [vm_compute; discriminate | lia]|].
  split; [unfold static_owned, vml_lo, vml_len; rewrite Hlock, Hlibc, HGG, HG, Hdb, Hsc, Hsmall, Hmed, Hvml, Hdbl;
    lia|].
  split; [rewrite Hctx; unfold CTX_SIZE; lia|].
  unfold errno_addr. rewrite Htp, Heo. lia.
Qed.

Lemma llvm_G_inside : forall a, in_globals llvm_G a -> in_globals frame_G a.
Proof. intros a (lo & len & Hin & _). destruct Hin. Qed.

Lemma llvm_GI_local : forall B, G_local_c B llvm_G llvm_GI.
Proof. intros B j m m' _ _. exact I. Qed.

Lemma llvm_GI_img : forall B mem, G_img_c B llvm_G mem -> llvm_GI 0%nat mem.
Proof. intros B mem _. exact I. Qed.

Lemma ret_ok_of_even : forall ra, ra mod 2 = 0 -> YK0s.ret_ok (Z_to_bv 64 ra).
Proof.
  intros ra H. apply ret_ok_even. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). Z.div_mod_to_equations. lia.
Qed.

Theorem plain_halts_of_slot : slot_contract_all -> frame_ret_hyp -> Statements.plain_halts.
Proof.
  intros SLOT FRH. destruct (FRH lock_ret lock_ret_cases) as (B & API & LS & SH & SK & ra & empty & H).
  destruct H as (Hs & Hra & Hm & Hf & Hreal & Hcal & Hel & Hg & Hgg & Hctx & Hlock & Hlibc & Hsc & Hsmall & Hmed
    & Hdb & Htp & Heo & Hrep & Hvml & Hdbl & Hhead & Hlk & Hthr & He & He2 & Hctxro & HfG & HfR & HK & HD & HR & HA
    & H).
  assert (HR' : forall b n, @lib_room LS b n -> llvm_room b).
  { intros b n Hb. destruct (HR b n Hb) as (H1 & H2 & H3). unfold llvm_room. rewrite H3. unfold CAPMAX. lia. }
  assert (HFR : forall rc : RunCeil, llvm_frame rc B (API rc) SH SK).
  { intros rc. split; [intros fx; exact (HA rc fx)|]. split; [exact (Hel rc)|].
    exact (lock_sink_env B SH SK Hs Hg Hgg Hctx Hlock Hlibc Hsc Hsmall Hmed Hdb Htp Heo Hvml Hdbl Hhead Hlk Hthr). }
  apply (H llvm_G llvm_GI llvm_G_inside (llvm_GI_local B) (llvm_GI_img B)).
  intros rc fx j Hj.
  destruct (HA rc fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HX & _).
  apply (SLOT rc fx LS B (API rc) SH SK (HFR rc)).
  - unfold llvm_binds, LLVM_MALLOC, LLVM_FREE, LLVM_GUARD_GOT, LLVM_GUARD.
    repeat (split; [assumption|]). exact HX.
  - split; [intros pl fs K; rewrite HK; apply t_eq_refl|]. split; [exact HR' | exact HD].
  - exact Hj.
  - unfold LLVM_K, LLVM_FRAME, CL_STACK, CL_FRAME, ALLOC_STACK, SLOT_STACK. lia.
  - exact (ret_ok_of_even ra Hra).
Qed.
