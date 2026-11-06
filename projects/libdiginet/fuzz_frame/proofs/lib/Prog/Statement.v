(* fuzz_frame's plain halting statement from the slot contract of LLVMFuzzerTestOneInput, in the form of
   libreac/fuzz_decode's lib/Prog/Statement.v (bf7779f81ed7), which concludes from FrameAPI.v frame_plain.
   Written by Theorem Labs.

   llvm_frame binds the allocator and sink words of fuzz_frame.plain as FrameAPI.v frame_plain does; each is a
   symbol of the unstripped twin of fuzz_frame.plain (pyelftools; its text, RELRO, data and rodata bytes are the
   pinned image's):
     ms_calloc         None     the image links no calloc (FrameAPI.v frame_plain: ms_calloc B = None)
     ms_ctx            0x4e958  __malloc_context (928 bytes)
     ms_lock           0x4e950  __malloc_lock
     ms_libc           0x4e8e0  __libc (104 bytes); sk_threaded is its byte 1, libc.threaded
     ms_size_classes   0x1040e  __malloc_size_classes (96 bytes: 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, ...)
     ms_small_cnt      0x1046e  small_cnt_tab (27 bytes)
     ms_med_cnt        0x10489  med_cnt_tab (4 bytes)
     ms_debruijn       0x103ee  a 32-byte table with no symbol (mapping symbol $d), the 32 bytes before
                                __malloc_size_classes: the count-trailing-zeros table of the de Bruijn number
                                0x077cb531 (entry (2 ^ i * 0x077cb531 mod 2 ^ 32) / 2 ^ 27 is i)
     ms_debruijn_len   32
     ms_tp             0x2e650  builtin_tls (0x2e588) + 0xc8: static_init_tls (0x14164) puts the thread pointer
                                0xc8 bytes above the thread block (addi s0, s2, 0xc8 at 0x14338)
     ms_errno_off      -164     __errno_location (0x148a0): mv a0, tp; addi a0, a0, -0xa4
     ms_vmlock         None
     sk_ofl_head       0x4ed10  ofl_head
     sk_ofl_lock       0x4ed08  ofl_lock
   slot_sr_all is the premise the walk of LLVMFuzzerTestOneInput supplies: its SR contract under llvm_frame, the
   theorem decode's lib/Prog/LLVMFuzzerTestOneInput_link.v proves (LLVMFuzzerTestOneInput_holds). *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Reusable Require Import YK11 YK0s YK15 YM05 YO0f YO0d YO09 YO0o
  YL0g YL0i YI14 YI16 YL01.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Lib Require Mem.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.Prog Require Import LLVMFuzzerTestOneInput_c.
From OSSVerify.libdiginet.fuzz_frame Require Statements.
Import ListNotations.
Local Open Scope Z_scope.

Definition llvm_frame (rc : RunCeil) (B : malloc_syms) (API : AllocAPI B) (SH : sink_head) (SK : sink_syms) : Prop :=
  (forall fx : FPState, @frame_allocator rc fx B API) /\ errno_addr B + 4 <= @alloc_ceiling rc /\
  ms_calloc B = None /\
  ms_ctx B = 0x4e958 /\ ms_lock B = 0x4e950 /\ ms_libc B = 0x4e8e0 /\ ms_size_classes B = 0x1040e /\
  ms_small_cnt B = 0x1046e /\ ms_med_cnt B = 0x10489 /\ ms_debruijn B = 0x103ee /\ ms_tp B = 0x2e650 /\
  ms_errno_off B = -164 /\ ms_vmlock B = None /\ ms_debruijn_len B = 32 /\
  @sk_ofl_head SH = 0x4ed10 /\ @sk_ofl_lock SK = 0x4ed08 /\ @sk_threaded SK = 0x4e8e0 + 1.

Definition slot_contract_all : Prop :=
  forall (rc : RunCeil) (fx : FPState) (LS : lib_shape) (B : malloc_syms) (API : AllocAPI B)
         (SH : sink_head) (SK : sink_syms),
    llvm_frame rc B API SH SK ->
    LLVMFuzzerTestOneInput_contract B API.

Definition slot_sr_all : Prop :=
  forall (rc : RunCeil) (fx : FPState) (LS : lib_shape) (B : malloc_syms) (API : AllocAPI B)
         (SH : sink_head) (SK : sink_syms),
    llvm_frame rc B API SH SK ->
    LLVMFuzzerTestOneInput_sr_contract B API.

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

Theorem plain_halts_of_slot : slot_contract_all -> frame_plain -> Statements.plain_halts.
Proof.
  intros SLOT (B & API & LS & SH & SK & ra & empty & H).
  assert (Hs : ms_segs B = rsegs) by tauto. assert (Hra : ra mod 2 = 0) by tauto.
  assert (Hm : ms_malloc B = 0x149ec) by tauto. assert (Hf : ms_free B = 0x148ac) by tauto.
  assert (Hg : ms_guard B = 0x4e8c0) by tauto. assert (Hgg : ms_got_guard B = 0x1d2d8) by tauto.
  assert (HK : forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs [])) by tauto.
  assert (HD : forall n b, @lib_delta LS n b = b) by tauto.
  assert (HR : forall b n, @lib_room LS b n -> llvm_room b).
  { assert (HR0 : forall b n, @lib_room LS b n -> sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ sb_cap b = CAPMAX)
      by tauto.
    intros b n Hb. destruct (HR0 b n Hb) as (H1 & H2 & H3). unfold llvm_room. rewrite H3. unfold CAPMAX. lia. }
  assert (HA : forall (rc : RunCeil) (fx : FPState), @frame_allocator rc fx B (API rc)) by tauto.
  assert (Hel : forall rc : RunCeil, errno_addr B + 4 <= @alloc_ceiling rc) by tauto.
  assert (HFR : forall rc : RunCeil, llvm_frame rc B (API rc) SH SK).
  { intros rc. unfold llvm_frame. split; [intros fx; exact (HA rc fx)|]. split; [exact (Hel rc)|]. tauto. }
  repeat match type of H with _ /\ _ => apply proj2 in H end.
  apply (H llvm_G llvm_GI llvm_G_inside (llvm_GI_local B) (llvm_GI_img B)).
  intros rc fx j Hj.
  destruct (HA rc fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HX & _).
  apply (SLOT rc fx LS B (API rc) SH SK (HFR rc)).
  - unfold llvm_binds, LLVM_MALLOC, LLVM_FREE, LLVM_GUARD_GOT, LLVM_GUARD.
    repeat (split; [assumption|]). exact HX.
  - split; [intros pl fs K; rewrite HK; apply t_eq_refl|]. split; [exact HR | exact HD].
  - exact Hj.
  - exact llvm_K_slot.
  - exact (ret_ok_of_even ra Hra).
Qed.
