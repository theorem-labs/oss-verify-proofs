From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Core Require Import Shapes.
From OSSVerify.omx_clap_core.fuzz_preset Require Statements Images.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Ubsan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots YO0d_cf YL0i_cfw.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG SlotPack
  SlotAgree SlotAgreeV AllocCf Agree AgreeWalk AgreeZlib AgreeWalkP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require AgreeLim.
Import ListNotations.
Open Scope Z_scope.

Section Mono.
Context {fx : FPState} {rc : RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Lemma lib_contract_x_Rc_mono : forall RI G G' R R' GI f j pc ra empty stk,
  (forall a, in_globals G a -> in_globals G' a) ->
  (forall a, in_globals R a -> in_globals R' a) ->
  lib_contract_x_Rc B API RI G R GI f j pc ra empty stk ->
  lib_contract_x_Rc B API RI G' R' GI f j pc ra empty stk.
Proof.
  intros RI G G' R R' GI f j pc ra empty stk HG HRR H L A regs mem md p n pl T K Hpre HRI HGI HTL HpT HR Hfrm HK.
  apply (H L A regs mem md p n pl T K Hpre HRI HGI HTL HpT (G_img_mono _ R R' mem HRR HR) Hfrm).
  intros l c' (fx' & L' & A' & regs' & mem' & md' & T' & Hc & Hf & Hp & HRI' & HGI').
  apply HK. exists fx', L', A', regs', mem', md', T'. split; [exact Hc|]. split; [exact Hf|].
  split; [exact (lib_post_x_R_mono B API G G' (f pl) stk L A regs mem md p n l T T' L' A' regs' mem' md' HG Hp)|].
  split; [exact HRI' | exact HGI'].
Qed.

End Mono.

Theorem ubsan_crealizes_of_cgpg : forall (LIM : Z) (LS : lib_shape) (CS : list byte -> list Z) (G : list (Z * Z))
    (GI : nat -> (word -> option byte) -> Prop),
  CS_ok CS ->
  (forall rc : RunCeil, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AgreeLim.limlaw_at LIM src0_msyms (@zlib_API rc)) ->
  (forall a, in_globals G a -> in_globals frame_G a) ->
  G_local_c src0_msyms G GI ->
  (forall mem, G_img_c src0_msyms G mem -> GI 0%nat mem) ->
  (forall (rc : RunCeil), OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AgreeLim.limlaw_at LIM src0_msyms (@zlib_API rc) ->
     forall (fx : FPState) (j : nat), (j < 4)%nat ->
     @lib_contract_cgpg fx rc LS src0_msyms (@zlib_API rc) src0_sink_head src0_sink
       CS G frame_RELRO GI j ENTRY RA_LIB EMPTY SLOT_STACK) ->
  forall en inp lim, valid_entry Images.ubsan en inp -> valid_input inp -> SRC_LIM_MIN <= lim ->
    rz_run Images.ubsan lim en inp (SPECX (LS:=LS) inp) /\ cf_run Images.ubsan lim en inp.
Proof.
  intros LIM LS CS G GI HCS HLIM HG GIL GI0 H [sp brk0 mbase rnd] inp lim Hentry Hinput Hlim.
  apply (valid_entry_sv48 _ _ inp (valid_input_va_size inp Hinput)) in Hentry.
  destruct Hentry as [Hsp [Hbrk [Hmb Hfits]]].
  set (rc := RunCeilOf (bv_unsigned sp) (valid_sp_window_for_ceil sp Hsp)).
  assert (HG' : forall a, in_globals G a -> in_globals src0_G a) by (intros a h; exact (frame_G_src0 a (HG a h))).
  assert (HX : lib_contract_x_Rc_all src0_msyms (@zlib_API rc) (RI_Pc CS) src0_G src0_R
    (fun j T m => T = [] /\ GI j m) (fun _ => []) LIBPC RA_LIB EMPTY LIB_STACK).
  { intros fx j Hj.
    apply (lib_contract_x_Rc_mono src0_msyms (@zlib_API rc) (RI_Pc CS) G src0_G frame_RELRO src0_R
      _ (fun _ => []) j LIBPC RA_LIB EMPTY LIB_STACK HG' frame_RELRO_src0).
    apply (lib_contract_x_Rc_of_cgp src0_msyms (@zlib_API rc) (zlib_tables rc) CS G frame_RELRO _ j
      LIBPC RA_LIB EMPTY LIB_STACK HCS).
    apply lib_contract_cgp_of_cgpg.
    exact (H rc (HLIM rc) fx j Hj). }
  change (crealizes src0_msyms (init_config src0segs Ubsan_init_pc Ubsan_phdrs sp brk0 mbase rnd lim inp)
    (SPECX (LS:=LS) inp)).
  apply (zlib_pack_walk_crealizes rc LS CS (fun j T m => T = [] /\ GI j m) (fun _ => []) HCS
    (G_local_T_mono src0segs G src0_G _ HG' (G_local_T_of_G src0segs G GI GIL))
    (fun mem Hm => conj eq_refl (GI0 mem (G_img_mono src0segs G src0_G mem HG' Hm)))
    HX sp brk0 mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinput Hlim).
  unfold rc. apply ceil_of_top_run.
Qed.
