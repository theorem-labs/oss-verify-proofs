(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/YZ04.v (ossv/recipes c8557374ad2e) for fuzz_pcap. src0_realizesX_rc and src0_realizesX keep the donor's statements (YZ04.v:56-62, :70-75) at fuzz_pcap's agreement shape AgreePcap.ag_out_shape (the donor's is cgif's ff_lib_shape). Their proof applies fuzz_pcap's released Reusable/YL0j.v:163 src0_realizes_specX, as the donor's YZ04.v:65 applies cgif's, over fuzz_pcap's released plain library contract (lib/AgreePcap.v:74-80), assembled as lib/AgreeFrameO.v:38-45 and lib/AgreeTop.v:26-40 assemble it; the donor's YZ04.v:20-55 (calls_bound, ff_room_calls, cgif's library-contract assembly) are cgif's program and are replaced by AgreeShape.ag_room_calls and these released contracts. fuzz_pcap's realizes (Reusable/YK15.v:208-221) has rz_silent and a cut, rz_cut, at a budget refusal, where cgif's (cgif YK15.v) has neither; as lib/A/YM09.v does, the cut-freedom that cgif's realizes carries comes from lib/A/RelimCut.v under the run's budget premise: src0_realizesX_cut_free. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.libreac.fuzz_pcap.images Require Import Plain.
(* AgreePcap first: it loads the ubsan modules, and the later Require Import of the plain modules binds the short
   names to the plain ones. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require AgreePcap.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
  YK11 YK15 YM05 YM02 YM0b YO0i YO0f YO0g YO0x YO0d YO05 YO0j YO0m YO03 YO09 YO06 YO04 YO0o
  YH00 YH02 YI06 YI14 YI16 YI5b YI5c YL01 YL0g YL0i YL0k YL0s YL0j YN03 YN2b YN33 YP09 DriverSlots.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import
  ZImage ZTraceSpec AllocSlots AllocRoom ZComplete ZAllocator Contract FrameAPI FrameSlotG OutForm FrameSlotO
  Agree AgreeZlib AgreeShape.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require PWalk PInv PSlot PHolds.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require RelimCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Open Scope Z_scope.
Section a.
Context {rc : YM05.RunCeil}.
(* The released plain library contract of the ubsan agreement (AgreePcap.v:74-80), in the form lib/AgreeFrameO.v:38-45
   gives src0_realizes_specX. *)
Let HP1 : forall (fx : FPState) (j : nat), (j < 4)%nat ->
  @lib_contract_o fx rc AgreePcap.ag_out_shape src0_msyms (@zlib_API rc) src0_sink_head src0_sink
    PWalk.OUT frame_G frame_RELRO PInv.GI j ENTRY RA_LIB EMPTY SLOT_STACK :=
  fun fx j _ =>
  @PSlot.slot_contract_ols fx rc src0_msyms (@zlib_API) src0_sink_head src0_sink RA_LIB EMPTY
    AgreePcap.ag_ff_plain AgreePcap.ag_out_shape PWalk.OUT (fun _ _ _ => eq_refl) (fun _ _ => eq_refl)
    (ag_room_g (out_shape PWalk.OUT))
    (PHolds.pcap_entry rc src0_msyms (@zlib_API) src0_sink_head src0_sink RA_LIB EMPTY AgreePcap.ag_ff_plain)
    PWalk.OUT_big j.
Let LX1 : lib_contract_x_R_all (LS:=AgreePcap.ag_out_shape) src0_msyms (@zlib_API rc) (@RI_G AgreePcap.ag_out_shape) frame_G frame_RELRO
  (fun j T m => T = [] /\ PInv.GI j m) PWalk.OUT LIBPC RA_LIB EMPTY LIB_STACK :=
  lib_contract_x_R_all_of_T src0_msyms (@zlib_API rc) (@RI_G AgreePcap.ag_out_shape) frame_G frame_RELRO _ PWalk.OUT
    LIBPC RA_LIB EMPTY LIB_STACK (@RI_G_step AgreePcap.ag_out_shape PInv.GI)
    (fun fx j Hj =>
      lib_contract_x_T_of_G src0_msyms (@zlib_API rc) frame_G frame_RELRO PInv.GI PWalk.OUT j
        LIBPC RA_LIB EMPTY LIB_STACK
        (lib_contract_x_G_of_o src0_msyms (@zlib_API rc) (zlib_tables rc) PWalk.OUT frame_G frame_RELRO PInv.GI j
          LIBPC RA_LIB EMPTY LIB_STACK (HP1 fx j Hj))).
Let ROOM1 : forall data, @room_calls AgreePcap.ag_out_shape (payload_len data) (calls data) SBD_AG :=
  fun data => ag_room_calls (out_shape PWalk.OUT) _ _.
Lemma src0_realizesX_rc : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_brk src0segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
(SRC_LIM_MIN <= lim)%Z ->
YM05.ceil_of_top (bv_unsigned sp - stack_max_size) ->
realizes src0segs (init_config src0segs Plain.M.init_pc Plain.M.phdrs sp brk mbase rnd lim inp)
(SPECX (LS:=AgreePcap.ag_out_shape) inp).
Proof.
intros sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim Hceil.
exact (src0_realizes_specX (rc:=rc) (LS:=AgreePcap.ag_out_shape) (@zlib_API rc) zlib_allocator_extra
  (fun j T m => T = [] /\ PInv.GI j m) (@RI_G AgreePcap.ag_out_shape) PWalk.OUT
  (G_local_T_mono src0segs frame_G YL0k.src0_G _ frame_G_src0
     (G_local_T_of_G src0segs frame_G PInv.GI (PSlot.GI_local src0_msyms eq_refl)))
  (fun mem H => conj eq_refl (PSlot.GI_img src0_msyms mem eq_refl (G_img_mono src0segs frame_G YL0k.src0_G mem frame_G_src0 H)))
  (lib_contract_x_R_all_mono src0_msyms (@zlib_API rc) (@RI_G AgreePcap.ag_out_shape) frame_G YL0k.src0_G
     frame_RELRO YL0k.src0_R _ PWalk.OUT LIBPC RA_LIB EMPTY LIB_STACK frame_G_src0 frame_RELRO_src0 LX1)
  driver_obligationsX_proved (driver_RI_AG AgreePcap.ag_out_shape ROOM1)
  sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim Hceil).
Qed.
End a.
Lemma valid_sp_window' : forall sp, valid_sp sp -> (sp_window_lo <= bv_unsigned sp <= sp_window_hi)%Z.
Proof. intros sp (H1 & H2 & _). split; assumption. Qed.
Theorem src0_realizesX : forall sp brk mbase rnd lim inp,
valid_sp sp -> valid_brk src0segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
(SRC_LIM_MIN <= lim)%Z ->
realizes src0segs (init_config src0segs Plain.M.init_pc Plain.M.phdrs sp brk mbase rnd lim inp)
(SPECX (LS:=AgreePcap.ag_out_shape) inp).
Proof.
intros sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim.
exact (@src0_realizesX_rc (YM05.RunCeilOf (bv_unsigned sp) (valid_sp_window' sp Hsp))
sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim (YM05.ceil_of_top_run _)).
Qed.
(* The cut-freedom of the donor's realizes, for fuzz_pcap's: the run at lim reaches no refused configuration when the
   run at a smaller limit Ls is never refused (lib/A/RelimCut.v cut_free_of_relim, as lib/A/YM09.v uses it). *)
Theorem src0_realizesX_cut_free : forall sp brk mbase rnd lim inp (Ls : Z),
valid_sp sp -> valid_brk src0segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) -> valid_input inp ->
(SRC_LIM_MIN <= lim)%Z -> (Ls <= lim)%Z ->
~ run_scfg_budget_refused ACFG (mkImage src0segs Plain.M.init_pc Plain.M.phdrs) Ls (mkEntry sp brk mbase rnd) inp ->
realizes src0segs (init_config src0segs Plain.M.init_pc Plain.M.phdrs sp brk mbase rnd lim inp)
(SPECX (LS:=AgreePcap.ag_out_shape) inp) /\
cut_free src0segs (init_config src0segs Plain.M.init_pc Plain.M.phdrs sp brk mbase rnd lim inp).
Proof.
intros sp brk mbase rnd lim inp Ls Hsp Hbrk Hmb Hfits Hinp Hlim HLs NB. split.
- exact (src0_realizesX sp brk mbase rnd lim inp Hsp Hbrk Hmb Hfits Hinp Hlim).
- exact (RelimCut.cut_free_of_relim src0segs Plain.M.init_pc Plain.M.phdrs sp brk mbase rnd Ls lim inp HLs NB).
Qed.
