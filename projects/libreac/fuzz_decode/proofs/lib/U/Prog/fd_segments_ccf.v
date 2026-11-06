From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Contract Img0 MemNorm.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import check_round_trip_c fd_segments_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import LLVMFuzzerTestOneInput_cfb.
Import ListNotations.
Local Open Scope Z_scope.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition fd_room_cf (b : sbound) : Prop := sb_live b <= 65 /\ sb_bytes b <= 2 ^ 28 + 2 ^ 27 /\ 128 <= sb_cap b <= CAP_AG.

Definition fd_inv_cf (S len frame : Z) (fr : list byte) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (b : sbound) : Prop :=
  MR L A mem md /\ WF A /\ bounded A /\
  spZ regs mod 16 = 0 /\ alloc_ceiling + FD_WIN <= spZ regs /\ spZ regs < 2 ^ 47 /\
  (forall a, spZ regs - FD_WIN <= a < spZ regs -> writable_at segs mem a) /\
  (forall a, S - FD_FRAME <= a < S -> writable_at segs mem a) /\
  getr regs 4 = Z_to_bv 64 (ms_tp B) /\
  (forall a, errno_addr B <= a < errno_addr B + 4 -> writable_at segs mem a) /\
  st_init_done A = true /\
  ro_agree segs mem /\
  m_halted md = None /\ m_vm_lazy md = [] /\
  spZ regs = S - FD_FRAME /\
  0 <= len < 2 ^ 26 /\ Z.of_nat (length fr) = len /\
  In (frame, len) (blocks L A) /\
  blk_data B mem frame fr /\
  fd_res A b /\ fd_room_cf b.

Definition fd_seg_post_cf (S len frame : Z) (fr : list byte) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (b : sbound) (RP : bvmap 5 word -> Prop) (pc_end : Z)
    (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 pc_end) mem' (seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    fd_inv_cf S len frame fr L' A' regs' mem' md' b /\
    getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
    blocks L' A' = blocks L A /\
    fd_kept B API S L A mem md L' A' mem' md' /\
    RP regs'.

Definition fd_down_contract_cf : Prop :=
  fd_env B API ->
  forall L A regs mem md b (S len frame mode nch ns : Z) (fr : list byte),
    fd_inv_cf S len frame fr L A regs mem md b ->
    frm_zero fp_csr ->
    getr regs 9 = Z_to_bv 64 len -> getr regs 25 = Z_to_bv 64 frame ->
    getr regs 19 = Z_to_bv 64 mode ->
    fd_mode_ok B S mode nch ns mem ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 FD_DOWN) mem (seg_rom segs)) md)
      (fd_seg_post_cf S len frame fr L A regs mem md b (fd_up_regs len frame) FD_DOWN_END).

Definition fd_up_contract_cf : Prop :=
  fd_env B API ->
  forall L A regs mem md b (S len frame : Z) (fr : list byte),
    fd_inv_cf S len frame fr L A regs mem md b ->
    frm_zero fp_csr ->
    fd_up_regs len frame regs ->
    SRcf B (mkCfg (mkst regs (Z_to_bv 64 FD_UP) mem (seg_rom segs)) md)
      (fd_seg_post_cf S len frame fr L A regs mem md b (fd_exit_regs frame) FD_UP_END).

End K.
