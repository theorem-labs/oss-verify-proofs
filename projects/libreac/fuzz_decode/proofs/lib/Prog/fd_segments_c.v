From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_decode.lib Require Import Contract Img0 MemNorm.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Prog Require Import check_round_trip_c
  LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr.
Import ListNotations.
Local Open Scope Z_scope.

Definition FD_DOWN : Z := 0x12e5c.
Definition FD_DOWN_END : Z := 0x130fc.
Definition FD_UP : Z := 0x130fc.
Definition FD_UP_END : Z := 0x132ac.
Definition FD_FRAME : Z := 160.
Definition FD_WIN : Z := CRT_STACK.
Definition FD_KEEP : Z := 116.

Definition MODE_44K1 : Z := 0x103f8.
Definition MODE_48K : Z := 0x10404.
Definition MODE_96K : Z := 0x10410.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let segs := ms_segs B.
Let MR := aa_MR API.

Definition fd_env : Prop := llvm_binds B API /\ errno_addr B + 4 <= alloc_ceiling.

Definition fd_res (A : astate) (b : sbound) : Prop := res_ok_slots A b.

Definition fd_room (b : sbound) : Prop := sb_live b <= 65 /\ sb_bytes b <= 2 ^ 29 /\ 128 <= sb_cap b <= CAPMAX.

Definition fd_inv (S len frame : Z) (fr : list byte) (L : layout) (A : astate) (regs : bvmap 5 word)
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
  getr regs 25 = Z_to_bv 64 len /\ getr regs 26 = Z_to_bv 64 frame /\
  0 <= len < 2 ^ 26 /\ Z.of_nat (length fr) = len /\
  In (frame, len) (blocks L A) /\
  blk_data B mem frame fr /\
  fd_res A b /\ fd_room b.

Definition fd_mode_ok (S mode nch ns : Z) (mem : word -> option byte) : Prop :=
  (mode = MODE_44K1 \/ mode = MODE_48K \/ mode = MODE_96K \/ mode = S - FD_KEEP) /\
  -128 <= nch <= 127 /\ -128 <= ns <= 127 /\
  blk_data B mem (mode + 4) (Z_to_le_bytes 4 (nch mod 2 ^ 32)) /\
  blk_data B mem (mode + 8) (Z_to_le_bytes 4 (ns mod 2 ^ 32)).

Definition fd_kept (S : Z) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (L' : layout) (A' : astate) (mem' : word -> option byte) (md' : Model) : Prop :=
  lf_fr B API (LLVM_K - FD_KEEP) (S - FD_KEEP) L A mem md L' A' mem' md'.

Definition fd_seg_post (S len frame : Z) (fr : list byte) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (b : sbound) (pc_end : Z) (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 pc_end) mem' (seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    fd_inv S len frame fr L' A' regs' mem' md' b /\
    getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
    blocks L' A' = blocks L A /\
    fd_kept S L A mem md L' A' mem' md' /\
    getr regs' 8 = Z_to_bv 64 (frame + 50).

Definition fd_down_contract : Prop :=
  fd_env ->
  forall L A regs mem md b (S len frame mode nch ns : Z) (fr : list byte),
    fd_inv S len frame fr L A regs mem md b ->
    frm_zero fp_csr ->
    getr regs 18 = Z_to_bv 64 mode ->
    fd_mode_ok S mode nch ns mem ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 FD_DOWN) mem (seg_rom segs)) md)
      (fd_seg_post S len frame fr L A regs mem md b FD_DOWN_END).

Definition fd_up_contract : Prop :=
  fd_env ->
  forall L A regs mem md b (S len frame : Z) (fr : list byte),
    fd_inv S len frame fr L A regs mem md b ->
    frm_zero fp_csr ->
    getr regs 8 = Z_to_bv 64 (frame + 50) ->
    SR segs (mkCfg (mkst regs (Z_to_bv 64 FD_UP) mem (seg_rom segs)) md)
      (fd_seg_post S len frame fr L A regs mem md b FD_UP_END).

End K.
