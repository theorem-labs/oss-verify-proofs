(* rp_frame_channels in image A (fuzz_wire.asan): the addresses, the constant and the model of
   lib/Prog/rp_frame_channels_c.v (the plain build's, reac-repacer src/repace_wire.c:74-86) at image A. Its ASan contract
   is the footprint form, rp_frame_channels_F_c.v. The code (DIS of image A, 0x8136c, 0x74 bytes) is the
   plain build's instruction for instruction: a 16-byte frame (ra at sp - 8, s0 at sp - 16), `bltz a0` to the -1 return,
   `jal reac_frame_clean_len` (lib/A/Prog/reac_frame_clean_len_c.v), and the division by 36 through the 8-byte
   reciprocal K36 at A_K36 in .rodata (`auipc` / `ld` at +0x20 / +0x24). It makes no ASan runtime call and has no
   shadow check. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A Require Import Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.A.Prog Require Import reac_frame_clean_len_c.
Import ListNotations.
Open Scope Z_scope.

Definition RP_FRAME_CHANNELS : Z := 0x8136c.
Definition RP_FRAME_CHANNELS_FRAME : Z := 16.
Definition A_K36 : Z := 0x10328.
Definition K36 : Z := 0xe38e38e38e38e38f.

(* The C function on the signed `long len` (lib/Prog/rp_frame_channels_c.v rp_frame_channels_model, here over image A's
   reac_frame_clean_len_model): REAC_UPSTREAM_OVERHEAD = 52, REAC_UPSTREAM_BYTES_PER_CH = 36, REAC_MAX_CHANNELS = 40;
   `(int)` of the size_t quotient is the two's complement wrap to 32 bits. *)
Definition rp_frame_channels_model (len : Z) : Z :=
  if len <? 0 then -1
  else
    let clean := reac_frame_clean_len_model len in
    if (clean <? 52) || negb ((clean - 52) mod 36 =? 0) then -1
    else
      let nch := bv_swrap 32 ((clean - 52) / 36) in
      if (nch <? 2) || (40 <? nch) || Z.odd nch then -1 else nch.
