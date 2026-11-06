From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** check_text_masks (fuzz_codec.c:492-519; 208 bytes at 0x15000, frame 0x30, spec_segments inlined; calls
    the frameless diginet_meter_mask, diginet_meter_segments, diginet_ring_dot, diginet_ring_fill). Called
    by LLVMFuzzerTestOneInput at 0x14928 with a0 = n (u32 composed with slliw: sign-extended), a1 = mask
    (u16, zero-extended). It returns without calling abort when the four library values equal the
    harness's. Writes a0-a3 and its frame. *)
Definition CHECK_TEXT_MASKS : Z := 0x15000.
Definition CHECK_TEXT_MASKS_DEPTH : Z := 0x30.

Definition check_text_masks_pre (sp a0 a1 : word) (m : word -> option byte) (lo n mask : Z) : Prop :=
  arg_u32 a0 n /\
  arg_zx 16 a1 mask /\
  mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp) /\
  lo + CHECK_TEXT_MASKS_DEPTH <= bv_unsigned sp /\
  meter_mask_spec n = owed_meter_mask n /\
  meter_segments_spec mask = spec_segments_spec mask /\
  ring_dot_spec n = owed_ring_dot n /\
  ring_fill_spec n = owed_ring_fill n.

Definition check_text_masks_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo n mask : Z),
    check_text_masks_pre sp a0 a1 m lo n mask ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' a3' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - CHECK_TEXT_MASKS_DEPTH, bv_unsigned sp)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 CHECK_TEXT_MASKS) fc None m (seg_rom rsegs)).
