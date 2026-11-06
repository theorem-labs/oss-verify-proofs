From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells.
Import ListNotations.
Open Scope Z_scope.

(** diginet_scribble_encode (diginet_codec.c:287-303; 204 bytes at 0x15e50, frame 0x40, calls memcpy at
    0x15ec8 and diginet_sysex_encode at 0x15ee0: depth 0x70). Called by LLVMFuzzerTestOneInput at 0x143dc
    (k.p, k.a, &k.bytes, &k.out). *)
Definition DIGINET_SCRIBBLE_ENCODE : Z := 0x15e50.
Definition DIGINET_SCRIBBLE_ENCODE_DEPTH : Z := 0x70.

Definition diginet_scribble_encode_pre (sp a0 a1 a2 a3 : word) (m : word -> option byte) (lo : Z) (pd : option desk) (addr : Z) (cs before : list byte) : Prop :=
  pers_arg m a0 pd /\
  (forall d, pd = Some d -> disj (bv_unsigned a0 + 16) 4 (bv_unsigned sp - DIGINET_SCRIBBLE_ENCODE_DEPTH) DIGINET_SCRIBBLE_ENCODE_DEPTH) /\
  (forall d, pd = Some d -> d_chars d <= 8 /\ d_chars d <= Z.of_nat (length cs)) /\
  arg_u32 a1 addr /\
  bv_unsigned a2 <> 0 /\
  bytes_at rsegs m (bv_unsigned a2) cs /\
  bv_unsigned a3 <> 0 /\
  rw_cells rsegs m (bv_unsigned a3) [CB 32 before] /\
  bv_unsigned a3 mod 4 = 0 /\
  bv_unsigned sp <= bv_unsigned a2 /\
  bv_unsigned sp <= bv_unsigned a3 /\
  mem_inv rsegs m /\
  stk rsegs m lo (bv_unsigned sp) /\
  lo + DIGINET_SCRIBBLE_ENCODE_DEPTH <= bv_unsigned sp.

Definition diginet_scribble_encode_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (pd : option desk) (addr : Z) (cs before : list byte),
    diginet_scribble_encode_pre sp a0 a1 a2 a3 m lo pd addr cs before ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - DIGINET_SCRIBBLE_ENCODE_DEPTH, bv_unsigned sp); (bv_unsigned a3, bv_unsigned a3 + 32)] m m' /\
         wmono rsegs m m' /\
         mem_inv rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         let '(rc, o) := scribble_spec pd addr (zb cs) in
         a0' = Z_to_bv 64 rc /\ rw_cells rsegs m' (bv_unsigned a3) [CB 32 (cmd_out before o)])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DIGINET_SCRIBBLE_ENCODE) fc None m (seg_rom rsegs)).
